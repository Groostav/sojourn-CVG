@file:JvmName("Sojourn")
package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import com.microsoft.z3.Status
import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.immutableListOf
import kotlinx.collections.immutable.plus
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.ReceiveChannel
import kotlinx.coroutines.channels.consumeEach
import kotlinx.coroutines.channels.first
import kotlinx.coroutines.channels.produce
import kotlinx.coroutines.selects.select
import java.text.DecimalFormat
import java.util.*

enum class Satisfiability { SATISFIABLE, UNSATISFIABLE, UNKNOWN }
data class Generation(val satisfiable: Satisfiability, val values: List<InputVector>)

val SOLUTION_PAGE_SIZE = 10_000
val EASY_PATH_THRESHOLD_FACTOR = 0.1
val WARMUP_ROUNDS = 10

private data class DependencyGroup(var deps: Set<String>, var constraints: Set<BabelExpression>) {
    override fun toString(): String = "DependencyGroup(deps=$deps, constraints={${constraints.joinToString { it.expressionLiteral }}})"
}


fun CoroutineScope.makeSampleAgent(
    inputs: List<InputVariable>,
    targetPointCount: Int,
    constraints: Collection<BabelExpression>,
    seeds: ImmutableList<InputVector> = immutableListOf(),
    samplerSeed: Random = Random(),
    improverSeed: Random = Random()
): ReceiveChannel<Generation> {

    inputs.duplicates().let { require(it.isEmpty()) { "duplicate inputs: $it" } }

    val dependencyGroups = mutableListOf<DependencyGroup>()

    for(constraint in constraints){
        if(constraint.containsDynamicLookup){
            //only the global group can solve for this one
            continue
        }

        val merging = constraint.staticallyReferencedSymbols.flatMap { varName ->
            dependencyGroups.filter { varName in it.deps }
        }

        when(merging.size) {
            0 -> dependencyGroups += DependencyGroup(constraint.staticallyReferencedSymbols, setOf(constraint))
            1 -> merging.single().apply {
                this.deps += constraint.staticallyReferencedSymbols
                this.constraints += constraint
            }
            else -> {
                val receiver = merging.first()
                receiver.apply {
                    this.deps += constraint.staticallyReferencedSymbols
                    this.constraints += constraint
                }
                val deletions = merging.drop(1)
                for(deletion in deletions){
                    receiver.deps += deletion.deps
                    receiver.constraints += deletion.constraints
                    dependencyGroups -= deletion
                }
            }
        }
    }

    trace {
        "found groups ${dependencyGroups.joinToString()}"
    }

    val globalGroup = startAgent(inputs, constraints, samplerSeed, improverSeed, targetPointCount, seeds)

    fail;//blargwargl, this isnt easy.
    
//    when(dependencyGroups.size) {
//        1 -> {
//            require(dependencyGroups.single().deps == inputs.map { it.name }.toSet())
            return globalGroup
//        }
//        else -> {
//
//             TODO: it might make more sense to create a kind of composite constraint solving pool,
//             the reason being is that we can then use the same load balancing as previous

//            val parts = dependencyGroups.map {group ->
//                startAgent(inputs.filter { it.name in group.deps }, group.constraints, samplerSeed, improverSeed, targetPointCount, seeds)
//            }
//
//            return produce {
//
//                launch {
//                    globalGroup.consumeEach { send(it) }
//                }
//                while(isActive){
//                    val partResults = parts.map { it.receive() }
//
//                    val generation = Generation(
//                        partResults.first().satisfiable,
//                        TODO()
//                    )
//                }
//            }
//        }
//    }
}

private fun <T> List<T>.duplicates(): List<T> =
    groupBy { it }.filter { it.value.size >= 2 }.flatMap { it.value }

private fun CoroutineScope.startAgent(
    inputs: List<InputVariable>,
    constraints: Collection<BabelExpression>,
    samplerSeed: Random,
    improverSeed: Random,
    targetPointCount: Int,
    seeds: ImmutableList<InputVector>
) = produce<Generation>(Dispatchers.Default) {

    val fairSampler = RandomSamplingPool.create(inputs, constraints)
    val adaptiveSampler = RandomSamplingPool.Factory(samplerSeed, true).create(inputs, constraints)
    val improover = RandomBoundedWalkingImproverPool.Factory(improverSeed).create(inputs, constraints)
    val smt = Z3SolvingPool.create(inputs, constraints)

    if (smt.check() == Status.UNSATISFIABLE) {
        trace { "unsat" }
        send(Generation(Satisfiability.UNSATISFIABLE, immutableListOf()))
        return@produce
    }

    val initialRoundTarget = targetPointCount.coerceAtMost(SOLUTION_PAGE_SIZE)
    val initialResults = fairSampler.makeNewPointGeneration(initialRoundTarget, seeds)

    trace { "initial-sampling gen hit ${((100.0 * initialResults.size) / initialRoundTarget).toInt()}%" }

    when {
        initialResults.size > EASY_PATH_THRESHOLD_FACTOR * initialRoundTarget -> {
            trace { "easy" }

            var results = initialResults
            while (results.size < targetPointCount) {
                results += fairSampler.makeNewPointGeneration(targetPointCount - results.size, results + seeds)
            }

            send(Generation(Satisfiability.SATISFIABLE, results))
        }
        else -> {
            trace { "balancing" }

            var nextRoundTarget = targetPointCount.coerceIn(1..SOLUTION_PAGE_SIZE)

            var pool = seeds + initialResults
            var publishedPoints = immutableListOf<InputVector>()

            var targets = listOf(fairSampler, adaptiveSampler, improover)
                .associate { it to nextRoundTarget / 3 }
                .let { it + (smt to 5) }

            var roundNo = 1

            val inputNames = inputs.map { it.name }

            while (publishedPoints.size < targetPointCount) try {

                trace {
                    "round start: target=$nextRoundTarget, " +
                            targets.entries.joinToString { (solver, target) -> "${solver.name}($target)" }
                }

                val resultsAsync: Map<ConstraintSolvingPool, Deferred<PoolResult>> = targets
                    .mapValues { (solver, target) ->
                        async(Dispatchers.Default) {
                            val (time, pts) = measureTime { solver.makeNewPointGeneration(target, pool) }
                            val (centroid, variance) = findDispersion(inputNames, pts)

                            PoolResult(time, pts, centroid, variance.takeIf { !it.isNaN() } ?: 0.0)
                        }
                    }

                val results: Map<ConstraintSolvingPool, PoolResult> = resultsAsync
                    .mapValues { (_, deferred) -> deferred.await() }

                val overheadStartTime = System.currentTimeMillis()

                val roundResults = results.values.flatMap { (_, points) -> points }
                pool += roundResults

                val newQualityResults = roundResults.filter { constraints.passFor(it) }

                trace {
                    val dispersion = findDispersion(inputNames, newQualityResults)
                    "round results: " +
                            "target=$nextRoundTarget, " +
                            "got=${newQualityResults.size}, " +
                            "dispersion=${dispersion.variance} " +
                            results.entries.joinToString { (solver, result) ->
                                "${solver.name}(${result.points.size}, ${TwoSigFigs.format(result.timeMillis)}ms, v=${TwoSigFigsWithE.format(
                                    result.variance
                                )})"
                            }
                }

                if (newQualityResults.isEmpty()) {
                    trace { "no-yards!!" }
                }

                if (roundNo > WARMUP_ROUNDS) {
                    val toPublish = newQualityResults.takeLast(targetPointCount - publishedPoints.size)
                    send(Generation(Satisfiability.SATISFIABLE, toPublish))
                    publishedPoints += newQualityResults
                } else trace { "dropped ${newQualityResults.size} pts on warmup round $roundNo" }

                nextRoundTarget = when {
                    roundNo < WARMUP_ROUNDS -> SOLUTION_PAGE_SIZE
                    else -> (targetPointCount - publishedPoints.size).coerceIn(1..SOLUTION_PAGE_SIZE)
                }

                // we balance on performance, unless any pool has a variance significantly worse than the others,
                // then we avoid that pool

                val speedSum = results.values.sumByDouble { (t, pts, _, _) -> 1.0 * pts.size / t }
                targets = results.mapValues { (pool, result) ->
                    val speed = 1.0 * result.points.size / result.timeMillis
                    (nextRoundTarget * speed / speedSum).toInt()
                }

                val previousTargets = targets
                val varianceSum = results.values.sumByDouble { it.variance }

                val varianceAverage = varianceSum / results.values.size

                targets = targets.mapValues { (pool, previousTime) ->

                    val minimumVarianceParticipation = 1.0 / (targets.size * 2)

                    val thisPoolVariance = results.getValue(pool).variance
                    if (thisPoolVariance / varianceSum < minimumVarianceParticipation) {
                        if (previousTargets.getValue(pool) != 0) {
                            trace { "dropped execution of ${pool.name} as its variance was $thisPoolVariance (average is $varianceAverage)" }
                        }
                        0
                    } else previousTime
                }

                trace {
                    "overhead: ${System.currentTimeMillis() - overheadStartTime}ms"
                }
            } finally {
                roundNo += 1
            }
        }
    }
}

suspend fun makeSamples(
        inputs: List<InputVariable>,
        targetPointCount: Int,
        constraints: Collection<BabelExpression>,
        seeds: ImmutableList<InputVector> = immutableListOf(),
        samplerSeed: Random = Random(),
        improverSeed: Random = Random()
): Generation = runBlocking {
    makeSampleAgent(inputs, targetPointCount, constraints, seeds, samplerSeed, improverSeed).first()
}

data class PoolResult(val timeMillis: Long, val points: List<InputVector>, val centroid: InputVector, val variance: Double)
data class Dispersion(val centroid: InputVector, val variance: Double)

fun findDispersion(names: List<String>, points: List<InputVector>): Dispersion {

    val center = findCenter(names, points)

    // as per a simple euclidian distence:
    // https://stats.stackexchange.com/questions/13272/2d-analog-of-standard-deviation
    val deviation = if(points.isEmpty()) Double.NaN else points.sumByDouble { point ->
        val r = point.keys.sumByDouble { Math.pow(point[it]!! - center[it]!!, 2.0) }
        return@sumByDouble Math.sqrt(r)
    }

    return Dispersion(center, deviation / points.size)
}

fun findCenter(names: List<String>, points: List<InputVector>): InputVector {
    var center = points.firstOrNull()?.mapValues { _, _ -> 0.0 }
        ?: return names.associate { it to Double.NaN }.toInputVector()

    for(point in points){

        center = center vecPlus point
    }

    center /= points.size.toDouble()

    return center
}

private val TwoSigFigs = DecimalFormat("0.##")
private val TwoSigFigsWithE = DecimalFormat("0.##E0")