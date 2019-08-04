@file:JvmName("Sojourn")
package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import com.microsoft.z3.Status
import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.immutableListOf
import kotlinx.collections.immutable.plus
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.ReceiveChannel
import kotlinx.coroutines.channels.produce
import kotlinx.coroutines.selects.select
import java.lang.IndexOutOfBoundsException
import java.text.DecimalFormat
import java.util.*

val SOLUTION_PAGE_SIZE = 10_000
val EASY_PATH_THRESHOLD_FACTOR = 0.1
val WARMUP_ROUNDS = 5

private data class DependencyGroup(var deps: Set<String>, var constraints: Set<BabelExpression>) {
    override fun toString(): String = "DependencyGroup(deps=$deps, constraints={${constraints.joinToString { it.expressionLiteral }}})"
}

sealed class ConstraintAnalysis
sealed class Worthwhile(val results: ReceiveChannel<InputVector>): ConstraintAnalysis(), ReceiveChannel<InputVector> by results
class Satisfiable(results: ReceiveChannel<InputVector>): Worthwhile(results)
class Unknown(results: ReceiveChannel<InputVector>, val problemConstraint: BabelExpression?): Worthwhile(results)
class Unsatisfiable(val problemConstraint: BabelExpression?): ConstraintAnalysis()

fun CoroutineScope.makeSampleAgent(
    inputs: List<InputVariable>,
    constraints: Collection<BabelExpression>,
    seeds: ImmutableList<InputVector> = immutableListOf(),
    samplerSeed: Random = Random(),
    improverSeed: Random = Random()
): ConstraintAnalysis {

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

    val globalGroup = startAgentGroup(inputs, constraints, samplerSeed, improverSeed, seeds)

    if(globalGroup is Unsatisfiable) return globalGroup

    when(dependencyGroups.size) {
        1 -> {
            require(dependencyGroups.single().deps == inputs.map { it.name }.toSet())
            return globalGroup
        }
        else -> {

//             TODO: it might make more sense to create a kind of composite constraint solving pool,
//             the reason being is that we can then use the same load balancing as previous

            val parts = dependencyGroups.associate { group ->
                group to (startAgentGroup(inputs.filter { it.name in group.deps }, group.constraints, samplerSeed, improverSeed, seeds) as Worthwhile)
            }

            require(globalGroup is Worthwhile)

            val pts = globalGroup + produce<InputVector> {
                try {
                    while (isActive) {

                        val pointsBySource = parts.mapValues { (_, channel) ->
                            channel.receiveOrNull()
                        }

                        if (null in pointsBySource.values) {
                            val extras = pointsBySource.filterValues { it != null }
                            if (extras.any()) trace {
                                val names = pointsBySource.entries.joinToString { (group, pt) ->
                                    "${group.deps}->${pt?.let { "pt" } ?: "null"}"
                                }
                                "one or more dependency groups quit while one or more produced more results: $names"
                            }

                            return@produce
                        }

                        send(InputVector(pointsBySource.values.flatMap { it!!.entries }))
                    }
                }
                finally {
                    globalGroup.cancel()
                    parts.values.forEach { it.cancel() }
                }
            }

            return when(globalGroup){
                is Unsatisfiable -> TODO()
                is Satisfiable -> Satisfiable(pts)
                is Unknown -> Unknown(pts, globalGroup.problemConstraint)
            }
        }
    }
}

@UseExperimental(InternalCoroutinesApi::class)
operator fun <T> ReceiveChannel<T>.plus(right: ReceiveChannel<T>) = GlobalScope.produce<T>(onCompletion = { cancel(); right.cancel() }) {
    val left = this@plus
    while(isActive){
        val next = select<T> {
            if(! left.isClosedForReceive) left.onReceive { it }
            if(! right.isClosedForReceive) right.onReceive { it }
        }
        send(next)

        if(left.isClosedForReceive && right.isClosedForReceive) break
    }
}

fun <T> List<List<T>>.asTransposedRegular(): List<List<T>> = object: AbstractList<List<T>>() {

    //in outputs terms
    val columns = this@asTransposedRegular

    init {
        require(columns.isEmpty() || columns.map { it.size }.distinct().size == 1)
    }

    val rowCount = columns.firstOrNull()?.size ?: 0
    val colCount = columns.size

    override fun get(rowIndex: Int): AbstractList<T> {
        if(rowIndex < 0 || rowIndex >= rowCount) throw IndexOutOfBoundsException("rowIndex=$rowIndex in matrix with $rowCount rows")
        return object: AbstractList<T>() {
            override fun get(columnIndex: Int): T = columns[columnIndex][rowIndex]
            override val size: Int get() = colCount
        }
    }

    override val size get() = rowCount
}

private fun <T> List<T>.duplicates(): List<T> =
    groupBy { it }.filter { it.value.size >= 2 }.flatMap { it.value }

private fun CoroutineScope.startAgentGroup(
    inputs: List<InputVariable>,
    constraints: Collection<BabelExpression>,
    samplerSeed: Random,
    improverSeed: Random,
    seeds: ImmutableList<InputVector>
): ConstraintAnalysis {

    val inputNames = inputs.map { it.name }
    val fairSampler = RandomSamplingPool.create(inputs, constraints)
    val adaptiveSampler = RandomSamplingPool.Factory(samplerSeed, true).create(inputs, constraints)
    val improover = RandomBoundedWalkingImproverPool.Factory(improverSeed).create(inputs, constraints)
    val smt = Z3SolvingPool.create(inputs, constraints)

    val smtState = smt.check()
    if (smtState == Status.UNSATISFIABLE) {
        trace { "unsat" }
        return Unsatisfiable(smt.problem)
    }

    val pts = produce<InputVector>(Dispatchers.Default) {

        val initialRoundTarget = SOLUTION_PAGE_SIZE
        val initialResults = fairSampler.makeNewPointGeneration(initialRoundTarget, seeds)

        trace { "initial-sampling gen hit ${((100.0 * initialResults.size) / initialRoundTarget).toInt()}%" }

        when {
            initialResults.size > EASY_PATH_THRESHOLD_FACTOR * initialRoundTarget -> {
                trace { "easy: $inputNames" }

                var results = initialResults
                while (isActive) {
                    val nextGen = fairSampler.makeNewPointGeneration(SOLUTION_PAGE_SIZE, results + seeds)
                    results += nextGen

                    nextGen.forEach { send(it) }
                }
            }
            else -> {
                trace { "balancing: $inputNames" }

                var pool = seeds + initialResults
                var publishedPoints = immutableListOf<InputVector>()

                var targets = listOf(fairSampler, adaptiveSampler, improover)
                    .associate { it to SOLUTION_PAGE_SIZE / 3 }
                    .let { it + (smt to 5) }

                var roundNo = 1
                var roundHadProgress = true

                val inputNames = inputs.map { it.name }

                while (isActive) try {

                    trace {
                        "round start: " + targets.entries.joinToString { (solver, target) -> "${solver.name}($target)" }
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
                                "feasible=${newQualityResults.size}, " +
                                "dispersion=${dispersion.variance} " +
                                results.entries.joinToString { (solver, result) ->
                                    "${solver.name}(${result.points.size}, " +
                                            "${TwoSigFigs.format(result.timeMillis)}ms, " +
                                            "${TwoSigFigsWithE.format(result.variance)}σ)"
                                }
                    }

                    if (newQualityResults.isEmpty()) {
                        trace { "no-yards!!" }
                        roundHadProgress = false
                    }

                    if (roundNo > WARMUP_ROUNDS) {
                        newQualityResults.forEach{ send(it) }
                        publishedPoints += newQualityResults
                    } else trace { "dropped ${newQualityResults.size} pts on warmup round $roundNo" }

                    // we balance on performance, unless any pool has a variance significantly worse than the others,
                    // then we avoid that pool

                    val speedSum = results.values.sumByDouble { (t, pts, _, _) -> 1.0 * pts.size / t }

                    targets = results.mapValues { (pool, result) ->
                        val speed = 1.0 * result.points.size / result.timeMillis
                        fail;// ok, running with 'x1 < 0.0001^(x2+1)' scares me
                        // notice that the improver offers a much higher variance
                        // but we still pick the adaptive sampler, which doenst appear to be adapting very well.
                        // hmm.
                        // i think that we should actually just publish results from the pool with the highest variance
                        // also, as another feature, the adaptive random sampling pool could "split" into multiple pools,
                        // if it is able to detect invalid regions.... does that work at 100 vars?
                        (SOLUTION_PAGE_SIZE * speed / speedSum).toInt()
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
                    if(roundHadProgress) roundNo += 1
                    roundHadProgress = true
                }
            }
        }
    }

    return when(smtState){
        Status.SATISFIABLE -> Satisfiable(pts)
        Status.UNKNOWN -> Unknown(pts, smt.problem)
        Status.UNSATISFIABLE -> TODO()
    }
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