@file:JvmName("Sojourn")
package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import com.microsoft.z3.Status
import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.immutableListOf
import kotlinx.collections.immutable.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.ReceiveChannel
import kotlinx.coroutines.channels.first
import kotlinx.coroutines.channels.produce
import java.util.*

enum class Satisfiability { SATISFIABLE, UNSATISFIABLE, UNKNOWN }
data class Generation(val satisfiable: Satisfiability, val values: List<InputVector>)

val IMPROVER_HANDICAP = 0.1
val SMT_HANDICAP = 0.005

val TOUGH_PATH_MAX_TARGET = 5_000
val EASY_PATH_MAX_TARGET = 10_000
val EASY_PATH_THRESHOLD_FACTOR = 0.1

fun CoroutineScope.makeSampleAgent(
    inputs: List<InputVariable>,
    targetPointCount: Int,
    constraints: Collection<BabelExpression>,
    seeds: ImmutableList<InputVector> = immutableListOf(),
    samplerSeed: Random = Random(),
    improverSeed: Random = Random()
) = produce<Generation>(Dispatchers.Default) {

    val sampler = RandomSamplingPool.Factory(samplerSeed).create(inputs, constraints)
    val improover = RandomBoundedWalkingImproverPool.Factory(improverSeed).create(inputs, constraints)
    val smt = Z3SolvingPool.create(inputs, constraints)

    if(smt.check() == Status.UNSATISFIABLE){
        trace { "unsat" }
        send(Generation(Satisfiability.UNSATISFIABLE, immutableListOf()))
        return@produce
    }

    val initialRoundTarget = targetPointCount.coerceAtMost(EASY_PATH_MAX_TARGET)
    val initialResults = sampler.makeNewPointGeneration(initialRoundTarget, seeds)

    trace { "initial-sampling gen hit ${ ((100.0 * initialResults.size) / initialRoundTarget).toInt()}%" }

    when {
        initialResults.size > EASY_PATH_THRESHOLD_FACTOR * initialRoundTarget -> {
            trace { "easy" }

            var results = initialResults
            while(results.size < targetPointCount){
                results += sampler.makeNewPointGeneration(targetPointCount - results.size, results + seeds)
            }

            send(Generation(Satisfiability.SATISFIABLE, results))
        }
        else -> {
            trace { "balancing" }

            var nextRoundTarget = targetPointCount.coerceAtMost(TOUGH_PATH_MAX_TARGET)

            var pool = initialResults
            var qualityResults = pool.filter { constraints.passFor(it) }.toImmutableList()

            var nextRoundSamplingTarget = nextRoundTarget.coerceAtLeast(1)
            var nextRoundImprooverTarget = (nextRoundTarget*IMPROVER_HANDICAP).toIntAtLeast1()
            var nextRoundSmtTarget = (nextRoundTarget*SMT_HANDICAP).toIntAtLeast1()

            while(qualityResults.size < targetPointCount) {
                val samplingResultsAsync = GlobalScope.async(Dispatchers.Default) {
                    measureTime { sampler.makeNewPointGeneration(nextRoundSamplingTarget, pool + seeds) }
                }
                val improoverResultsAsync = GlobalScope.async(Dispatchers.Default) {
                    measureTime { improover.makeNewPointGeneration(nextRoundImprooverTarget, pool + seeds) }
                }
                val smtResultsAsync = GlobalScope.async(Dispatchers.Default){
                    measureTime { smt.makeNewPointGeneration(nextRoundSmtTarget, pool + seeds) }
                }

                val (samplingTime, samplingResults) = samplingResultsAsync.await()
                val (improoverTime, improoverResults) = improoverResultsAsync.await()
                val (smtTime, smtResults) = smtResultsAsync.await()

                val roundResults = samplingResults + improoverResults + smtResults
                pool += roundResults
                val newQualityResults = roundResults.filter { constraints.passFor(it) }
                qualityResults += newQualityResults

                val previousRoundTarget = nextRoundTarget
                nextRoundTarget = (targetPointCount - qualityResults.size).coerceIn(1 .. TOUGH_PATH_MAX_TARGET)

                val samplingWin = samplingResults.size.toDouble() / samplingTime
                val improoverWin = improoverResults.size.toDouble() / improoverTime
                val smtWin = smtResults.size.toDouble() / smtTime

                val totalWin = samplingWin + improoverWin + smtWin

                trace {
                    "round results: target=$previousRoundTarget, got=${newQualityResults.size}, SMT($nextRoundSmtTarget)=$smtWin, Imp($nextRoundImprooverTarget)=$improoverWin, Sampling($nextRoundSamplingTarget)=$samplingWin"
                }
                send(Generation(Satisfiability.SATISFIABLE, newQualityResults))

                if(newQualityResults.isEmpty()){
                    trace { "no-yards" }
                }

                nextRoundSamplingTarget = (nextRoundTarget * (samplingWin / totalWin)).toInt().coerceAtLeast(10)
                nextRoundImprooverTarget = (nextRoundTarget * (improoverWin / totalWin) * IMPROVER_HANDICAP).toInt().coerceAtLeast(10)
                nextRoundSmtTarget = (nextRoundTarget * (smtWin / totalWin) * SMT_HANDICAP).toInt().coerceAtMost(100)

                if(samplingWin <= 0.01 && improoverWin <= 0.01){
                    nextRoundSmtTarget = nextRoundSmtTarget.coerceAtLeast(1)
                }
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

private fun Double.toIntAtLeast1() = toInt().coerceAtLeast(1)