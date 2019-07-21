@file:JvmName("Sojourn")
package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import com.microsoft.z3.Status
import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.immutableListOf
import kotlinx.collections.immutable.*
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.GlobalScope
import kotlinx.coroutines.async
import java.util.*

enum class Satisfiability { SATISFIABLE, UNSATISFIABLE, UNKNOWN }
data class Generation(val satisfiable: Satisfiability, val values: ImmutableList<InputVector>)

val IMPROVER_HANDICAP = 0.1
val SMT_HANDICAP = 0.005

val TOUGH_PATH_MAX_TARGET = 5_000
val EASY_PATH_MAX_TARGET = 10_000
val EASY_PATH_THRESHOLD_FACTOR = 0.1


suspend fun makeSamples(
        inputs: List<InputVariable>,
        targetPointCount: Int,
        constraints: Collection<BabelExpression>,
        seeds: ImmutableList<InputVector> = immutableListOf(),
        samplerSeed: Random = Random(),
        improverSeed: Random = Random()
): Generation {

    val sampler = RandomSamplingPool.Factory(samplerSeed).create(inputs, constraints)

    val initialRoundTarget = targetPointCount.coerceAtMost(EASY_PATH_MAX_TARGET)
    val initialResults = sampler.makeNewPointGeneration(initialRoundTarget, seeds)

    when {
        initialResults.size > EASY_PATH_THRESHOLD_FACTOR * initialRoundTarget -> {
            var results = initialResults
            while(results.size < targetPointCount){
                results += sampler.makeNewPointGeneration(targetPointCount - results.size, results + seeds)
            }
            return Generation(Satisfiability.SATISFIABLE, results)
        }
        else -> {
            var nextRoundTarget = targetPointCount.coerceAtMost(TOUGH_PATH_MAX_TARGET)

            var pool = initialResults
            var qualityResults = pool.filter { constraints.passFor(it) }.toImmutableList()

            val improover = RandomBoundedWalkingImproverPool.Factory(improverSeed).create(inputs, constraints)
            val smt = Z3SolvingPool.create(inputs, constraints)

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

                if(smt.check() == Status.UNSATISFIABLE){
                    trace { "unsat" }
                    return Generation(Satisfiability.UNSATISFIABLE, immutableListOf())
                }

                val (samplingTime, samplingResults) = samplingResultsAsync.await()
                val (improoverTime, improoverResults) = improoverResultsAsync.await()
                val (smtTime, smtResults) = smtResultsAsync.await()

                val roundResults = samplingResults + improoverResults + smtResults
                pool += roundResults
                val previousQualityResults = qualityResults
                qualityResults += roundResults.filter { constraints.passFor(it) }
                val newResultCount = qualityResults.size - previousQualityResults.size

                val previousRoundTarget = nextRoundTarget
                nextRoundTarget = (targetPointCount - qualityResults.size).coerceIn(1 .. TOUGH_PATH_MAX_TARGET)

                val samplingWin = samplingResults.size.toDouble() / samplingTime
                val improoverWin = improoverResults.size.toDouble() / improoverTime
                val smtWin = smtResults.size.toDouble() / smtTime

                val totalWin = samplingWin + improoverWin + smtWin

                trace {
                    "round results: target=$previousRoundTarget, SMT=$smtWin, Imp=$improoverWin, Sampling=$samplingWin"
                }

                if(newResultCount == 0){
                    trace { "no-yards" }
                    return Generation(Satisfiability.UNKNOWN, qualityResults)
                }

                nextRoundSamplingTarget = (nextRoundTarget * (samplingWin / totalWin)).toInt().coerceAtLeast(10)
                nextRoundImprooverTarget = (nextRoundTarget * (improoverWin / totalWin) * IMPROVER_HANDICAP).toInt().coerceAtLeast(10)
                nextRoundSmtTarget = (nextRoundTarget * (smtWin / totalWin) * SMT_HANDICAP).toIntAtLeast1().coerceAtMost(100)
            }

            return Generation(Satisfiability.SATISFIABLE, qualityResults.subList(0, targetPointCount))
        }
    }
}

private fun Double.toIntAtLeast1() = toInt().coerceAtLeast(1)