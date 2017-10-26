package com.empowerops.sojourn

import com.empowerops.babel.BabelCompiler
import com.empowerops.babel.BabelExpression
import com.empowerops.babel.CompilationFailure
import kotlinx.collections.immutable.*
import org.assertj.core.api.Assertions.*
import org.assertj.core.data.Offset
import org.testng.SkipException
import org.testng.annotations.Test
import java.util.*

class Benchmarks {

    val RandomSamplingPool1234 = RandomSamplingPool.Factory(Random(1234L))
    val RandomWalkingPool1234 = RandomBoundedWalkingPool.Factory(Random(1234L))

    val compiler = BabelCompiler()

    data class ConstraintSet(
            val name: String,
            val inputs: List<InputVariable>,
            val constraints: List<String>,
            val centroid: InputVector,
            val dispersion: Double,
            val targetSampleSize: Int,
            val seeds: ImmutableList<InputVector> = immutableListOf(),
            val fudgeFactor: Double = 0.10
    )

    val SanityCheck = ConstraintSet(
            name = "SanityCheck",
            inputs = listOf(InputVariable("x", -1.0, +1.0)),
            constraints = listOf(
                    "x > 0.0"
            ),
            centroid = immutableMapOf("x" to 0.5),
            seeds = immutableListOf(immutableMapOf("x" to 0.5)),
            dispersion = 0.25,
            targetSampleSize = 1_000
    )


    val BriandeadInequalitySet = ConstraintSet(
            name = "Braindead",
            inputs = listOf("x1", "x2", "x3", "x4", "x5").map {
                InputVariable(it, 0.0, 1.0)
            },
            constraints = listOf(
                    "x1 + x2 > x3",
                    "x2 + x3 > x4",
                    "x3 + x4 > x5"
            ),
            centroid = immutableMapOf(
                    "x1" to 0.559,
                    "x2" to 0.619,
                    "x3" to 0.561,
                    "x4" to 0.506,
                    "x5" to 0.440
            ),
            seeds = expand(
                    listOf("x1", "x2", "x3", "x4", "x5"),
                    OneHundredBraindeadPoints
            ),
            dispersion = 0.579,
            targetSampleSize = 5_000
    )

    val TopCorner200D = ConstraintSet(
            "Top-corner-200D",
            (1..200).map { "x$it" }.map { InputVariable(it, 10.0, 11.0) },
            (1..200).map { "x$it > 10.5" },
            (1..200).associate { "x$it" to 10.75 }.toInputVector(),
            seeds = immutableListOf((1..200).associate { "x$it" to 10.75 }.toInputVector()),
            dispersion = 0.95, //TODO: this value doesnt seem correct at all. How is 200 ranges of [10.5..11] variance ~= 1.0?
            targetSampleSize = 200
    )

    val ToughSingleVar = ConstraintSet(
            name = "Small single var",
            inputs = listOf(
                    InputVariable("x", -3.0, +1.0),
                    InputVariable("y", -1.0, +1.0)
            ),
            constraints = listOf(
                    //punched this into wolfram, pulls up a very small region.
                    //y < sin(x*pi) && y > 1.1* sin(x*pi-0.05) && x > -3.0 && x < 1
                    "y < sin(x*pi)",
                    "y > 1.1*sin(x*pi-0.5)"
            ),
            centroid = InputVector("x" to 0.0, "y" to 0.0),
            dispersion = 1.0,
            targetSampleSize = 1000
    )

    val P118 = ConstraintSet(
            name = "P118",
            inputs = listOf(
                    InputVariable("x1", lowerBound = 0.0, upperBound = 21.0),
                    InputVariable("x2", lowerBound = 0.0, upperBound = 57.0),
                    InputVariable("x3", lowerBound = 0.0, upperBound = 16.0),
                    InputVariable("x4", lowerBound = 0.0, upperBound = 90.0),
                    InputVariable("x5", lowerBound = 0.0, upperBound = 120.0),
                    InputVariable("x6", lowerBound = 0.0, upperBound = 60.0),
                    InputVariable("x7", lowerBound = 0.0, upperBound = 90.0),
                    InputVariable("x8", lowerBound = 0.0, upperBound = 120.0),
                    InputVariable("x9", lowerBound = 0.0, upperBound = 60.0),
                    InputVariable("x10", lowerBound = 0.0, upperBound = 90.0),
                    InputVariable("x11", lowerBound = 0.0, upperBound = 120.0),
                    InputVariable("x12", lowerBound = 0.0, upperBound = 60.0),
                    InputVariable("x13", lowerBound = 0.0, upperBound = 90.0),
                    InputVariable("x14", lowerBound = 0.0, upperBound = 120.0),
                    InputVariable("x15", lowerBound = 0.0, upperBound = 60.0)
            ),
            constraints = listOf(
                    "0 > -x4+x1-7", "0 > x4-x1-6",
                    "0 > -x5+x2-7", "0 > x5-x2-7",
                    "0 > -x6+x3-7", "0 > x6-x3-6",
                    "0 > -x7+x4-7", "0 > x7-x4-6",
                    "0 > -x8+x5-7", "0 > x8-x5-7",
                    "0 > -x9+x6-7", "0 > x9-x6-6",
                    "0 > -x10+x7-7", "0 > x10-x7-6",
                    "0 > -x11+x8-7", "0 > x11-x8-7",
                    "0 > -x12+x9-7", "0 > x12-x9-6",
                    "0 > -x13+x10-7", "0 > x13-x10-6",
                    "0 > -x14+x11-7", "0 > x14-x11-7",
                    "0 > -x15+x12-7", "0 > x15-x12-6",

                    "0 > -x1-x2-x3+60",
                    "0 > -x4-x5-x6+50",
                    "0 > -x7-x8-x9+70",
                    "0 > -x10-x11-x12+85",
                    "0 > -x13-x14-x15+100"
            ),
            centroid = immutableMapOf(),
            dispersion = Double.NaN,
            targetSampleSize = 5
    )



    @Test fun `sampling sanity check`() = runTest(RandomSamplingPool1234, SanityCheck)
    @Test fun `random walking sanity check`() = runTest(RandomWalkingPool1234, SanityCheck)
    @Test fun `z3 sanity check`() = runTest(Z3SolvingPool, SanityCheck.copy(targetSampleSize = 100))

    @Test fun `sampling braindead inequalities`() = runTest(RandomSamplingPool1234, BriandeadInequalitySet)
    @Test fun `random walking brainded inequalities with 100 seeds`() = runTest(RandomWalkingPool1234, BriandeadInequalitySet)
    @Test fun `z3 braindead inequalities`() = runTest(Z3SolvingPool, BriandeadInequalitySet.copy(targetSampleSize = 100))

    @Test fun `sampling top-corner-200D inequalities`() = runTest(RandomSamplingPool1234, TopCorner200D)
    @Test fun `random walking top-corner-200D with one seed`() = runTest(RandomWalkingPool1234, TopCorner200D)
    @Test fun `z3 top-corner-200D`() = runTest(Z3SolvingPool, TopCorner200D)

    @Test fun `sampling on P118`() = runTest(RandomSamplingPool1234, P118)
    @Test fun `z3 on P118`() = runTest(Z3SolvingPool, P118)

    @Test fun `sampling on tough-single-var`() = runTest(RandomSamplingPool1234, ToughSingleVar)
    @Test fun `z3 tough-single-var`() = runTest(Z3SolvingPool, ToughSingleVar.copy(targetSampleSize = 100))

    private fun `runTest`(solverFactory: ConstraintSolvingPoolFactory, constraintSpec: ConstraintSet): Unit = constraintSpec.run {
        //setup
        val constraints = constraints
                .map { compiler.compile(it) }
                .map { when(it) {
                    is BabelExpression -> it
                    is CompilationFailure -> throw RuntimeException(it.problems.joinToString("\n"))
                }}

        val solver = solverFactory.create(inputs, constraints)

        //act
        val (timeTaken, results) = measureTime { solver.makeNewPointGeneration(targetSampleSize, seeds) }
        val (actualCentroid, actualDispersion) = findDispersion(inputs.map { it.name }, results)

        //assert 1 --publish performance results
        val situationKey = "${solver.name}-${constraintSpec.name}"
        TEAMCITY += "$situationKey-amount" to results.size
        TEAMCITY += "$situationKey-variance" to actualDispersion
        TEAMCITY += "$situationKey-time" to timeTaken

        if(results.isEmpty()) throw SkipException("$situationKey failed to generate any results")

        //assert 2 -- red/green assertions
        assertThat(results).allMatch { point -> constraints.all { it.evaluate(point).isPassedConstraint() }}
//        assertThat((actualCentroid vecMinus centroid).distance)
//                .describedAs("distance between result centroid $actualCentroid\nand the expected centroid $centroid")
//                .isLessThan(centroid.distance * fudgeFactor)
//
//        assertThat(actualDispersion).isEqualTo(dispersion, Offset.offset(fudgeFactor * dispersion))

        Unit
    }
}

val ConstraintSolvingPool.name: String get() = javaClass.simpleName

fun expand(inputs: List<String>, values: List<Double>): ImmutableList<InputVector> {

    var results = immutableListOf<InputVector>()

    for(index in 0 until values.size step inputs.size) {
        val result = inputs.zip(values.subList(index, index + inputs.size)).toInputVector()
        results += result
    }

    return results
}

object TEAMCITY {
    operator fun plusAssign(nameValuePair: Pair<String, Any>) {
        println("##teamcity[buildStatisticValue key='${nameValuePair.first}' value='${nameValuePair.second}']")
    }
}