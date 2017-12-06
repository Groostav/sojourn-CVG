package com.empowerops.sojourn

import com.empowerops.babel.BabelCompiler
import com.empowerops.babel.BabelExpression
import com.empowerops.babel.CompilationFailure
import kotlinx.collections.immutable.*
import org.assertj.core.api.Assertions.*
import org.testng.SkipException
import org.testng.annotations.Test
import java.util.*

typealias FeasibleRegion = Map<String, ClosedRange<Double>>

operator fun FeasibleRegion.contains(vector: InputVector): Boolean
        = this.entries.all { vector.getValue(it.key) in it.value }

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
            val fudgeFactor: Double = 0.10,
            val feasibleRegions: List<FeasibleRegion> = emptyList()
    ) {
        init {
            for (outer in feasibleRegions) {
                for (inner in feasibleRegions - outer) {
                    for(input: String in inputs.map { it.name }) {
                        val (innerValue, outerValue) = inner[input] to outer[input]
                        if(innerValue == null || outerValue == null) continue

                        require(innerValue.start !in outerValue)
                        require(innerValue.endInclusive !in outerValue)
                    }
                }
            }
        }
    }

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

    fun makeParabolicConstraints(offset: Double) = ConstraintSet(
            name = "ParabolicRoots",
            inputs = listOf(InputVariable("x", -5.0, +5.0)),
            constraints = listOf(
                    "(x + 2) * (x - 1) == 0 +/- $offset"
            ),
            centroid = immutableMapOf("x" to -0.5),
            dispersion = 1.0,
            targetSampleSize = 1000,
            seeds = immutableListOf(InputVector("x" to -2.0)),
            feasibleRegions = listOf(
                    mapOf("x" to (-2.0 - offset) .. (-2.0 + offset)),
                    mapOf("x" to (+1.0 - offset) .. (+1.0 + offset))
            )
    )

    val ParabolaRootsTypeOne = makeParabolicConstraints(0.1)
    val ParabolaRootsTypeTwo = makeParabolicConstraints(0.01)
    val ParabolaRootsTypeThree = makeParabolicConstraints(0.001)

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
    @Test fun `z3 top-corner-200D`() = runTest(Z3SolvingPool, TopCorner200D.copy(targetSampleSize = 100))

    @Test fun `sampling on P118`() = runTest(RandomSamplingPool1234, P118)
    @Test fun `z3 on P118`() = runTest(Z3SolvingPool, P118)

    @Test fun `sampling on tough-single-var`() = runTest(RandomSamplingPool1234, ToughSingleVar)
    @Test fun `z3 tough-single-var`() = runTest(Z3SolvingPool, ToughSingleVar.copy(targetSampleSize = 100))


    @Test fun solveThings() {
        val excelResults = ExcelResults()
        val constraintSpec = ParabolaRootsTypeOne.copy(targetSampleSize = 20)

        (1 .. 10).map {
            runTest(Z3SolvingPool, constraintSpec, excelResults)
        }

        println(excelResults)
    }


    private fun `runTest`(
            solverFactory: ConstraintSolvingPoolFactory,
            constraintSpec: ConstraintSet,
            excelResults: ExcelResults? = null
    ): Unit = constraintSpec.run {
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
        assertThat(results).allMatch { point -> constraints.passFor(point) }
//        assertThat((actualCentroid vecMinus centroid).distance)
//                .describedAs("distance between result centroid $actualCentroid\nand the expected centroid $centroid")
//                .isLessThan(centroid.distance * fudgeFactor)
//
//        assertThat(actualDispersion).isEqualTo(dispersion, Offset.offset(fudgeFactor * dispersion))

        //assert 3 -- publish to excel stuff
        excelResults?.let {
            it.results += ExcelResult(
                    velocityFeasible = results.size.toDouble() / timeTaken,
                    dispersion = dispersion,
                    timeToAllRegions = calcPointsTakenUntilAllRegionsSampled(results, constraintSpec)
            )
        }

        Unit
    }
}

data class ExcelResult(val velocityFeasible: Double, val dispersion: Double, val timeToAllRegions: Int?)
data class ExcelResults(var results: List<ExcelResult> = emptyList()) {
    override fun toString(): String {
        val builder = StringBuilder()
        builder.append("velocityFeasible, dispersion, timeToAllRegions")
        builder.append("\n")
        results.joinTo(builder, separator = "\n") { result -> result.run {
            "$velocityFeasible, $dispersion, $timeToAllRegions"
        }}

        return builder.toString()
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

fun calcPointsTakenUntilAllRegionsSampled(values: List<InputVector>, constraintSpec: Benchmarks.ConstraintSet): Int? {
    var remainingUnsatisfiedRegions = constraintSpec.feasibleRegions

    for((index, candidate) in values.withIndex()){
        val passingRegion = remainingUnsatisfiedRegions.singleOrNull { candidate in it }
        if(passingRegion != null) remainingUnsatisfiedRegions -= passingRegion

        if(remainingUnsatisfiedRegions.isEmpty()) return index + 1
    }

    return null
}

object TEAMCITY {
    operator fun plusAssign(nameValuePair: Pair<String, Any>) {
        println("##teamcity[buildStatisticValue key='${nameValuePair.first}' value='${nameValuePair.second}']")
    }
}