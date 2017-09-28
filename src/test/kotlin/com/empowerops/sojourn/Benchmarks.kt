package com.empowerops.sojourn

import com.empowerops.babel.BabelCompiler
import com.empowerops.babel.BabelExpression
import com.empowerops.babel.CompilationFailure
import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.immutableListOf
import kotlinx.collections.immutable.immutableMapOf
import org.assertj.core.api.Assertions.*
import org.assertj.core.data.Offset
import org.testng.annotations.Test
import java.util.*

class Benchmarks {

    val RandomSamplingPool1234 = RandomSamplingPool.Factory(Random(1234L))

    val compiler = BabelCompiler()

    data class ConstraintSet(
            val name: String,
            val inputs: List<InputVariable>,
            val constraints: List<String>,
            val centroid: InputVector,
            val dispersion: Double,
            val targetSampleSize: Int,
            val fudgeFactor: Double = 0.05
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
            dispersion = 0.579,
            targetSampleSize = 50_000
    )

    val P118 = ConstraintSet(
            name = "P118",
            inputs = listOf(
                    InputVariable("x1", lowerBound = 8.0, upperBound = 21.0),
                    InputVariable("x2", lowerBound = 43.0, upperBound = 57.0),
                    InputVariable("x3", lowerBound = 3.0, upperBound = 16.0),
                    InputVariable("x4", lowerBound = 0.0, upperBound = 90.0),
                    InputVariable("x5", lowerBound = 0.0, upperBound = 12.0),
                    InputVariable("x6", lowerBound = 0.0, upperBound = 60.0),
                    InputVariable("x7", lowerBound = 0.0, upperBound = 90.0),
                    InputVariable("x8", lowerBound = 0.0, upperBound = 12.0),
                    InputVariable("x9", lowerBound = 0.0, upperBound = 60.0),
                    InputVariable("x10", lowerBound = 0.0, upperBound = 90.0),
                    InputVariable("x11", lowerBound = 0.0, upperBound = 12.0),
                    InputVariable("x12", lowerBound = 0.0, upperBound = 60.0),
                    InputVariable("x13", lowerBound = 0.0, upperBound = 90.0),
                    InputVariable("x14", lowerBound = 0.0, upperBound = 12.0),
                    InputVariable("x15", lowerBound = 0.0, upperBound = 60.0)
            ),
            constraints = listOf(
                    "-x4+x1-7", "x4-x1-6",
                    "-x5+x2-7", "x5-x2-7",
                    "-x6+x3-7", "x6-x3-6",
                    "-x7+x4-7", "x7-x4-6",
                    "-x8+x5-7", "x8-x5-7",
                    "-x9+x6-7", "x9-x6-6",
                    "-x10+x7-7", "x10-x7-6",
                    "-x11+x8-7", "x11-x8-7",
                    "-x12+x9-7", "x12-x9-6",
                    "-x13+x10-7", "x13-x10-6",
                    "-x14+x11-7", "x14-x11-7",
                    "-x15+x12-7", "x15-x12-6",

                    "-x1-x2-x3+60",
                    "-x4-x5-x6+50",
                    "-x7-x8-x9+70",
                    "-x10-x11-x12+85",
                    "-x13-x14-x15+100"
            ),
            centroid = immutableMapOf(),
            dispersion = Double.NaN,
            targetSampleSize = -1
    )

    @Test fun `sampling braindead inequalities`() = runTest(RandomSamplingPool1234, BriandeadInequalitySet)
    
//    @Test fun `sampling on P118`() = runTest(RandomSamplingPool1234, P118)
//    @Test fun `ibex on P118`() = runTest(ChocoIbexSolvingPool.Factory(), P118)

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
        val results: ImmutableList<InputVector> = solver.makeNewPointGeneration(targetSampleSize, immutableListOf())
        val (actualCentroid, actualDispersion) = findDispersion(results)

        //assert 1 --publish performance results
        println("echoing to teamcity[buildStatisticValue key='${solver.name}-${constraintSpec.name}' value='$actualDispersion']")
        println("##teamcity[buildStatisticValue key='${solver.name}-${constraintSpec.name}' value='$actualDispersion']")
//        println("##teamcity[centroid solver='${solver.name}' constraintSet='${constraintSpec.name}' value='$actualDispersion']")

        //assert 2 -- red/green assertions
        assertThat(results).allMatch { point -> constraints.all { it.evaluate(point).isPassedConstraint() }}
        assertThat((actualCentroid vecMinus centroid).distance)
                .describedAs("distance between result centroid $actualCentroid\nand the expected centroid $centroid")
                .isLessThan(centroid.distance * fudgeFactor)

        assertThat(actualDispersion).isEqualTo(dispersion, Offset.offset(fudgeFactor * dispersion))

        Unit
    }
}

val ConstraintSolvingPool.name: String get() = javaClass.simpleName
    
infix fun InputVector.vecMinus(other: InputVector): InputVector {
    require(this.size == other.size)

    val result = InputVector().builder()

    for((key, value) in this){
        result += key to value - other.getValue(key)
    }

    return result.build()
}

val InputVector.distance: Double get() = Math.sqrt(values.sumByDouble { Math.pow(it, 2.0) })