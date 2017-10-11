    package com.empowerops.babel

import org.assertj.core.api.Assertions.*
import org.testng.annotations.Test

class Benchmarks {

    val compiler = BabelCompiler()

    data class ConstraintSet(val inputs: List<InputVariable>, val constraints: List<String>)

    val SimpleInequalitySet = ConstraintSet(
            inputs = listOf("x1", "x2", "x3", "x4", "x5").map {
                InputVariable(it, 0.0, 1.0)
            },
            constraints = listOf(
                    "x1 + x2 > x3",
                    "x2 + x3 > x4",
                    "x3 + x4 > x5"
            )
    )

    val P118 = ConstraintSet(
            inputs = listOf(
                    InputVariable("x1", lowerBound = 8.0, upperBound = 21.0),
                    InputVariable("x2", lowerBound = 43.0,upperBound = 57.0),
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
            )
    )

    @Test fun `sampling on simple inequalities`() = runTest(RandomSamplingPool, SimpleInequalitySet)
    @Test fun `sampling on P118`() = runTest(RandomSamplingPool, P118)

    @Test fun `ibex on P118`() = runTest(ChocoIbexSolvingPool.Factory(), P118)

    private fun `runTest`(solverFactory: ConstraintSolvingPoolFactory, constraintSpec: ConstraintSet){
        //setup
        val constraints = constraintSpec.constraints
                .map { compiler.compile(it) }
                .map { when(it) {
                    is BabelExpression -> it
                    is CompilationFailure -> throw RuntimeException(it.problems.joinToString("\n"))
                }}
        val solver = solverFactory.create(constraintSpec.inputs, constraints)

        //act
        val results = solver.makeNewPointGeneration(1_000)

        //assert
        assertThat(results).allMatch { point -> constraints.all { it.evaluate(point).isPassedConstraint() }}
    }
}