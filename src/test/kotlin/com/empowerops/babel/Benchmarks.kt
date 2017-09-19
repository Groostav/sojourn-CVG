package com.empowerops.babel

import org.assertj.core.api.Assertions.*
import org.testng.annotations.Test


class Benchmarks {

    val compiler = BabelCompiler()

    val inputs = listOf("x1", "x2", "x3", "x4", "x5").map {
        InputVariable(it, 0.0, 1.0)
    }

    val constraints = listOf(
            "x1 + x2 > x3",
            "x2 + x3 > x4",
            "x3 + x4 > x5"
    ).map { compiler.compile(it) }

    @Test
    fun `when using strategy should properly pass all constraints`(){
        //setup
        val strategy = RandomSamplingPool(inputs, constraints)

        //act
        val results = strategy.makeNewPointGeneration(10_000)

        //assert
        assertThat(results).allMatch { point -> constraints.all { it.evaluate(point).isPassedConstraint() }}

    }
}