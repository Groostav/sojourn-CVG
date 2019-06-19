package com.empowerops.sojourn

import kotlinx.collections.immutable.immutableListOf
import kotlinx.coroutines.runBlocking
import org.assertj.core.api.Assertions.assertThat
import org.testng.annotations.Test
import kotlin.system.measureTimeMillis

class IntegrationTests {

    @Test fun `when calling front-end on P118`() = runBlocking {

        val time = measureTimeMillis {
            val (sat, results) = P118.run { makeSamples(inputs, 20_000, constraints, immutableListOf()) }

            assertThat(sat).isEqualTo(Satisfiability.SATISFIABLE)
            assertThat(results.size).isEqualTo(20_000)
            assertThat(results.all { P118.constraints.passFor(it) })
        }

        println("took $time ms")

        Unit
    }
}