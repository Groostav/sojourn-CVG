package com.empowerops.sojourn

import kotlinx.collections.immutable.immutableListOf
import kotlinx.coroutines.channels.all
import kotlinx.coroutines.channels.count
import kotlinx.coroutines.channels.take
import kotlinx.coroutines.channels.toList
import kotlinx.coroutines.runBlocking
import org.assertj.core.api.Assertions.assertThat
import org.testng.annotations.Test
import kotlin.system.measureTimeMillis

class IntegrationTests {

    @Test fun `when calling front-end on P118`() = runBlocking<Unit> {

        val time = measureTimeMillis {
            val results = P118.run {
                makeSampleAgent(inputs, constraints, immutableListOf())
            } as? Satisfiable


            val points = results!!.take(20_000).toList()
            assertThat(points.size).isEqualTo(20_000)
            assertThat(points.all { P118.constraints.passFor(it) })
        }

        println("took $time ms")
    }

    @Test fun `when calling frontend on 200D corner`() = runBlocking<Unit> {
        val time = measureTimeMillis {
            val results = TopCorner200D.run {
                makeSampleAgent(inputs, constraints, immutableListOf())
            } as? Satisfiable


            val points = results!!.take(20_000).toList()
            assertThat(points.size).isEqualTo(20_000)
            assertThat(points.all { P118.constraints.passFor(it) })
        }

        println("took $time ms")
    }
}