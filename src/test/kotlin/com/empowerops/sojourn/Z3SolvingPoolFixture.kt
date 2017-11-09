package com.empowerops.sojourn

import com.empowerops.babel.BabelCompiler
import com.empowerops.babel.BabelExpression
import kotlinx.collections.immutable.immutableListOf
import org.assertj.core.api.Assertions.*
import org.testng.annotations.Test

class Z3SolvingPoolFixture {

    val compiler = BabelCompiler()

    @Test
    fun `simple arithmatic`() = runTest(
            mapOf(
                    "x1" to 0.0 .. 1.0,
                    "x2" to 0.0 .. 1.0,
                    "x3" to 0.0 .. 1.0,
                    "x4" to 0.0 .. 1.0
            ),
            listOf("x2 > x1 + 1/2*x2 - x3 / x4")
    )

    @Test
    fun `roots`() = runTest(
            mapOf(
                    "x1" to 0.0 .. 10.0,
                    "x2" to 0.0 .. 10.0,
                    "x3" to 0.0 .. 10.0,
                    "x4" to 0.0 .. 10.0
            ),
            listOf(
                    "x1 > sqrt(x2)",
                    "x3 > cbrt(x4)"
            )
    )

    @Test
    fun `power`() = runTest(
            mapOf(
                    "x1" to 0.0 .. 10.0,
                    "x2" to 0.0 .. 10.0,
                    "x3" to 0.0 .. 10.0,
                    "x4" to 0.0 .. 10.0,
                    "x5" to 0.0 .. 10.0
            ),
            listOf(
                    "x1 > x2^3"
                    //"x3 < x4^x5" //nope, Z3 wont reason about real-exponents.
            )
    )

    @Test
    fun `logarithms`() = runTest(
            mapOf(
                    "x1" to 0.0..10.0,
                    "x2" to 0.0..10.0,
                    "x3" to 0.0..10.0,
                    "x4" to 0.0..10.0,
                    "x5" to 0.0..10.0,
                    "x6" to 0.0..10.0
            ),
            listOf(
//                "x2 > ln(x1)"
                    "x4 < log(4)"
//                "x6 > log(2.0, x5)"
            )
    )

    @Test
    fun `mod`() = runTest(
            mapOf(
                    "x1" to 0.0..10.0,
                    "x2" to 0.0..10.0,
                    "x3" to 0.0..10.0,
                    "x4" to 0.0..10.0,
                    "x5" to 0.0..10.0,
                    "x6" to 0.0..10.0,
                    "x7" to 0.0..10.0
            ),
            listOf(
                    "x1 > x2 % 2.0",
                    "x3 < x4 % 4.5"
//                "x5 > x6 % x7"
            )
    )

    @Test
    fun `constants`() = runTest(
            mapOf("x1" to 0.0 .. 10.0, "x2" to 0.0 .. 10.0),
            listOf("x1 < pi", "x2 > e")
    )

    @Test
    fun `sgn`() = runTest(
            mapOf(
                    "x1" to -1.0 .. +1.0, "x2" to -2.0 .. +2.0
            ),
            listOf(
                    "x2 > sgn(x1)"
            )
    )

    @Test
    fun `vars`() = runTest(
            mapOf("x1" to -1.0 .. + 1.0, "x2" to -2.0 .. +2.0, "x3" to -2.0 .. +2.0),
            listOf("1.5 < var[1] + var[2]", "1.5 < var[2] - var[3]")
    )

    private fun runTest(inputs2: Map<String, ClosedRange<Double>>, constraints2: List<String>) {
        val inputs = inputs2.map { (key, value) -> InputVariable(key, value.start, value.endInclusive) }

        val constraints = constraints2.map {
            val result = compiler.compile(it)

            result as? BabelExpression ?: throw RuntimeException("compiler failure in $it: $result")
        }

        //act
        val pool = Z3SolvingPool.create(inputs, constraints)
        val results = pool.makeNewPointGeneration(10, immutableListOf())

        //assert
        assertThat(results).hasSize(10)
        assertThat(results).allMatch { constraints.passFor(it) }
    }
}