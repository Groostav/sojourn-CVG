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
            listOf("x2 == x1 + 1/2*x2 - x3 / x4 +/- 0.00001")
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
                    "x1 == sqrt(x2) +/- 0.0001",
                    "x3 == cbrt(x4) +/- 0.0001"
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
                    "x1 == x2^3 +/- 0.0001"
                    //"x3 < x4^x5" //nope, Z3 wont reason about real-exponents.
            )
    )

    @Test fun `logarithms`() = runTest(
            mapOf(
                    "x1" to 0.0..10.0,
                    "x2" to 0.0..10.0,
                    "x3" to 0.0..10.0,
                    "x4" to 0.0..10.0,
                    "x5" to 0.0..10.0,
                    "x6" to 0.0..10.0
            ),
            listOf(
//                "x2 > ln(x1)",
                    "x4 == log(4) +/- 0.0001"
//                "x6 > log(2.0, x5)"
            )
    )

    @Test fun `mod`() = runTest(
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
                    "x1 == x2 % 2.0 +/- 0.0001",
                    "x3 == x4 % 4.5 +/- 0.0001"
//                    "x3 == 27 % x5 +/- 0.0001"
//                    "x5 == x6 % x7 +/- 0.0001"
            )
    )

    @Test
    fun `constants`() = runTest(
            mapOf("x1" to 0.0 .. 10.0, "x2" to 0.0 .. 10.0),
            listOf("x1 == pi +/- 0.001", "x2 == e +/- 0.001")
    )

    @Test
    fun `sgn`() = runTest(
            mapOf(
                    "x1" to -1.0 .. +1.0, "x2" to -2.0 .. +2.0
            ),
            listOf(
                    "x2 == sgn(x1) +/- 0.001"
            )
    )

    @Test fun `ciel and floor`() = runTest(
            mapOf(
                    "x1" to 0.0 .. 10.0,
                    "x2" to 0.0 .. 10.0,
                    "x3" to 0.0 .. 10.0,
                    "x4" to 0.0 .. 10.0
            ),
            listOf(
                    "x1 > floor(x2)"
//                    "x3 > ceil(x4) + floor(x4)"
            )
    )
    
    @Test
    fun `vars`() = runTest(
            mapOf("x1" to -1.0 .. + 1.0, "x2" to -2.0 .. +2.0, "x3" to -2.0 .. +2.0),
            listOf("1.5 == var[1] + var[2]  +/- 0.001", "1.5 == var[2] - var[3] +/- 0.001")
    )

    @Test fun `abs`() = runTest(
            mapOf("x1" to 0.0 .. +1.0, "x2" to -1.0 .. +0.0, "x3" to -2.0 .. -1.0),
            listOf("abs(x1) == 1 +/- 0.001", "abs(x2) == 1  +/- 0.001", "abs(x3) == 1.5  +/- 0.001")
    )

    @Test fun `equality`() = runTest(
            mapOf("x1" to -1.0 .. + 1.0, "x2" to -1.0 .. +1.0),
            listOf("x1 == x2 +/- 0.1")
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
        assertThat(results).allMatch { constraints.passFor(it, tolerance = 0.000001) }
    }
}