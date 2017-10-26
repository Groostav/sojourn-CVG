package com.empowerops.sojourn

import com.empowerops.babel.BabelCompiler
import com.empowerops.babel.BabelExpression
import kotlinx.collections.immutable.immutableListOf
import org.assertj.core.api.Assertions.*
import org.testng.annotations.Test

class Z3SolvingPoolFixture {

    val compiler = BabelCompiler()

//    @Test
    fun `simple arithmatic`(){

        //setup
        val inputs = listOf(
                InputVariable("x1", 0.0, 1.0),
                InputVariable("x2", 0.0, 1.0),
                InputVariable("x3", 0.0, 1.0),
                InputVariable("x4", 0.0, 1.0)
        )

        val constraint = compiler.compile("x2 > x1 + 1/2*x2 - x3 / x4") as BabelExpression

        //act
        val pool = Z3SolvingPool.create(inputs, listOf(constraint))
        val results = pool.makeNewPointGeneration(10, immutableListOf())

        //assert
        assertThat(results).hasSize(10)
        assertThat(results).allMatch { constraint.evaluate(it).isPassedConstraint() }
    }

//    @Test
    fun `root`() {
        //setup
        val inputs = listOf(
                InputVariable("x1", 0.0, 10.0),
                InputVariable("x2", 0.0, 10.0),
                InputVariable("x3", 0.0, 10.0),
                InputVariable("x4", 0.0, 10.0)
        )

        val constraints = listOf(
                "x1 > sqrt(x2)",
                "x3 > cbrt(x4)"
        ).map { compiler.compile(it) as BabelExpression }

        //act
        val pool = Z3SolvingPool.create(inputs, constraints)
        val results = pool.makeNewPointGeneration(10, immutableListOf())

        //assert
        assertThat(results).hasSize(10)
        assertThat(results).allMatch { constraints.passFor(it) }
    }

//    @Test
    fun `power`(){
        //setup
        val inputs = listOf(
                InputVariable("x1", 0.0, 10.0),
                InputVariable("x2", 0.0, 10.0),
                InputVariable("x3", 0.0, 10.0),
                InputVariable("x4", 0.0, 10.0),
                InputVariable("x5", 0.0, 10.0)
        )

        val constraints = listOf(
                "x1 > x2^3"
                //"x3 < x4^x5" //nope, Z3 wont reason about real-exponents.
        ).map { compiler.compile(it) as BabelExpression }

        //act
        val pool = Z3SolvingPool.create(inputs, constraints)
        val results = pool.makeNewPointGeneration(10, immutableListOf())

        //assert
        assertThat(results).hasSize(10)
        assertThat(results).allMatch { constraints.passFor(it) }
    }

    @Test
    fun `logarithms`(){
        //setup
        val inputs = listOf(
                InputVariable("x1", 0.0, 10.0),
                InputVariable("x2", 0.0, 10.0),
                InputVariable("x3", 0.0, 10.0),
                InputVariable("x4", 0.0, 10.0),
                InputVariable("x5", 0.0, 10.0),
                InputVariable("x6", 0.0, 10.0)
        )

        val constraints = listOf(
//                "x2 > ln(x1)"
                "x4 < log(x3)"
//                "x6 > log(2.0, x5)"
        ).map { compiler.compile(it) as BabelExpression }

        //act
        val pool = Z3SolvingPool.create(inputs, constraints)
        val results = pool.makeNewPointGeneration(10, immutableListOf())

        //assert
        assertThat(results).hasSize(10)
        assertThat(results).allMatch { constraints.passFor(it) }
    }
}