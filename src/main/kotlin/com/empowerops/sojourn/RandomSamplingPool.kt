package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import kotlinx.collections.immutable.*
import java.util.*

class RandomSamplingPool(
        val inputVariables: List<InputVariable>,
        val constraints: List<BabelExpression>,
        val random: Random
): ConstraintSolvingPool {

    override fun makeNewPointGeneration(pointCount: Int, existingPoints: ImmutableList<InputVector>)
            : ImmutableList<InputVector> {

        var results = immutableListOf<InputVector>()

        for(point in 0 until pointCount){

            val candidate = makeRandomVector()

            if(constraints.any { ! it.evaluate(candidate).isPassedConstraint() }){
                continue
            }

            results += candidate
        }

        return results
    }

    private fun makeRandomVector(): InputVector = inputVariables
            .associate { it.name to it.run { random.nextDouble() * (upperBound - lowerBound) + lowerBound } }
            .toImmutableMap()     

    companion object: ConstraintSolvingPoolFactory {
        override fun create(inputSpec: List<InputVariable>, constraints: List<BabelExpression>)
                = RandomSamplingPool(inputSpec, constraints, Random())

    }

    class Factory(val random: Random): ConstraintSolvingPoolFactory {
        override fun create(inputSpec: List<InputVariable>, constraints: List<BabelExpression>)
                = RandomSamplingPool(inputSpec, constraints, random)

    }
}

