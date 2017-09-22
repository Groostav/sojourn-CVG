package com.empowerops.babel

import kotlinx.collections.immutable.*
import java.util.*

class RandomSamplingPool(val inputVariables: List<InputVariable>, val constraints: List<BabelExpression>): ConstraintSolvingPool {

    val random = Random()

    override fun makeNewPointGeneration(pointCount: Int): ImmutableList<InputVector> {

        var results = immutableListOf<InputVector>()

        while(results.size != pointCount){

            val candidate = makeRandomVector()

            if(constraints.any { ! it.evaluate(candidate).isPassedConstraint() }){
                continue
            }

            results += candidate
        }

        return results
    }

    fun makeRandomVector(): InputVector = inputVariables
            .associate { it.name to it.run { random.nextDouble() * (upperBound - lowerBound) + lowerBound } }
            .toImmutableMap()     

    companion object: ConstraintSolvingPoolFactory {
        override fun create(inputSpec: List<InputVariable>, constraints: List<BabelExpression>)
                = RandomSamplingPool(inputSpec, constraints)
    }
}