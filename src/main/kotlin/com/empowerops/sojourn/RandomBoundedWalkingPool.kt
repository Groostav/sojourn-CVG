package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import kotlinx.collections.immutable.*
import kotlinx.collections.immutable.immutableListOf
import java.util.*

class RandomBoundedWalkingPool(
        val inputVariables: List<InputVariable>,
        val constraints: List<BabelExpression>,
        val random: Random
): ConstraintSolvingPool {

    override fun makeNewPointGeneration(pointCount: Int, existingPoints: ImmutableList<InputVector>): ImmutableList<InputVector> {
        if(existingPoints.isEmpty()) return immutableListOf()

        var results = immutableListOf<InputVector>()

        for(pointIdx in 0 until pointCount) {
            val base = existingPoints[random.nextInt(existingPoints.size)]

            val direction = randomUnitVector(inputVariables.map { it.name })

            var candidate = makeBoundedOffset(base, direction)

            while (constraints.any { !it.evaluate(base vecPlus candidate).isPassedConstraint() }) {

                //not sure this is a fair distribution --I have the sneaking suspicion this skews closer to center
                candidate /= 2.0

                //rather than build the candidate here, i could just use a N-step bsearch (eg 20 step) to find the edge,
                //then interpolate linearly between the base and the edge.
            }

            results += base vecPlus candidate
        }

        return results
    }

    private fun makeBoundedOffset(base: InputVector, direction: InputVector): InputVector{

        var factor = Double.POSITIVE_INFINITY

        for(inputVar in inputVariables){
            val candidate = inputVar.run {
                if(direction[name]!! > 0.0) (upperBound - base[name]!!) / direction[name]!!
                else (base[name]!! - lowerBound) / direction[name]!!
            }
            factor = Math.min(factor, candidate)
        }

        return direction * factor
    }


    private fun randomUnitVector(inputs: List<String>): InputVector {

        val unnormalized = (0 until inputs.size).map { random.nextDouble() }
        val length = unnormalized.sum()

        val normalized = unnormalized.map { it / length }

        return inputs.zip(normalized).toMap().toImmutableMap()
    }

    companion object: ConstraintSolvingPoolFactory {
        override fun create(inputSpec: List<InputVariable>, constraints: List<BabelExpression>)
                = RandomBoundedWalkingPool(inputSpec, constraints, Random())

    }

    class Factory(val random: Random): ConstraintSolvingPoolFactory {
        override fun create(inputSpec: List<InputVariable>, constraints: List<BabelExpression>)
                = RandomBoundedWalkingPool(inputSpec, constraints, random)

    }
}