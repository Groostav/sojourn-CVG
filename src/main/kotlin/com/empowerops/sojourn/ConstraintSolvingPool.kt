package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import kotlinx.collections.immutable.ImmutableList

//typealias InputVector = ImmutableMap<String, Double>

data class InputVariable(val name: String, val lowerBound: Double, val upperBound: Double)

val InputVariable.span: Double get() = upperBound - lowerBound

interface ConstraintSolvingPoolFactory {
    fun create(inputSpec: List<InputVariable>, constraints: Collection<BabelExpression>): ConstraintSolvingPool
}

interface ConstraintSolvingPool {
    fun makeNewPointGeneration(pointCount: Int, existingPoints: ImmutableList<InputVector>): ImmutableList<InputVector>
}

