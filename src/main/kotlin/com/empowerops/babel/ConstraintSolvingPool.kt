package com.empowerops.babel

import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.ImmutableMap

typealias InputVector = ImmutableMap<String, Double>

data class InputVariable(val name: String, val lowerBound: Double, val upperBound: Double)

interface ConstraintSolvingPoolFactory {
    fun create(inputSpec: List<InputVariable>, constraints: List<BabelExpression>): ConstraintSolvingPool
}

interface ConstraintSolvingPool {
    fun makeNewPointGeneration(pointCount: Int): ImmutableList<InputVector>
}



fun Double.isPassedConstraint(): Boolean = this <= 0.0
