package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.ImmutableMap
import kotlinx.collections.immutable.immutableMapOf

typealias InputVector = ImmutableMap<String, Double>
fun InputVector() = immutableMapOf<String, Double>()

data class InputVariable(val name: String, val lowerBound: Double, val upperBound: Double)

interface ConstraintSolvingPoolFactory {
    fun create(inputSpec: List<InputVariable>, constraints: List<BabelExpression>): ConstraintSolvingPool
}

interface ConstraintSolvingPool {
    fun makeNewPointGeneration(pointCount: Int, existingPoints: ImmutableList<InputVector>): ImmutableList<InputVector>
}



fun Double.isPassedConstraint(): Boolean = this <= 0.0
