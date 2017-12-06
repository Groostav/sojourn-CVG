package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.ImmutableMap
import kotlinx.collections.immutable.immutableHashMapOf
import kotlinx.collections.immutable.toImmutableHashMap

typealias InputVector = ImmutableMap<String, Double>
inline fun InputVector(vararg inputValuesByName: Pair<String, Double>): InputVector = immutableHashMapOf(*inputValuesByName)
inline fun Iterable<Pair<String, Double>>.toInputVector() = toMap().toImmutableHashMap()
inline fun Map<String, Double>.toInputVector() = toImmutableHashMap()

data class InputVariable(val name: String, val lowerBound: Double, val upperBound: Double)

val InputVariable.span: Double get() = upperBound - lowerBound

interface ConstraintSolvingPoolFactory {
    fun create(inputSpec: List<InputVariable>, constraints: List<BabelExpression>): ConstraintSolvingPool
}

interface ConstraintSolvingPool {
    fun makeNewPointGeneration(pointCount: Int, existingPoints: ImmutableList<InputVector>): ImmutableList<InputVector>
}



fun Double.isPassedConstraint(): Boolean = this <= 0.0
