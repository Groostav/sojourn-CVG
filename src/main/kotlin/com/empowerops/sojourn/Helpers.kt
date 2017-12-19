package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import kotlinx.collections.immutable.ImmutableMap
import kotlinx.collections.immutable.*
import kotlin.system.measureTimeMillis


fun <R> measureTime(op: () -> R): Pair<Long, R> {
    var result: Any? = null
    val time = measureTimeMillis {
        result = op()
    }
    @Suppress("UNCHECKED_CAST") //safe by inline-nature of measureTimeMillis
    return time to (result as R)
}

operator fun InputVector.div(scalar: Double): InputVector = mapValues { key, value -> value / scalar }
operator fun InputVector.times(scalar: Double): InputVector = mapValues { key, value -> value * scalar }

infix fun InputVector.vecMinus(other: InputVector): InputVector {
    require(this.size == other.size)

    val result = InputVector().builder()

    for((key, value) in this){
        result += key to value - other.getValue(key)
    }

    return result.build()
}

infix fun InputVector.vecPlus(other: InputVector): InputVector {
    require(this.size == other.size)

    var result = InputVector()

    //according to jprofiler the destructuring here causes an an Arrays.copyOf call
    // that takes 20% of our overall overhead.
    // need a more compact and faster datatype for InputVector.
    for((key, value) in this){
        result = result.put(key, value + other.getValue(key))
    }

    return result
}

fun List<InputVariable>.canProduce(vector: InputVector): Boolean{
    
    for((name, lowerBound, upperBound) in this){
        val value = vector[name]!!
        if(value < lowerBound || value > upperBound) { return false }
    }
    
    return true
}

inline fun Iterable<BabelExpression>.passFor(inputs: InputVector, tolerance: Double = 0.0)
        = all { it.evaluate(inputs).isPassedConstraint(tolerance) }

val InputVector.distance: Double get() = Math.sqrt(values.sumByDouble { Math.pow(it, 2.0) })


inline fun <K, V, R> ImmutableMap<K, V>.mapValues(transform: (K, V) -> R): ImmutableMap<K, R> {
    val result = immutableHashMapOf<K, R>().builder()

    for((key, value) in this){
        result += key to transform(key, value)
    }

    return result.build()
}
