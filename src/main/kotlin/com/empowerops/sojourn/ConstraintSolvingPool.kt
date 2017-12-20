package com.empowerops.sojourn

import com.empowerops.babel.BabelExpression
import kotlinx.collections.immutable.ImmutableList
import java.util.*
import kotlin.collections.AbstractSet

//typealias InputVector = ImmutableMap<String, Double>

data class InputVariable(val name: String, val lowerBound: Double, val upperBound: Double)

val InputVariable.span: Double get() = upperBound - lowerBound

interface ConstraintSolvingPoolFactory {
    fun create(inputSpec: List<InputVariable>, constraints: Collection<BabelExpression>): ConstraintSolvingPool
}

interface ConstraintSolvingPool {
    fun makeNewPointGeneration(pointCount: Int, existingPoints: ImmutableList<InputVector>): ImmutableList<InputVector>
}

inline fun Map<String, Double>.toInputVector() = InputVector(this)
inline fun List<Pair<String, Double>>.toInputVector() = InputVector(this)

class InputVector : Map<String, Double> {

    companion object {
//        val EMPTY: InputVector = InputVector(keys = TreeSet())
    }

    val _keys: Array<String>
    val _values: DoubleArray

    var __keys: Set<String>? = null
    var __values: List<Double>? = null
    var _entries: EntrySet? = null

    private constructor(keys: Array<String>){
        _keys = keys
        _values = DoubleArray(keys.size)
    }

    constructor(vararg values: Pair<String, Double>){
        _keys = Array<String>(values.size) { values[it].first }
        _values = DoubleArray(values.size) { values[it].second }
    }
    constructor(values: List<Pair<String, Double>>){
        _keys = Array<String>(values.size) { values[it].first }
        _values = DoubleArray(values.size) { values[it].second }
    }
    constructor(values: Map<String, Double>) {
        _keys = Array<String>(values.size){ "" }
        _values = DoubleArray(values.size)

        var index = 0
        for((key, value) in values){
            _keys[index] = key
            _values[index] = value
            index += 1
        }
    }

    override val size: Int get() = keys.size
    override val entries: Set<Map.Entry<String, Double>> get() = _entries ?: EntrySet().also { _entries = it }

    override fun containsValue(value: Double) = value in _values
    override fun containsKey(key: String): Boolean = key in keys
    override fun get(key: String): Double? = if(key in keys) _values[_keys.indexOf(key)] else null
    override fun isEmpty() = size == 0
    override val values: List<Double> get() = __values ?: _values.asList().also { __values = it }
    override val keys: Set<String> get() = __keys ?: KeySet().also { __keys = it }

    override fun toString(): String = "<${entries.joinToString { (k, v) -> "$k=$v" }}>"

    infix fun vecPlus(right: InputVector): InputVector {
        require(keys == right.keys)

        val result = InputVector(_keys)

        for(index in 0 .. (_values.size - 1)){
            result._values[index] = _values[index] + right._values[index]
        }

        return result
    }

    infix fun vecMinus(right: InputVector): InputVector {
        require(keys == right.keys)

        val result = InputVector(_keys)

        for(index in 0 .. (_values.size - 1)){
            result._values[index] = _values[index] - right._values[index]
        }

        return result
    }

    fun mapValues(transform: (String, Double) -> Double): InputVector {

        val result = InputVector(_keys)

        for((index, key) in keys.withIndex()){
            result._values[index] = transform(key, _values[index])
        }

        return result
    }

    operator fun times(scalar: Double): InputVector {
        val result = InputVector(_keys)

        for(index in 0 .. (_values.size - 1)){
            result._values[index] = _values[index] * scalar
        }

        return result
    }
    inline operator fun div(scalar: Double) = times(1.0/scalar)

    inner class EntrySet: AbstractSet<Map.Entry<String, Double>>() {
        override val size = this@InputVector.size
        override fun contains(element: Map.Entry<String, Double>) = element.key in keys

        override fun iterator(): Iterator<Map.Entry<String, Double>> = object: Iterator<Map.Entry<String, Double>> {
            val keysIter = keys.iterator()
            var index: Int = 0

            override fun hasNext() = keysIter.hasNext()
            override fun next() = AbstractMap.SimpleEntry(keysIter.next(), _values[index++])

        }
    }

    inner class KeySet: AbstractSet<String>(){
        override fun iterator(): Iterator<String> = _keys.iterator()
        override val size = _keys.size
    }
}