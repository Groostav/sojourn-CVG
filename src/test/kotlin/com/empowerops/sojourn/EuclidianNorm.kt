package com.empowerops.sojourn

import kotlinx.collections.immutable.*
import kotlinx.collections.immutable.immutableMapOf
import java.util.concurrent.atomic.DoubleAccumulator


fun findDispersion(points: List<InputVector>): Pair<InputVector, Double> {

    val center = findCenter(points)

    // as per a simple euclidian distence:
    // https://stats.stackexchange.com/questions/13272/2d-analog-of-standard-deviation
    val deviation = points.sumByDouble { point ->
        val r = point.keys.sumByDouble { Math.pow(point[it]!! - center[it]!!, 2.0) }
        return@sumByDouble Math.sqrt(r)
    }

    return center to deviation / points.size
}

fun findCenter(points: List<InputVector>): InputVector {
    var center = points.first().mapValues { 0.0 }

    for(point in points){
        for(key in center.keys){
            center += key to (center[key]!! + point[key]!!)
        }
    }

    for(key in center.keys){
        center += key to center[key]!! / points.size
    }

    return center
}


inline fun <K, V, R> ImmutableMap<K, V>.mapValues(transform: (V) -> R): ImmutableMap<K, R>{
    val container = immutableMapOf<K, R>().builder()
    for((key, value) in this){
        container[key] = transform(value)
    }
    return container.build()
}

