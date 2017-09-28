package com.empowerops.sojourn

import kotlinx.collections.immutable.*
import kotlinx.collections.immutable.immutableMapOf
import java.util.concurrent.atomic.DoubleAccumulator


fun findDispersion(names: List<String>, points: List<InputVector>): Pair<InputVector, Double> {

    val center = findCenter(names, points)

    // as per a simple euclidian distence:
    // https://stats.stackexchange.com/questions/13272/2d-analog-of-standard-deviation
    val deviation = if(points.isEmpty()) Double.NaN else points.sumByDouble { point ->
        val r = point.keys.sumByDouble { Math.pow(point[it]!! - center[it]!!, 2.0) }
        return@sumByDouble Math.sqrt(r)
    }

    return center to deviation / points.size
}

fun findCenter(names: List<String>, points: List<InputVector>): InputVector {
    var center = points.firstOrNull()?.mapValues { _, _ -> 0.0 }
            ?: return names.associate { it to Double.NaN }.toImmutableMap()

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
