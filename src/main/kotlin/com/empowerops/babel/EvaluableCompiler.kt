package com.empowerops.babel

/**
 * Jargon side interface into babel expressions, to allow for test classes (and other components)
 * to rely on something that looks suspiciously like a babel expression, without a direct runtime
 * dependency.
 *
 * Created by Geoff on 6/3/2016.
 */
interface EvaluableCompiler {
    fun compile(expressionLiteral: String): Evaluable
}

interface Evaluable {
    fun evaluate(values: Map<String, Double>): Double
}
