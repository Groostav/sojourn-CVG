package com.empowerops.sojourn

import com.empowerops.babel.BabelCompiler
import com.empowerops.babel.BabelExpression
import com.empowerops.babel.CompilationFailure

suspend fun main(args: Array<String>){

    // TODO i would really prefer to use a library for this...
    // why not getoptk you dingus?
    var exprArgs = args.toList()

    val targetPointCount = if(args.firstOrNull() == "--targetPointCount"){
        when(val passed = args.drop(1).first()){
            "inf" -> Int.MAX_VALUE
            null -> Int.MAX_VALUE
            else -> passed.toInt()
        }.also {
            exprArgs = exprArgs.drop(2)
        }
    }
    else 10

    val expr = exprArgs.joinToString(" ")

    val compiled = BabelCompiler().compile(expr)

    when(compiled){
        is CompilationFailure -> {
            println("compilation failure: ${compiled.problems.joinToString("\n")}")
            return
        }
        is BabelExpression -> {

            val inputs = compiled.staticallyReferencedSymbols.map {
                InputVariable(it, 0.0, 1.0)
            }
            val samples = makeSamples(
                inputs,
                targetPointCount,
                setOf(compiled)
            )

            println("${samples.satisfiable}")
            samples.values.forEach { println(it.toString()) }
        }
    }
}
