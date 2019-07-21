package com.empowerops.sojourn

import com.empowerops.babel.BabelCompiler
import com.empowerops.babel.BabelExpression
import com.empowerops.babel.CompilationFailure

suspend fun main(args: Array<String>){

//    if(args.firstOrNull() == "--")

    val expr = args.joinToString(" ")

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
                10,
                setOf(compiled)
            )

            println("${samples.satisfiable}")
            samples.values.forEach { println(it.toString()) }
        }
    }
}
