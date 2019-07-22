package com.empowerops.sojourn

import org.testng.annotations.Test

class IntegrationFixture {

    @Test fun `commandLineP118`(){
        val params = P118.inputs.flatMap { listOf("--input", it.toCLIString()) }
        val expressions = P118.constraints.flatMap { listOf("&&", it.expressionLiteral) }.drop(1)

        val args = (params + expressions).toTypedArray()

        main(args)

        TODO("use jvm fork? get from standard output? add kotlinx.exec and getoptk?")
    }
}

fun InputVariable.toCLIString(): String = "$name:{lower:$lowerBound,step:$stepsize,upper:$upperBound}"