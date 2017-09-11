package com.empowerops.babel

import org.antlr.v4.runtime.tree.ParseTree

data class BabelExpressionProblem(val description: String, val parseTreeLocation: ParseTree?) {

    val sourcedDescription = description + ":\n" +
                if (parseTreeLocation != null) parseTreeLocation.text else "[unknown source]"

    override fun toString() = sourcedDescription
}