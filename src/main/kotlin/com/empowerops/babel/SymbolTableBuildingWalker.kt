package com.empowerops.babel

import com.empowerops.babel.SymbolTable
import com.empowerops.babel.todo_deleteme.BabelParser
import com.empowerops.babel.todo_deleteme.BabelParserBaseListener
import org.antlr.v4.runtime.ParserRuleContext
import java.util.*

/**
 * Created by Justin Casol on 2/2/2015.
 */
class SymbolTableBuildingWalker : BabelParserBaseListener() {

    val table = SymbolTable()
    private val errors = HashSet<BabelExpressionProblem>()

    override fun exitVariable(ctx: BabelParser.VariableContext) {
        val symbol = ctx.text
        table.registerSymbolUsage(ctx, symbol)
    }

    override fun enterName(ctx: BabelParser.NameContext) {
        val symbol = ctx.text
        table.declareSymbol(ctx.getParent(), symbol)
    }

    override fun exitDynamicVariableAccess(ctx: BabelParser.DynamicVariableAccessContext) {
        table.setContainsDynamicVarLookup(true)
    }

    val semanticProblems: Set<BabelExpressionProblem>
        get() = errors
}

