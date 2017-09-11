import com.empowerops.linqalike.LinqingSet
import com.empowerops.linqalike.Queryable
import com.empowerops.problem_definition.parser.BabelParser
import com.empowerops.problem_definition.parser.BabelParserBaseListener
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.misc.NotNull

/**
 * Created by Justin Casol on 2/2/2015.
 */
class SymbolTableBuildingWalker : BabelParserBaseListener() {

    val table = SymbolTable()
    private val errors = LinqingSet<BabelExpressionProblem>()

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

    val semanticProblems: Queryable<BabelExpressionProblem>
        get() = errors
}

