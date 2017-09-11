import com.empowerops.common.ErrorContext
import com.empowerops.common.ErrorDescription
import com.empowerops.common.documentation.Immutable
import com.empowerops.common.documentation.ReflectionSensitive
import com.empowerops.common.documentation.Unordered
import com.empowerops.jargon.model.Evaluable
import com.empowerops.jargon.model.VariableSymbol
import com.empowerops.linqalike.Queryable
import com.empowerops.linqalike.QueryableMap
import com.empowerops.linqalike.common.Formatting
import org.antlr.v4.runtime.tree.ParseTree
import java.io.Serializable
import java.util.logging.Level
import java.util.logging.Logger


@Immutable
open class BabelExpression internal constructor(
        @ReflectionSensitive override val resultSymbol: VariableSymbol,
        @ReflectionSensitive override val literalExpression: String,
        // life cycle here is a bit weird,// its up to the serializers to get this right,
        private val compilerResult: BabelCompiler.CompilationResult
) : Serializable, Evaluable {

    val errors: Queryable<BabelExpressionProblem> = compilerResult.problems

    fun hasErrors(): Boolean = errors.any()

    override val isBooleanExpression = compilerResult.booleanExpression

    @Throws(RuntimeBabelException::class)
    override fun evaluate(values: QueryableMap<String, Double>): Double = synchronized(this) {

        log.log(Level.CONFIG, "called babel.evaluate with '" + Formatting.csv(values.values()) + "'")

        compilerResult.getSymbolTable().setAsStaticScope(values)
        try {
            val runResult = compilerResult.getExecutable().execute()
            return runResult.toDouble()
        }
        catch (error: IllegalArgumentException) {
            log.warning(error.localizedMessage)
            return Double.POSITIVE_INFINITY
        }
        catch (error: Exception) {
            throw RuntimeBabelException(
                    "there was an error evaluating the expression \n\t" +
                            "'" + literalExpression + "' " +
                            "at the point: \n\t" +
                            Formatting.verticallyPrintMembers(values.select({ l, r -> l + ":" + r })),
                    error
            )
        }
        catch (error: AssertionError) {
            throw RuntimeBabelException(
                    "there was an error evaluating the expression \n\t" + "'" + literalExpression + "' " + "at the point: \n\t" + Formatting.verticallyPrintMembers(
                            values.select({ l, r -> l + ":" + r })), error)
        }
        finally {
            compilerResult.getSymbolTable().clearCheapPointScope()
        }
    }

    @Unordered override fun allPossibleUsedIdentifiers(availableIdentifiers: Queryable<String>): Queryable<String> {

        val staticallyUsedVars = compilerResult.symbolTable.staticallyUsedSymbols

        if (compilerResult.getSymbolTable().containsDynamicVarLookup()) {
            return availableIdentifiers.union(staticallyUsedVars)
        }
        else {
            return staticallyUsedVars
        }
    }

    override fun getStaticallyUsedIdentifiers(): Queryable<String> = compilerResult.symbolTable.staticallyUsedSymbols

    override val isMathematicalExpression = true

    val functionName = resultSymbol.canonicalName

    override fun toString(): String {
        try {
            return "BABEL [ ${resultSymbol.canonicalName}" +
                    " = " +
                    "${ if (literalExpression.isEmpty()) "\"\"" else literalExpression } ]"
        }
        catch (e: Exception) {
            log.log(Level.WARNING, "error in toString()", e)
            return "BABEL { Error in toString: " + e.message + "}"
        }
        catch (e: AssertionError) {
            log.log(Level.WARNING, "error in toString()", e)
            return "BABEL { Error in toString: " + e.message + "}"
        }

    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other == null || javaClass != other.javaClass) return false

        val that = other as BabelExpression?

        if (literalExpression != that!!.literalExpression) return false
        return resultSymbol == that.resultSymbol

    }

    override fun hashCode(): Int {
        var result = literalExpression.hashCode()
        result = 31 * result + resultSymbol.hashCode()
        return result
    }


    class RuntimeBabelException(s: String, error: Throwable) : RuntimeException(s, error) {
        companion object {
            private val serialVersionUID = 3250565988984538375L
        }
    }

    companion object {

        val log = Logger.getLogger(BabelExpression::class.java.canonicalName)
        val NullInstance: BabelExpression = Null()

        private const val serialVersionUID = 5857326798585186200L

        @ErrorContext
        var onExpressionError = ErrorDescription.forStaticClassDescriptor(
                "The given expression could not be understood",
                "The expression supplied could not be understood by oasis. " +
                        "The expression was also supplied in a context \nwhere we did not check to see if the expression was valid," +
                        " meaning the problem exists internally in oasis." +
                        "\n Check to make sure any used function files (" + "opt.json" + " files) " +
                        "are OK.\n If the project was loaded, check to make sure the project files " +
                        "(" + "oasis" + " files) are OK."
        )
    }
}
class Null : BabelExpression(VariableSymbol.NullSymbol, "$[Null Expression]",
        BabelCompiler.CompilationResult.NullInstance) {

    @Throws(RuntimeBabelException::class)
    override fun evaluate(values: QueryableMap<String, Double>) = throw UnsupportedOperationException("evaluate")
}
