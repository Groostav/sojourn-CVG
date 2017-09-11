package com.empowerops.babel

import java.io.Serializable
import java.util.logging.Level
import java.util.logging.Logger
import javax.annotation.concurrent.Immutable

@Immutable
open class BabelExpression internal constructor(
        val literalExpression: String,
        // life cycle here is a bit weird,// its up to the serializers to get this right,
        private val compilerResult: BabelCompiler.CompilationResult
) : Serializable, Evaluable {

    val errors: Set<BabelExpressionProblem> = compilerResult.problems

    fun hasErrors(): Boolean = errors.any()

    @Throws(RuntimeBabelException::class)
    override fun evaluate(values: Map<String, Double>): Double = synchronized(this) {

        log.log(Level.CONFIG, "called babel.evaluate with '" + values.values.joinToString() + "'")

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


    class RuntimeBabelException(s: String, error: Throwable) : RuntimeException(s, error) {
        companion object {
            private val serialVersionUID = 3250565988984538375L
        }
    }

    companion object {

        val log = Logger.getLogger(BabelExpression::class.java.canonicalName)

        private const val serialVersionUID = 5857326798585186200L
    }
}