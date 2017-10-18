package com.empowerops.sojourn

import com.empowerops.babel.*
import com.empowerops.babel.BabelParser.*
import com.microsoft.z3.*
import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.immutableListOf
import org.antlr.v4.runtime.RuleContext
import org.antlr.v4.runtime.tree.ParseTree
import java.util.*

class Z3SolvingPool(val results: ImmutableList<InputVector>): ConstraintSolvingPool {

    override fun makeNewPointGeneration(pointCount: Int, existingPoints: ImmutableList<InputVector>)
            = results

    companion object: ConstraintSolvingPoolFactory {

        override fun create(
                inputSpec: List<InputVariable>,
                constraints: List<BabelExpression>
        ): Z3SolvingPool {

            val recompiler = BabelCompiler()

            val ctx = Context()
            val model = ctx.config {

                val solver: Solver = ctx.mkSolver()

                //1: input bounds
                val inputExprs = inputSpec.associate { input ->
                    val inputExpr = ctx.mkRealConst(input.name)

                    solver.add(inputExpr gt input.lowerBound.asZ3Literal())
                    solver.add(inputExpr lt input.upperBound.asZ3Literal())

                    input.name to inputExpr
                }

                //2: transcode constraint expressions
                constraints.forEach { constraint ->

                    val transcoder = BabelZ3TranscodingWalker(ctx, inputExprs)
                    recompiler.compile(constraint.expressionLiteral, transcoder)

                    solver.add(transcoder.transcodedExpr)
                }


                //or use a mkTupleSort? maybe just use an array?
                val pointCtor = ctx.mkDatatypeSort("point", arrayOf(ctx.mkConstructor("point", "point", arrayOf("x1"), arrayOf(ctx.mkRealSort()), null)))

                val p0 = ctx.mkConstDecl("p0", pointCtor)

//                solver.add(ctx.mkEq(ctx.selec()))

                val resolve = solver.check()

                solver.model
            }

            println(model.toString())

            val satisfyingInput = model.constDecls.map {
                val interp = model.getConstInterp(it) as RatNum
                val decimal = interp.numerator.int.toDouble() / interp.denominator.int

                it.name.toString() to decimal
            }.toMap()




            val results = immutableListOf(satisfyingInput.toInputVector())

            return Z3SolvingPool(results)
        }
    }
}

fun <R> Context.config(mutator: ContextConfigurator.() -> R): R = ContextConfigurator(this).mutator()

class ContextConfigurator(val ctx: Context) {
    infix fun ArithExpr.gt(right: ArithExpr): BoolExpr = ctx.mkGt(this, right)
    infix fun ArithExpr.lt(right: ArithExpr): BoolExpr = ctx.mkLt(this, right)

    fun Double.asZ3Literal(): RealExpr = ctx.mkFPToReal(ctx.mkFPNumeral(this, ctx.mkFPSortDouble()))
}

class BabelZ3TranscodingWalker(val z3: Context, val vars: Map<String, RealExpr>): BabelParserBaseListener() {

    lateinit var transcodedExpr: BoolExpr
        private set

    val exprs: Deque<ArithExpr> = LinkedList()

    override fun exitExpr(ctx: BabelParser.ExprContext) {

        when {

            ctx.callsBinaryOp() -> {
                val right = exprs.pop()
                val left = exprs.pop()

                val transcoded = when(ctx[1]) {
                    is PlusContext -> z3.mkAdd(left, right)
                    is MinusContext -> z3.mkSub(left, right)
                    is MultContext -> z3.mkMul(left, right)
                    is DivContext -> z3.mkDiv(left, right)
                    is ModContext -> TODO() //z3 only defines mod for ints

                    is GtContext -> z3.mkGt(left, right)
                    is GteqContext -> z3.mkGe(left, right)
                    is LtContext -> z3.mkLt(left, right)
                    is LteqContext -> z3.mkLe(left, right)

                    else -> TODO()
                }

                when (transcoded){
                    is ArithExpr -> exprs.push(transcoded)
                    is BoolExpr -> transcodedExpr = transcoded
                    else -> TODO()
                }
            }
        }
    }

    override fun exitVariable(ctx: VariableContext) {
        exprs.push(vars(ctx.text))
    }

    override fun exitLiteral(ctx: LiteralContext) {
        when {
            ctx.FLOAT() != null -> {
                val (numerator, denominator) = ctx.text.toIntRatio()
                exprs.push(z3.mkReal(numerator, denominator))
            }
            ctx.INTEGER() != null -> {
                exprs.push(z3.mkInt(ctx.text.toIntStrict()))
            }
            ctx.CONSTANT() != null -> {
                TODO() //irrational numbers e and pi.
            }
            else -> TODO()
        } as Any

    }
}

operator fun RuleContext.get(index: Int): ParseTree = getChild(index)


fun String.toIntStrict(): Int = toInt().let { when(it) {
//TODO, this should probably be smarted to allow for the literal max/min value number
    Integer.MAX_VALUE -> throw NumberFormatException("overflow representing $this as integer")
    Integer.MIN_VALUE -> throw NumberFormatException("underflow representing $this as integer")
    else -> it
}}

fun String.toIntRatio(): Pair<Int, Int> {
    val numerator = replace(".", "").toIntStrict()
    val denominator = when {
        '.' !in this -> 1
        else -> Math.pow(10.0, 0.0+length - indexOf('.') - 1).toInt()
    }

    return numerator to denominator
}

private inline operator fun <K, V> Map<K, V>.invoke(key: K): V = getValue(key)