package com.empowerops.babel

import com.empowerops.babel.BabelParser.*
import com.microsoft.z3.*
import kotlinx.collections.immutable.ImmutableList
import org.antlr.v4.runtime.RuleContext
import org.antlr.v4.runtime.tree.ParseTree
import java.util.*

class Z3SolvingPool: ConstraintSolvingPool {

    override fun makeNewPointGeneration(pointCount: Int): ImmutableList<InputVector> {
//        val x =
        TODO()
    }


    companion object: ConstraintSolvingPoolFactory {

        override fun create(
                inputSpec: List<InputVariable>,
                constraints: List<BabelExpression>
        ): Z3SolvingPool {

            val recompiler = BabelCompiler()

            Context().config {

                //1: input bounds
                val inputExprs = inputSpec.associate { input ->
                    val inputExpr = ctx.mkRealConst(input.name)

                    inputExpr gt input.lowerBound.asZ3Literal()
                    inputExpr lt input.upperBound.asZ3Literal()

                    input.name to inputExpr
                }

                //2: transcode constraint expressions
                constraints.forEach {

                    val transcoder = BabelZ3TranscodingWalker(ctx, inputExprs)
                    it.walk(transcoder)
                }

                //3: add objective function
//                val intType = ctx.intSort
//                val realtype = ctx.realSort
//                val grid = ctx.mkConst("grid", ctx.mkArraySort(ctx.mkArraySort(TODO(), TODO()), TODO()), TODO())

                // euclidean distance d = sqrt( (x0-xa)^2 + (y0-ya)^2 + ... + (z0-za)^2 )
                // thats going to be realy hard to encode. Node that there is no "mkSum" exposed,
                // so it would have to be done via a `mkForAll(inputs)`, and im not sure how to specificy the aggregator function.

                // but what about something thats simpler to encode: multi objective on taxi-cab distance?
                // hmm, how do we grow the pool also? writing a grid (array of array) type in this dsl is going to be quite difficult.
//                opt.MkMaximize()
            }

            TODO()
        }
    }
}

fun <R> Context.config(mutator: ContextConfigurator.() -> R): R {
    TODO()
}

class ContextConfigurator(val ctx: Context) {
    infix fun ArithExpr.gt(right: ArithExpr) = ctx.mkGt(this, right)
    infix fun ArithExpr.lt(right: ArithExpr) = ctx.mkLt(this, right)

    fun Double.asZ3Literal() = ctx.mkReal(toString())
}

class BabelZ3TranscodingWalker(val z3: Context, val vars: Map<String, RealExpr>): BabelParserBaseListener() {

    lateinit var transcodedExpr: BoolExpr
        private set

    val exprs: Deque<ArithExpr> = TODO()

    override fun exitExpr(ctx: BabelParser.ExprContext) {

        when {

            ctx.callsBinaryOp() -> {
                val left = exprs.pop()
                val right = exprs.pop()

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
                TODO()
            }
            else -> TODO()
        } as Any

    }
}

fun BabelExpression.walk(listener: BabelParserListener): Unit = TODO()

operator fun RuleContext.get(index: Int): ParseTree = TODO()


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
