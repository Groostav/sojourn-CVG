package com.empowerops.sojourn

import com.empowerops.babel.*
import com.empowerops.babel.BabelParser.*
import com.microsoft.z3.*
import kotlinx.collections.immutable.*
import org.antlr.v4.runtime.RuleContext
import org.antlr.v4.runtime.tree.ParseTree
import java.util.*

class Z3SolvingPool(val ctx: Context, val solver: Solver, val constraints: List<BabelExpression>): ConstraintSolvingPool {

    companion object: ConstraintSolvingPoolFactory {

        init {
            println("PATH is ${System.getenv("PATH")}")
            println("java.library.path is ${System.getProperty("java.library.path")}")

//            System.loadLibrary("msvcr110")
            System.loadLibrary("libz3")
            System.loadLibrary("libz3java")
        }

        override fun create(
                inputSpec: List<InputVariable>,
                constraints: List<BabelExpression>
        ): Z3SolvingPool {


            val ctx = Context()
            return ctx.config {

                val recompiler = BabelCompiler()
                val solver: Solver = ctx.mkSolver()

                //1: input bounds
                val inputExprs = inputSpec.associate { input ->
                    val inputExpr = ctx.mkRealConst(input.name)

                    solver.add(inputExpr gt input.lowerBound.asZ3Ratio())
                    solver.add(inputExpr lt input.upperBound.asZ3Ratio())

                    input.name to inputExpr
                }

                //2: transcode constraint expressions
                constraints.forEach { constraint ->

                    val transcoder = BabelZ3TranscodingWalker(ctx, inputExprs)
                    recompiler.compile(constraint.expressionLiteral, transcoder)

                    val newSatState = solver.check()

                    if(newSatState != Status.SATISFIABLE){
                        TODO("$constraint made constraint set $newSatState\n solver is:\n$solver")
                        //we could simply drop this and do a guess-and-check
                    }

                    solver.add(transcoder.transcodedExpr)
                }

                Z3SolvingPool(ctx, solver, constraints)
            }
        }

    }

    override fun makeNewPointGeneration(pointCount: Int, existingPoints: ImmutableList<InputVector>): ImmutableList<InputVector> {

        //TODO: use a distence metric + optimization, rather than simple model subtraction.
        //or use a mkTupleSort? maybe just use an array?
//                val pointCtor = ctx.mkDatatypeSort("point", arrayOf(ctx.mkConstructor("point", "point", arrayOf("x1"), arrayOf(ctx.mkRealSort()), null)))
//                val p0 = ctx.mkConstDecl("p0", pointCtor)
//                solver.add(ctx.mkEq(ctx.selec()))

        var resolved = solver.check()

        if(resolved != Status.SATISFIABLE) return immutableListOf()

        var model = solver.model
        val seed = model.buildInputVector()

        var results = immutableListOf(seed)

        for(index in 1 until pointCount){
            model.constDecls
                    .map { ctx.mkNot(ctx.mkEq(model.getConstInterp(it), ctx.mkRealConst(it.name))) }
                    .forEach { solver.add(it) }

            resolved = solver.check()
            if(resolved != Status.SATISFIABLE) { break }

            model = solver.model
            val nextResult = model.buildInputVector()

            if ( ! constraints.passFor(nextResult)) { break }

            results += nextResult
        }

        return results
    }
}

fun Model.buildInputVector(): InputVector = constDecls.map {
    val interp = getConstInterp(it) as RatNum
    val decimal = interp.numerator.bigInteger.toDouble() / interp.denominator.bigInteger.toDouble()

    it.name.toString() to decimal
}.toMap().toInputVector()


fun <R> Context.config(mutator: ContextConfigurator.() -> R): R = ContextConfigurator(this).mutator()

class ContextConfigurator(val ctx: Context) {
    infix fun ArithExpr.gt(right: ArithExpr): BoolExpr = ctx.mkGt(this, right)
    infix fun ArithExpr.lt(right: ArithExpr): BoolExpr = ctx.mkLt(this, right)

    fun Double.asZ3Literal(): RealExpr = ctx.mkFPToReal(ctx.mkFPNumeral(this, ctx.mkFPSortDouble()))
    fun Double.asZ3Ratio(): ArithExpr = this.toString().toIntRatio().let { ctx.mkReal(it.first, it.second) }
}

class BabelZ3TranscodingWalker(val z3: Context, val vars: Map<String, RealExpr>): BabelParserBaseListener() {

    lateinit var transcodedExpr: BoolExpr
        private set

    //TODO: null safety on push/pop
    val exprs: Deque<ArithExpr> = LinkedList()

    override fun exitExpr(ctx: BabelParser.ExprContext) {

        when {

            ctx.negate() != null -> {
                val child = exprs.pop()
                exprs.push(z3.mkUnaryMinus(child))
            }

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
                exprs.push(z3.mkReal(ctx.FLOAT().text))
            }
            ctx.INTEGER() != null -> {
                exprs.push(z3.mkInt(ctx.text.toLong()))
            }
            ctx.CONSTANT() != null -> when(ctx.text.toLowerCase()){
                "pi" -> exprs.push(z3.mkReal("pi"))
                else -> TODO()
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