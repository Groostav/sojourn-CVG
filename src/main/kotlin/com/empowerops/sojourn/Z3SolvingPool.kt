package com.empowerops.sojourn

import com.empowerops.babel.*
import com.empowerops.babel.BabelParser.*
import com.microsoft.z3.*
import kotlinx.collections.immutable.*
import org.antlr.v4.runtime.RuleContext
import org.antlr.v4.runtime.tree.ParseTree
import java.util.*

class Z3SolvingPool(
        val ctx: Context,
        val solver: Solver,
        val inputs: List<InputVariable>,
        val constraints: List<BabelExpression>
): ConstraintSolvingPool {

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
                val solver = ctx.mkSolver(ctx.mkTactic("qfnra-nlsat"))

                //1: input bounds
                val inputExprs = inputSpec.associate { input ->
                    val inputExpr = ctx.mkRealConst(input.name)

                    solver.add(inputExpr gt input.lowerBound.asZ3Real())
                    solver.add(inputExpr lt input.upperBound.asZ3Real())

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

                    transcoder.requirements.forEach { solver.add(it) }
                }

                Z3SolvingPool(ctx, solver, inputSpec, constraints)
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

        if(resolved == Status.UNSATISFIABLE) return immutableListOf()

        var model = solver.model
        val seed = model.buildInputVector(inputs)

        if ( ! constraints.passFor(seed)) {
            return immutableListOf()
        }
        var results = immutableListOf(seed)

//        FAIL; //not sure, model looks ok but under the debugger the solver just magically shifts.
        //problem is that the temp in a sqrt can be negative!@
        for(index in 1 until pointCount){
            model.constDecls
                    .filter { it.name.toString() in inputs.map { it.name} }
                    .map { ctx.mkNot(ctx.mkEq(model.getConstInterp(it), ctx.mkRealConst(it.name))) }
                    .forEach { solver.add(it) }

            resolved = solver.check()
            if(resolved == Status.UNSATISFIABLE) { break }

            model = solver.model
            val nextResult = model.buildInputVector(inputs)

            if ( ! constraints.passFor(nextResult)) {
                break
            }

            results += nextResult
        }

        return results
    }
}

fun Model.buildInputVector(inputs: List<InputVariable>): InputVector = constDecls
        .map {
            it.name.toString() to getConstInterp(it)
        }
        .filter {
            it.first in inputs.map { it.name }
        }
        .map {
            val interp = it.second
            val decimal = when(interp){
                is RatNum -> interp.numerator.bigInteger.toDouble() / interp.denominator.bigInteger.toDouble()
                is IntNum -> interp.bigInteger.toDouble()
                else -> TODO()
            }
            it.first to decimal
        }
        .toMap()
        .toInputVector()


fun <R> Context.config(mutator: ContextConfigurator.() -> R): R = ContextConfigurator(this).mutator()

class ContextConfigurator(val ctx: Context) {
    infix fun ArithExpr.gt(right: ArithExpr): BoolExpr = ctx.mkGt(this, right)
    infix fun ArithExpr.lt(right: ArithExpr): BoolExpr = ctx.mkLt(this, right)

    fun Double.asZ3Real(): ArithExpr = ctx.mkReal(this.toString())
}

class BabelZ3TranscodingWalker(val z3: Context, val vars: Map<String, RealExpr>): BabelParserBaseListener() {

    var requirements: List<BoolExpr> = emptyList()

    //TODO: null safety on push/pop
    val exprs: Deque<ArithExpr> = LinkedList()

    override fun exitExpr(ctx: BabelParser.ExprContext) {

        val transcoded = when {

            ctx.literal() != null || ctx.variable() != null -> null

            ctx.negate() != null -> {
                val child = exprs.pop()
                z3.mkUnaryMinus(child)
            }

            ctx.unaryFunction() != null -> {
                val arg = exprs.pop()

                when(ctx[0].text) {
                    "sqrt" -> {
                        val rooted = z3.mkAnonRealConst()
                        requirements += z3.mkGt(rooted, z3.mkReal("0.0"))
                        requirements += z3.mkEq(arg, z3.mkMul(rooted, rooted))
                        rooted
                    }
                    "cbrt" -> {
                        val tripleRooted = z3.mkAnonRealConst()
                        requirements += z3.mkEq(arg, z3.mkMul(tripleRooted, tripleRooted, tripleRooted))
                        tripleRooted
                    }
                    //do a tree-match on expr ^ (1/exprB), then do a `mkMul(*exprB.toArray())`?
                    "log" -> {
//                        val logged = z3.mkAnonRealConst()
                        val logged = z3.mkIntConst("T_${tempId++}")
                        requirements += z3.mkEq(arg, z3.mkPower(z3.mkInt("10"), logged))
                        logged
                    }
                    "ln" -> {
                        val lawned = z3.mkAnonRealConst()
                        requirements += z3.mkEq(arg, z3.mkPower(z3.mkReal(Math.E.toString()), lawned))
                        lawned
                    }
                    else -> TODO()
                }
            }
            ctx.callsBinaryOp() -> {
                val right = exprs.pop()
                val left = exprs.pop()

                when(ctx[1]) {
                    is PlusContext -> z3.mkAdd(left, right)
                    is MinusContext -> z3.mkSub(left, right)
                    is MultContext -> z3.mkMul(left, right)
                    is DivContext -> z3.mkDiv(left, right)
                    is ModContext -> TODO() //z3 only defines mod for ints
                    is RaiseContext -> z3.mkPower(left, right)

                    is GtContext -> z3.mkGt(left, right)
                    is GteqContext -> z3.mkGe(left, right)
                    is LtContext -> z3.mkLt(left, right)
                    is LteqContext -> z3.mkLe(left, right)

                    else -> TODO()
                }
            }
            else -> TODO("op for ${ctx.text}")
        }

        when (transcoded){
            null -> {}
            is ArithExpr -> exprs.push(transcoded)
            is BoolExpr -> requirements += transcoded
            else -> TODO()
        }
    }

    override fun exitVariable(ctx: VariableContext) {
        exprs.push(vars(ctx.text))
    }

    override fun exitLiteral(ctx: LiteralContext) {
        exprs.push(when {
            ctx.FLOAT() != null -> z3.mkReal(ctx.FLOAT().text)
            ctx.INTEGER() != null -> z3.mkReal(ctx.INTEGER().text)
            ctx.CONSTANT() != null -> when(ctx.text.toLowerCase()){
                "pi" -> z3.mkReal(Math.PI.toString())
                "e" -> z3.mkReal(Math.E.toString())
                else -> TODO()
            }
            else -> TODO()
        })

    }
}

operator fun RuleContext.get(index: Int): ParseTree = getChild(index)

private inline operator fun <K, V> Map<K, V>.invoke(key: K): V = getValue(key)

private var tempId: Int = 0
private fun Context.mkAnonRealConst(): RealExpr = mkRealConst("T_${tempId++}")