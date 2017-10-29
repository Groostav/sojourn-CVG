package com.empowerops.sojourn

import com.empowerops.babel.*
import com.empowerops.babel.BabelParser.*
import com.microsoft.z3.*
import kotlinx.collections.immutable.*
import org.antlr.v4.runtime.RuleContext
import org.antlr.v4.runtime.tree.ParseTree
import java.util.*

class Z3SolvingPool(
        val inputs: List<InputVariable>,
        val constraints: List<BabelExpression>
): ConstraintSolvingPool {

    private val recompiler = BabelCompiler()
    private val z3 = Context()
//    private val solver = z3.configure { Solver(Tactic("qfnra-nlsat")) }
    private val solver = z3.configure { Solver() }
    private val inputExprs: Map<String, RealExpr>

    val mod: FuncDecl by lazyZ3 { Function("mod2", realSort, realSort, returnType = realSort) }
    val quot: FuncDecl by lazyZ3 { Function("quot2", realSort, realSort, returnType = realSort) }
    val sgn: FuncDecl by lazyZ3 { Function("sgn", realSort, returnType = realSort) }

    fun <R> lazyZ3(initializer: ContextConfigurator.() -> R) = lazy { z3.configure(initializer) }

    companion object: ConstraintSolvingPoolFactory {

        init {
            println("PATH is ${System.getenv("PATH")}")
            println("java.library.path is ${System.getProperty("java.library.path")}")

//            System.loadLibrary("msvcr110") //TBD: preloading this things deps should mean we can get it off the PATH.
            System.loadLibrary("libz3")
            System.loadLibrary("libz3java")
        }

        override fun create(
                inputSpec: List<InputVariable>,
                constraints: List<BabelExpression>
        )
                = Z3SolvingPool(inputSpec, constraints).apply { checkConstraints() }
    }

    init {
        inputExprs = z3.configure {
            //1: input bounds
            inputs.associate { input ->
                val inputExpr = Real(input.name)

                solver += inputExpr gt input.lowerBound.asZ3Real()
                solver += inputExpr lt input.upperBound.asZ3Real()

                input.name to inputExpr
            }
        }
    }

    private fun checkConstraints() = z3.configure {

        require(solver.check() == Status.SATISFIABLE) { "before adding constraints solver SAT is ${solver.check()}:\n $solver " }

        //2: transcode constraint expressions
        constraints.forEach { constraint ->

            val transcoder = BabelZ3TranscodingWalker()
            recompiler.compile(constraint.expressionLiteral, transcoder)

            val newSatState = solver.check()

            if(newSatState != Status.SATISFIABLE){
                TODO("$constraint made constraint set $newSatState\n solver is:\n$solver")
                //we could simply drop this and do a guess-and-check
            }

            transcoder.requirements.forEach { solver += it }
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

        z3.configure {
            //        FAIL; //not sure, model looks ok but under the debugger the solver just magically shifts.
            //problem is that the temp in a sqrt can be negative!@
            for(index in 1 until pointCount){
                model.constDecls
                        .filter { it.name.toString() in inputs.map { it.name} }
                        .map { ! (model.getConstInterp(it) eq Real(it.name)) }
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

    inner class BabelZ3TranscodingWalker: BabelParserBaseListener() {

        var requirements: List<BoolExpr> = emptyList()

        //TODO: null safety on push/pop
        val exprs: Deque<ArithExpr> = LinkedList()

        override fun exitExpr(ctx: BabelParser.ExprContext) = z3.configureReals {

            val transcoded = when {

                ctx.literal() != null || ctx.variable() != null -> null

                ctx.negate() != null -> {
                    val child = exprs.pop()
                    z3.mkUnaryMinus(child)
                }

                ctx.unaryFunction() != null -> {
                    val arg = exprs.pop()

                    when(ctx[0].text) {
                        "sgn" -> {
                            requirements += listOf(
                                    arg eq 0 implies (sgn.invoke<ArithExpr>(arg) eq 0),
                                    arg gt 0 implies (sgn.invoke<ArithExpr>(arg) eq 1),
                                    arg lt 0 implies (sgn.invoke<ArithExpr>(arg) eq -1)
                            )

                            sgn(arg)
                        }
                        "sqrt" -> {
                            val rooted = z3.mkAnonRealConst()
                            requirements += rooted gt 0
                            requirements += arg eq rooted * rooted
                            rooted
                        }
                        "cbrt" -> {
                            val tripleRooted = z3.mkAnonRealConst()
                            requirements += arg eq tripleRooted * tripleRooted * tripleRooted
                            tripleRooted
                        }
                    //do a tree-match on expr ^ (1/exprB), then do a `mkMul(*exprB.toArray())`?
                        "log" -> {
                            val logged = z3.mkAnonRealConst()
                            requirements += arg eq (10 pow logged)
                            logged
                        }
                        "ln" -> {
                            val lawned = z3.mkAnonRealConst()
                            requirements += arg eq (E pow lawned)
                            lawned
                        }
                        else -> TODO()
                    }
                }
                ctx.callsBinaryOp() -> {
                    val right = exprs.pop()
                    val left = exprs.pop()

                    when(ctx[1]) {
                        is PlusContext -> left + right
                        is MinusContext -> left - right
                        is MultContext -> left * right
                        is DivContext -> left / right
                        is RaiseContext -> left pow right

                        is ModContext -> {

                            //    mod = z3.Function('mod', z3.RealSort(),z3.RealSort(), z3.RealSort())
                            //    quot = z3.Function('quot', z3.RealSort(),z3.RealSort(), z3.IntSort())
                            //    s = z3.Solver()
                            //
                            //    def mk_mod_axioms(X,k):
                            //      s.add(Implies(k != 0, 0 <= mod(X,k)),
                            //          Implies(k > 0, mod(X,k) < k),
                            //          Implies(k < 0, mod(X,k) < -k),
                            //          Implies(k != 0, k*quot(X,k) + mod(X,k) == X))
                            //
                            //    x, y = z3.Reals('x y')
                            //
                            //    mk_mod_axioms(x, 3)
                            //    mk_mod_axioms(y, 5)

                            val X = left
                            val k = right

                            requirements += listOf(

                                    0 lt mod(X, k),
                                    0 neq quot(X, k),
                                    (k gt 0) implies (mod<ArithExpr>(X, k) lt k),
                                    (k lt 0) implies (mod<ArithExpr>(X, k) lt -k),
                                    k * quot<ArithExpr>(X, k) + mod<ArithExpr>(X, k) eq X
                            )

                            mod(left, right)
                        }

                        is GtContext -> left gt right
                        is GteqContext -> left gte right
                        is LtContext -> left lt right
                        is LteqContext -> left lte right

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
            exprs.push(inputExprs(ctx.text))
        }

        override fun exitLiteral(ctx: LiteralContext) = z3.configure {
            exprs.push(when {
                ctx.FLOAT() != null -> z3.mkReal(ctx.FLOAT().text)
                ctx.INTEGER() != null -> z3.mkReal(ctx.INTEGER().text)
                ctx.CONSTANT() != null -> when(ctx.text.toLowerCase()){
                    "pi" -> PI
//                    val exprCtor = Expr::class.staticFunctions
//                        .single { it.name == "create" && it.parameters.size == 2 }
//                        .apply { isAccessible = true }
//                    val nCtxMember = Context::class.members
//                        .single { it.name == "nCtx" }
//                        .apply { isAccessible = true }
//                    val nCtxPointer = nCtxMember.call(z3) as Long
//                    val nativePiPointer = Native.rcfMkPi(nCtxPointer)
//                    exprCtor.call(z3, nativePiPointer) as ArithExpr
                    "e" -> E
                    else -> TODO()
                }
                else -> TODO()
            })
        }

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


operator fun RuleContext.get(index: Int): ParseTree = getChild(index)

private inline operator fun <K, V> Map<K, V>.invoke(key: K): V = getValue(key)

private var tempId: Int = 0
private fun Context.mkAnonRealConst(): RealExpr = mkRealConst("T_${tempId++}")