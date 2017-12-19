package com.empowerops.sojourn

import com.empowerops.babel.*
import com.empowerops.babel.BabelParser.*
import com.microsoft.z3.*
import kotlinx.collections.immutable.*
import org.antlr.v4.runtime.RuleContext
import org.antlr.v4.runtime.tree.ParseTree
import org.antlr.v4.runtime.tree.TerminalNode
import java.nio.file.Files
import java.nio.file.Paths
import java.util.*
import java.util.stream.Stream

class Z3SolvingPool private constructor(
        val inputs: List<InputVariable>,
        val constraints: Collection<BabelExpression>
): ConstraintSolvingPool {


    private val recompiler = BabelCompiler()
    private val z3 = Context()
//    private val solver = z3 { Solver(Tactic("qfnra-nlsat")) }
    private val solver = z3 { Solver() }
    
    private val inputExprs: Map<String, RealExpr> = z3 {
        //1: input bounds
        inputs.associate { input ->
            val inputExpr = Real(input.name)

            solver += inputExpr gt input.lowerBound.asZ3Real()
            solver += inputExpr lt input.upperBound.asZ3Real()

            input.name to inputExpr
        }
    }

//    val floor: FuncDecl by lazyZ3 { Function("floor", realSort, returnType = realSort) }
    val mod: BinaryFunction<ArithExpr, ArithExpr, ArithExpr> by lazyZ3 { BinaryFunction("mod2", Real, Real, Real) }
    val quot: BinaryFunction<ArithExpr, ArithExpr, ArithExpr> by lazyZ3 { BinaryFunction("quot2", Real, Real, Real) }
    val sgn: UnaryFunction<ArithExpr, ArithExpr> by lazyZ3 { UnaryFunction("sgn", Real, Real) }
    val abs: UnaryFunction<ArithExpr, ArithExpr> by lazyZ3 { UnaryFunction("abs", Real, Real) }

    val vars: UnaryFunction<ArithExpr, ArithExpr> by lazyZ3 {
        UnaryFunction("var", Real, Real).also {
            for((index, input) in inputs.withIndex()){
                solver += it((index + 1).zr) eq inputExprs[input.name]!!
            }
        }
    }

    companion object: ConstraintSolvingPoolFactory {

        init {
            // set sys_paths to null; this will force a re-parse of the java.library.path by System.loadLibrary,
            // thus pushing our changes.
            // note we might be able to do this with Unsafe:
            // https://javax0.wordpress.com/2017/05/03/hacking-the-integercache-in-java-9/
            ClassLoader::class.java.getDeclaredField("sys_paths").apply {
                isAccessible = true
                set(null, null)
            }

            val oldPathValues = (System.getProperty("java.library.path") ?: "")
                    .split(';')
                    .toSet()

            val newLibraryPath = System.getProperty("java.class.path").split(";")
                    .map { Paths.get(it).parent }
                    .asSequence()
                    .distinct()
                    .flatMap { Files.walk(it).asSequence() }
                    .filter { it.toString().let { it.endsWith(".dll") || it.endsWith(".so") || it.endsWith(".lib") }}
                    .map { it.parent }
                    .toSet()
                    .let { oldPathValues + (it - oldPathValues) }
                    .map { it.toString() }
                    .filter { it.isNotBlank() }
                    .joinToString(";")

            System.setProperty("java.library.path", newLibraryPath)

            listOf("msvcr110", "vcomp110", "libz3", "libz3java")
                    .map { System.loadLibrary(it) }
        }

        fun <T> Stream<T>.asSequence(): Sequence<T> = Sequence(this::iterator)

        override fun create(
                inputSpec: List<InputVariable>,
                constraints: Collection<BabelExpression>
        )
                = Z3SolvingPool(inputSpec, constraints).apply { applyConstraints() }
    }

    private fun applyConstraints() = z3 {

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

    class UnsatisfiableConstraintsException(solver: String): RuntimeException(solver)

    override fun makeNewPointGeneration(pointCount: Int, existingPoints: ImmutableList<InputVector>): ImmutableList<InputVector> {

        //TODO: use a distence metric + optimization, rather than simple model subtraction.
        //or use a mkTupleSort? maybe just use an array?
//                val pointCtor = ctx.mkDatatypeSort("point", arrayOf(ctx.mkConstructor("point", "point", arrayOf("x1"), arrayOf(ctx.mkRealSort()), null)))
//                val p0 = ctx.mkConstDecl("p0", pointCtor)
//                solver.add(ctx.mkEq(ctx.selec()))

        var resolved = solver.check()

        if(resolved == Status.UNSATISFIABLE) throw UnsatisfiableConstraintsException(solver.toString())

        var model = solver.model
        val seed = model.buildInputVector(inputs)

        if ( ! constraints.passFor(seed)) {
            //this is likely from a rounding error, we're gonna have to think of something smarter at some point.
//            return immutableListOf()
            val x = 4;
        }
        
        var results = immutableListOf(seed)

        z3 {

            for(index in 1 until pointCount){
                solver += model.constDecls
                        .filter { it.name.toString() in inputs.map { it.name } }
                        .flatMap { func ->
                            val offset = 0.000005 * inputs.single { it.name == func.name.toString() }.span
                            val value = model.getConstInterp(func) as ArithExpr
                            val temp = z3.mkAnonRealConst()
                            listOf(
                                    temp eq value,
                                    (Real(func.name) lt (temp - offset)) or (Real(func.name) gt (temp + offset))
                            )
                        }

                resolved = solver.check()
                if(resolved == Status.UNSATISFIABLE) {
                    //likely our point negation strategy pushed us into UNSAT
                    break
                }

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

    fun <T> Deque<T>.pop(count: Int) = (1 .. count).map { this.pop() }

    inner class BabelZ3TranscodingWalker: BabelParserBaseListener() {

        var requirements: List<BoolExpr> = emptyList()

        //TODO: null safety on push/pop
        val exprs: Deque<ArithExpr> = LinkedList()

        override fun exitBooleanExpr(ctx: BooleanExprContext) = z3 {
            val dk = when {
                ctx.callsBinaryOp() -> {
                    val right = exprs.pop()
                    val left = exprs.pop()

                    requirements += when {
                        ctx.gt() != null -> left gt right
                        ctx.lt() != null -> left lt right
                        ctx.gteq() != null -> left gte right
                        ctx.lteq() != null -> left lte right

                        else -> TODO("unknown: ${ctx.text}")
                    }
                }
                ctx.eq() != null -> {
                    val (offset, right, left) = exprs.pop(3)

                    val (offsetSym, rightSym, leftSym) = listOf(offset, right, left).fold(emptyList<ArithExpr>()){ accum, next ->
                        val nextSymbol = z3.mkAnonRealConst()
                        requirements += nextSymbol eq next
                        accum + nextSymbol
                    }

                    requirements += (leftSym gte rightSym - offsetSym) and (leftSym lte rightSym + offsetSym)
                }
                else -> TODO("unknown: ${ctx.text}")
            }
        }

        override fun exitScalarExpr(ctx: ScalarExprContext) = z3 {

            val transcoded = when {

                ctx.literal() != null || ctx.variable() != null -> null

                ctx.callsDynamicVariableAccess() -> {
                    val index = exprs.pop()
                    vars(index)
                }

                ctx.negate() != null -> -exprs.pop()

                (ctx[0] as? TerminalNode)?.symbol?.type == BabelLexer.OPEN_PAREN -> null

                ctx.unaryFunction() != null -> {
                    val arg = exprs.pop()
                    val operatorText = ctx[0].text

                    when(operatorText) {
                        "sgn" -> {
                            requirements += listOf(
                                    arg eq 0 implies (sgn(arg) eq 0),
                                    arg gt 0 implies (sgn(arg) eq 1),
                                    arg lt 0 implies (sgn(arg) eq -1)
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
                            requirements += arg eq pow(10, logged)
                            logged
                        }
                        "ln" -> {
                            val lawned = z3.mkAnonRealConst()
                            requirements += arg eq pow(E, lawned)
                            lawned
                        }
                        "floor" -> {
//                            floor(arg)
                            TODO()
                        }
                        "abs" -> {
                            requirements += arg lt 0 implies (abs(arg) eq -1 * arg)
                            requirements += arg gte 0 implies (abs(arg) eq arg)

                            abs(arg)
                        }
                        "sin" -> {
                            val sinned = z3.mkAnonRealConst()

                            //using an expansion of sin(x): http://math2.org/math/algebra/functions/sincos/expansions.htm
                            val i3Fac = z3.mkReal(1, /*3!*/ 6)
                            val i5Fac = z3.mkReal(1, /*5!*/ 120)
                            val i7Fac = z3.mkReal(1, 5040)
                            val i9Fac = z3.mkReal(1, 362880)
                            val i11Fac = z3.mkReal(1, 39916800)
                            //this only gets us a handful of sig-figs. 

                            requirements += sinned eq (
                                            arg
                                            - (i3Fac * pow(arg, 3))
                                            + (i5Fac * pow(arg, 5))
                                            - (i7Fac * pow(arg, 7))
                                            + (i9Fac * pow(arg, 9))
                                            - (i11Fac * pow(arg, 11))
//                                            + 13
                                    ) 

                            sinned
                        }
                        else -> TODO("not implemented: $operatorText")
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
                        is RaiseContext -> pow(left, right)

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
                                    (k gt 0) implies (mod(X, k) lt k),
                                    (k lt 0) implies (mod(X, k) lt -k),
                                    k * quot(X, k) + mod(X, k) eq X
                            )

                            mod(left, right)
                        }
                        else -> TODO()
                    }
                }
                else -> TODO("op for ${ctx.text}")
            }

            appendInstruction(transcoded)
        }

        private fun appendInstruction(transcoded: Expr?) {
            when (transcoded) {
                null -> {
                }
                is ArithExpr -> exprs.push(transcoded)
                is BoolExpr -> requirements += transcoded
                else -> TODO()
            }
        }

        override fun exitVariable(ctx: VariableContext) {
            exprs.push(inputExprs(ctx.text))
        }

        override fun exitLiteral(ctx: LiteralContext) = z3{
            exprs.push(when {
                ctx.FLOAT() != null -> z3.mkReal(ctx.FLOAT().text)
                ctx.INTEGER() != null -> z3.mkReal(ctx.INTEGER().text)
                ctx.CONSTANT() != null -> when(ctx.text.toLowerCase()){
                    "pi" -> PI
                    "e" -> E
                    else -> TODO()
                }
                else -> TODO()
            })
        }

    }


    fun <R> lazyZ3(initializer: ContextConfigurator.() -> R) = lazy { z3.configureReals(initializer) }
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
