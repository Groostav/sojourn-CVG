package com.empowerops.sojourn

import com.empowerops.babel.*
import com.empowerops.babel.BabelParser.*
import com.microsoft.z3.*
import kotlinx.collections.immutable.*
import org.antlr.v4.runtime.RuleContext
import org.antlr.v4.runtime.tree.ParseTree
import org.antlr.v4.runtime.tree.TerminalNode
import java.lang.NullPointerException
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
    val sgn: UnaryFunction<ArithExpr, RealExpr> by lazyZ3 { UnaryFunction("sgn", Arith, Real) }
    val abs: UnaryFunction<ArithExpr, RealExpr> by lazyZ3 { UnaryFunction("abs", Arith, Real) }

    val mod: BinaryFunction<ArithExpr, ArithExpr, RealExpr> by lazyZ3 { BinaryFunction("mod", Arith, Arith, Real) }
    val quot: BinaryFunction<ArithExpr, ArithExpr, IntExpr> by lazyZ3 { BinaryFunction("quot", Arith, Arith, Integer) }

    fun mkModAxioms(X: ArithExpr, k: ArithExpr) = z3 {
        solver.add(
                (k neq 0) implies (0 lte mod(X, k)),
                (k gt 0) implies (mod(X, k) lt k),
                (k lt 0) implies (mod(X, k) lt -k),
                (k * quot(X, k) + mod(X, k)) eq X
        )
    }

    val vars: UnaryFunction<RealExpr, RealExpr> by lazyZ3 {
        UnaryFunction("var", Real, Real).also {
            for((index, input) in inputs.withIndex()){
                solver += it((index + 1).zr) eq inputExprs.getValue(input.name)
            }
        }
    }

    override fun toString(): String {
        return "SOLVER:\n$solver\nMODEL:${try { solver.model } catch(ex: Z3Exception) { null }}"
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

            transcoder.requirements.forEach { solver += it }

            val newSatState = solver.check()

            if(newSatState != Status.SATISFIABLE){
                trace { "constraint expr '${constraint.expressionLiteral}' made constraint set $newSatState\n solver is:\n$solver" }
                //we could simply drop this and do a guess-and-check
            }
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

//        if ( ! constraints.passFor(seed)) {
            //this is likely from a rounding error, we're gonna have to think of something smarter at some point.
//            return immutableListOf()
//            val x = 4;
//        }
        
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

//                if ( ! constraints.passFor(nextResult)) {
//                    TODO("again, probably rounding error. Not sure what to do.")
//                    break
//                }

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
                        //TODO: this is a hack to hedge against for rounding error
                        ctx.gteq() != null -> left gt right
                        ctx.lteq() != null -> left lt right

                        else -> TODO("unknown: ${ctx.text}")
                    }
                }
                ctx.eq() != null -> {
                    val (offset, right, left) = exprs.pop(3)

                    val (offsetSym, rightSym, leftSym) = listOf(offset, right, left).map {
                        val nextSymbol = z3.mkAnonRealConst()
                        requirements += nextSymbol eq it
                        nextSymbol
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
                    val index = exprs.pop() as RealExpr
                    vars(index)
                }

                ctx.negate() != null -> -exprs.pop()

                (ctx[0] as? TerminalNode)?.symbol?.type == BabelLexer.OPEN_PAREN -> null

                ctx.unaryFunction() != null -> {
                    val arg = exprs.pop() as RealExpr
                    val operatorText = ctx[0].text

                    val result: ArithExpr = when(operatorText) {
                        "sgn" -> {
                            requirements += listOf(
                                    arg eq 0 implies (sgn(arg) eq 0),
                                    arg gt 0 implies (sgn(arg) eq 1),
                                    arg lt 0 implies (sgn(arg) eq -1)
                            )

                            sgn(arg)
                        }
                        "sqrt" -> {
                            val rooted = z3.mkAnonRealConst(operatorText)
                            requirements += rooted gt 0
                            requirements += arg eq rooted * rooted
                            rooted
                        }
                        "cbrt" -> {
                            val tripleRooted = z3.mkAnonRealConst(operatorText)
                            requirements += arg eq tripleRooted * tripleRooted * tripleRooted
                            tripleRooted
                        }
                    //do a tree-match on expr ^ (1/exprB), then do a `mkMul(*exprB.toArray())`?
                        "log" -> {
                            val logged = z3.mkAnonRealConst(operatorText)
                            requirements += arg eq pow(10, logged)
                            logged
                        }
                        "ln" -> {
                            val lawned = z3.mkAnonRealConst(operatorText)
                            requirements += arg eq pow(E, lawned)
                            lawned
                        }
                        "floor" -> {
                            val floored = z3.mkAnonIntConst(operatorText)
                            val rem = z3.mkAnonRealConst("floor_rem")
                            requirements += listOf(
                                    floored + rem eq arg,
                                    rem gte 0,
                                    rem lt 1
                            )

                            floored
                        }
                        "ceil" -> {
                            val ceiled = z3.mkAnonIntConst(operatorText)
                            val rem = z3.mkAnonRealConst("ceil_rem")
                            requirements += listOf(
                                    ceiled - rem eq arg,
                                    rem gte 0,
                                    rem lt 1
                            )

                            ceiled
                        }
                        "abs" -> {
                            requirements += arg lt 0 implies (abs(arg) eq -1 * arg)
                            requirements += arg gte 0 implies (abs(arg) eq arg)

                            abs(arg)
                        }
                        "sin" -> {
                            val sinned = z3.mkAnonRealConst(operatorText)

                            //using an expansion of sin(x): http://math2.org/math/algebra/functions/sincos/expansions.htm
                            val i3Fac = z3.mkReal(1, /*3!*/ 6)
                            val i5Fac = z3.mkReal(1, /*5!*/ 120)
                            val i7Fac = z3.mkReal(1, 5040)
                            val i9Fac = z3.mkReal(1, 362880)
                            val i11Fac = z3.mkReal(1, 39916800)

                            fail; //blargwargl, I cannot for the life of me get this
                            // 1. to use a sin function, though this might have been a name collision
                            // 2. to use and "see-through" a 'mod(arg, 2PI)' call. It simply goes UNKNOWN with no solution. bummer.

//                            val modded = z3.mkAnonRealConst("mod-sin")
//                            val leftParam = arg + PI
//                            val rightParam = 2 * PI
//                            mkModAxioms(leftParam, rightParam)
//                            val modded = mod(leftParam, rightParam) - PI
//                            requirements += listOf(
//                                    (arg gt PI) implies (modded eq (mod(leftParam, rightParam) - PI)),
//                                    (arg lte PI) implies (modded eq arg)
//                            )
//                            val modded = arg + (2*PI)
//                            requirements += (modded eq (arg + 2*PI))
                            val modded = arg
//
//                            requirements += listOf(
//                                    modded lt PI
//                                    modded gt -PI
//                            )

//                            requirements += sinned eq (
//                                    modded
//                                    - (i3Fac * modded * modded * modded)
//                                    + (i5Fac * pow(modded, 5))
//                                    - (i7Fac * pow(modded, 7))
//                                    + (i9Fac * pow(modded, 9))
//                                    - (i11Fac * pow(modded, 11))
//                            )

                            requirements += ((modded lte PI) and (modded gte -PI)) implies (sinned eq (
                                    modded
                                    - (i3Fac * pow(modded, 3))
                                    + (i5Fac * pow(modded, 5))
                                    - (i7Fac * pow(modded, 7))
                                    + (i9Fac * pow(modded, 9))
                                    - (i11Fac * pow(modded, 11))
                            ))
                            requirements += (modded gt PI) implies (sinned eq (
                                    (modded - 2*PI)
                                    - (i3Fac * pow(modded - 2*PI, 3))
                                    + (i5Fac * pow(modded - 2*PI, 5))
                                    - (i7Fac * pow(modded - 2*PI, 7))
                                    + (i9Fac * pow(modded - 2*PI, 9))
                                    - (i11Fac * pow(modded - 2*PI, 11))
                            ))
                            //I cant seem to get mod working

                            sinned
                        }
                        else -> TODO("not implemented: $operatorText")
                    }

                    result
                }
                ctx.callsBinaryOp() -> {
                    val right = exprs.pop() as RealExpr
                    val left = exprs.pop() as RealExpr

                    when(ctx[1]) {
                        is PlusContext -> left + right
                        is MinusContext -> left - right
                        is MultContext -> left * right
                        is DivContext -> left / right
                        is RaiseContext -> pow(left, right)
                        is ModContext -> {
                            mkModAxioms(left, right)
                            mod(left, right)
                        }
                        else -> TODO()
                    }
                }
                else -> TODO("op for ${ctx.text}")
            }

            appendInstruction(transcoded)
        }

        private fun ContextConfigurator.letMod(right: ArithExpr, left: ArithExpr, prefix: String = ""): RealExpr {

            //https://github.com/Z3Prover/z3/issues/557

            val mod = z3.mkAnonRealConst("${prefix}mod")
            val quot = z3.mkAnonIntConst("${prefix}quot")

            val X = left
            val k = right

            requirements += listOf(
                    (k neq 0) implies (0 lte mod),
                    (k gt 0) implies (mod lt k),
                    (k lt 0) implies (mod lt -k),
                    (k neq 0) implies ((k * quot + mod) eq X)
//                    mod gte 0,
//                    mod lt k,
//                    quot neq 0,
//                    quot neq mod,
//                    (k * quot) + mod eq X
            )
            return mod
        }

        private fun appendInstruction(transcoded: Expr?) {
            when (transcoded) {
                null -> { }
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

fun Model.buildInputVector(inputs: List<InputVariable>): InputVector {
    val valuesByName = constDecls
            .map {
                it.name.toString() to getConstInterp(it)
            }
            .filter {
                it.first in inputs.map { it.name }
            }
            .map {
                val interp = it.second
                val decimal = when (interp) {
                    is RatNum -> interp.numerator.bigInteger.toDouble() / interp.denominator.bigInteger.toDouble()
                    is IntNum -> interp.bigInteger.toDouble()
                    else -> TODO("cant decode interp $interp")
                }
                it.first to decimal
            }
            .toMap()

    return InputVector(inputs.associate { it.name to (valuesByName[it.name] ?: Double.NaN) })
}


operator fun RuleContext.get(index: Int): ParseTree = getChild(index)

private inline operator fun <K, V> Map<K, V>.invoke(key: K): V = getValue(key)

private var tempId: Int = 0

private fun Context.mkAnonRealConst(prefix: String = ""): RealExpr = mkRealConst("${if(prefix != "") "$prefix-" else ""}temp-${tempId++}")
private fun Context.mkAnonIntConst(prefix: String = ""): IntExpr = mkIntConst("${if(prefix != "") "$prefix-" else ""}temp-${tempId++}")
