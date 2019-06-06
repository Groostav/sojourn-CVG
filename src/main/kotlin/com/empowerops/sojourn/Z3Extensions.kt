package com.empowerops.sojourn

import com.microsoft.z3.*
import javafx.beans.binding.BooleanExpression
import java.math.BigDecimal

inline fun <R> Context.configureReals(mutator: ContextConfigurator.() -> R): R = ContextConfigurator(this).mutator()
inline fun <R> Context.configure(mutator: ContextConfigurator.() -> R): R = ContextConfigurator(this).mutator()
inline operator fun <R> Context.invoke(mutator: ContextConfigurator.() -> R): R = ContextConfigurator(this).mutator()

class ContextConfigurator(val z3: Context){

    infix fun ArithExpr.gt(right: Int): BoolExpr = z3.mkGt(this, right.zr)
    infix fun ArithExpr.gte(right: Int): BoolExpr = z3.mkGe(this, right.zr)
    infix fun ArithExpr.lt(right: Int): BoolExpr = z3.mkLt(this, right.zr)
    infix fun ArithExpr.lte(right: Int): BoolExpr = z3.mkLe(this, right.zr)

    operator fun ArithExpr.times(right: Int): ArithExpr = z3.mkMul(this, right.zr)
    operator fun ArithExpr.div(right: Int): ArithExpr = z3.mkDiv(this, right.zr)
    operator fun ArithExpr.plus(right: Int): ArithExpr = z3.mkAdd(this, right.zr)
    operator fun ArithExpr.plus(right: Double): ArithExpr = z3.mkAdd(this, right.zr)
    operator fun ArithExpr.minus(right: Int): ArithExpr = z3.mkSub(this, right.zr)
    operator fun ArithExpr.minus(right: Double): ArithExpr = z3.mkSub(this, right.zr)
    fun pow(left: ArithExpr, right: Int) = z3.mkPower(left, right.zr)

    infix fun Int.gt(right: ArithExpr): BoolExpr = z3.mkGt(this.zr, right)
    infix fun Int.gte(right: ArithExpr): BoolExpr = z3.mkGe(this.zr, right)
    infix fun Int.lt(right: ArithExpr): BoolExpr = z3.mkLt(this.zr, right)
    infix fun Int.lte(right: ArithExpr): BoolExpr = z3.mkLe(this.zr, right)

    operator fun Int.times(right: ArithExpr): ArithExpr = z3.mkMul(this.zr, right)
    operator fun Int.div(right: ArithExpr): ArithExpr = z3.mkDiv(this.zr, right)
    operator fun Int.plus(right: ArithExpr): ArithExpr = z3.mkAdd(this.zr, right)
    operator fun Int.minus(right: ArithExpr): ArithExpr = z3.mkSub(this.zr, right)
    fun pow(left: Int, right: ArithExpr): ArithExpr = z3.mkPower(left.zr, right)
    //note kotlin will use left-associativity here.

    infix fun ArithExpr.eq(right: Int): BoolExpr = z3.mkEq(this, right.zr)
    infix fun ArithExpr.neq(right: Int): BoolExpr = ! z3.mkEq(this, right.zr)
    infix fun Int.eq(right: ArithExpr): BoolExpr = z3.mkEq(this.zr, right)
    infix fun Int.neq(right: ArithExpr): BoolExpr = ! z3.mkEq(this.zr, right)

    //consts
    //TODO pending https://github.com/Z3Prover/z3/issues/1327
    // current strategy is just to use a high resolution constant a le floating point.
    val E: RealExpr = BigDecimal("2.7182818284590452353").zr
    val PI: RealExpr = BigDecimal("3.1415926535897932384").zr

    //arith-expr
    infix fun ArithExpr.gt(right: ArithExpr): BoolExpr = z3.mkGt(this, right)
    infix fun ArithExpr.gte(right: ArithExpr): BoolExpr = z3.mkGe(this, right)
    infix fun ArithExpr.lt(right: ArithExpr): BoolExpr = z3.mkLt(this, right)
    infix fun ArithExpr.lte(right: ArithExpr): BoolExpr = z3.mkLe(this, right)
    operator fun ArithExpr.unaryMinus(): ArithExpr = z3.mkUnaryMinus(this)

    infix fun BoolExpr.implies(right: BoolExpr): BoolExpr = z3.mkImplies(this, right)
    operator fun BoolExpr.not() = z3.mkNot(this)
    infix fun BoolExpr.and(right: BoolExpr): BoolExpr = z3.mkAnd(this, right)
    infix fun BoolExpr.or(right: BoolExpr): BoolExpr = z3.mkOr(this, right)

    operator fun ArithExpr.times(right: ArithExpr): ArithExpr = z3.mkMul(this, right)
    operator fun ArithExpr.div(right: ArithExpr): ArithExpr = z3.mkDiv(this, right)
    operator fun ArithExpr.plus(right: ArithExpr): ArithExpr = z3.mkAdd(this, right)
    operator fun ArithExpr.minus(right: ArithExpr): ArithExpr = z3.mkSub(this, right)
    fun pow(left: ArithExpr, right: ArithExpr): ArithExpr = z3.mkPower(left, right)

    //type coercion
    fun RealExpr.isInt2(): BoolExpr = z3.mkIsInteger(this)

    //expr
    infix fun ArithExpr.eq(right: ArithExpr): BoolExpr = z3.mkEq(this, right)
    infix fun BoolExpr.eq(right: BoolExpr): BoolExpr = z3.mkEq(this, right)
    infix fun ArithExpr.neq(right: ArithExpr): BoolExpr = ! z3.mkEq(this, right)
    infix fun BoolExpr.neq(right: BoolExpr): BoolExpr = ! z3.mkEq(this, right)

    //CONSTS
    fun Real(name: String) = z3.mkRealConst(name)
    fun Real(name: Symbol) = z3.mkRealConst(name)
    fun Reals(spaceSeparatedNames: String): List<RealExpr> = spaceSeparatedNames.split(' ').map { Real(it) }
    fun Reals(vararg names: String): List<RealExpr> = names.map { Real(it) }
    fun Int(name: String) = z3.mkIntConst(name)
    fun Int(name: Symbol) = z3.mkIntConst(name)

    //vals
    val Int.z get() = z3.mkInt(this)
    val Int.zr get() = z3.mkReal(this)
    val Double.zr get() = z3.mkReal(this.toString())
    val BigDecimal.zr get() = z3.mkReal(this.toString())

    val realSort: Sort = z3.realSort

    //SOLVER
    fun Solver(): Solver = z3.mkSolver()
    fun Solver(tactic: Tactic): Solver = z3.mkSolver(tactic)
    operator fun Solver.plusAssign(expr: BoolExpr): Unit = add(expr)
    operator fun Solver.plusAssign(exprs: List<BoolExpr>): Unit = exprs.forEach { add(it) }

    //TACTIC
    fun Tactic(name: String): Tactic = z3.mkTactic(name) //TBD: generated sealed/enum-class?

    //FUNCTION
    fun Function(name: String, vararg paramTypes: Sort, returnType: Sort): FuncDecl = z3.mkFuncDecl(name, paramTypes, returnType)
    fun <P1, R> UnaryFunction(name: String, paramType: Sortish<P1>, returnType: Sortish<R>): UnaryFunction<P1, R> where P1: Expr, R: Expr
            = UnaryFunction<P1, R>(z3.mkFuncDecl(name, paramType.makeSortIn(z3), returnType.makeSortIn(z3)))

    fun <P1, P2, R> BinaryFunction(name: String, leftParamType: Sortish<P1>, rightParamType: Sortish<P2>, returnType: Sortish<R>): BinaryFunction<P1, P2, R> where P1: Expr, P2: Expr, R: Expr
            = BinaryFunction<P1, P2, R>(z3.mkFuncDecl(name, arrayOf(leftParamType.makeSortIn(z3), rightParamType.makeSortIn(z3)), returnType.makeSortIn(z3)))

    fun Implies(cause: BoolExpr, result: BoolExpr): BoolExpr = z3.mkImplies(cause, result)

    //misc
    fun Double.asZ3Real(): ArithExpr = z3.mkReal(this.toString())

    //TODO: `in` via contains?

}

//without a wrapper that embeds more type information theres not much we can do here.
inline operator fun <reified T: Expr> FuncDecl.invoke(arg1: Expr, arg2: Expr): T = this.apply(arg1, arg2) as T
inline operator fun <reified T: Expr> FuncDecl.invoke(arg1: Expr): T = this.apply(arg1) as T

class UnaryFunction<in P1, out R>(val decl: FuncDecl) where P1: Expr, R: Expr {
    operator fun invoke(param: P1): R = decl.apply(param) as R
}
class BinaryFunction<in P1, in P2, out R>(val decl: FuncDecl) where P1: Expr, P2: Expr, R: Expr {
    operator fun invoke(leftParam: P1, rightParam: P2): R = decl.apply(leftParam, rightParam) as R
}

interface Sortish<out T: Expr> { fun makeSortIn(z3: Context): Sort }

object Arith: Sortish<ArithExpr> {
    override fun makeSortIn(z3: Context): Sort = z3.realSort
}
object Real: Sortish<RealExpr> {
    override fun makeSortIn(z3: Context): Sort = z3.realSort
}
object Integer: Sortish<IntExpr> {
    override fun makeSortIn(z3: Context): Sort = z3.intSort
}
