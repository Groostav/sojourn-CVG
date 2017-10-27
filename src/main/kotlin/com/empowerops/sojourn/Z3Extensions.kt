package com.empowerops.sojourn

import com.microsoft.z3.*
import javafx.beans.binding.BooleanExpression

inline fun <R> Context.configure(mutator: ContextConfigurator.() -> R): R = ContextConfigurator(this).mutator()

class ContextConfigurator(val z3: Context) {

    //consts
    val E: ArithExpr get() = TODO("fish e constant out of Native.rcfMkPi()")
    val PI: ArithExpr get() = TODO("fish e constant out of Native.rcfMkPi()")

    //arith-expr
    infix fun ArithExpr.gt(right: ArithExpr): BoolExpr = z3.mkGt(this, right)
    infix fun ArithExpr.gte(right: ArithExpr): BoolExpr = z3.mkGe(this, right)
    infix fun ArithExpr.lt(right: ArithExpr): BoolExpr = z3.mkLt(this, right)
    infix fun ArithExpr.lte(right: ArithExpr): BoolExpr = z3.mkLe(this, right)
    operator fun ArithExpr.unaryMinus(): ArithExpr = z3.mkUnaryMinus(this)

    infix fun BoolExpr.implies(right: BoolExpr): BoolExpr = z3.mkImplies(this, right)
    operator fun BoolExpr.not() = z3.mkNot(this)

    operator fun ArithExpr.times(right: ArithExpr): ArithExpr = z3.mkMul(this, right)
    operator fun ArithExpr.div(right: ArithExpr): ArithExpr = z3.mkDiv(this, right)
    operator fun ArithExpr.plus(right: ArithExpr): ArithExpr = z3.mkAdd(this, right)
    operator fun ArithExpr.minus(right: ArithExpr): ArithExpr = z3.mkSub(this, right)
    //note kotlin will use left-associativity here.
    infix fun ArithExpr.pow(right: ArithExpr): ArithExpr = z3.mkPower(this, right)

    //expr
    infix fun Expr.eq(right: Expr): BoolExpr = z3.mkEq(this, right)
    infix fun Expr.neq(right: Expr): BoolExpr = ! z3.mkEq(this, right)

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

    val realSort: Sort = z3.realSort

    //SOLVER
    fun Solver(): Solver = z3.mkSolver()
    fun Solver(tactic: Tactic): Solver = z3.mkSolver(tactic)
    operator fun Solver.plusAssign(expr: BoolExpr): Unit = add(expr)

    //TACTIC
    fun Tactic(name: String): Tactic = z3.mkTactic(name) //TBD: generated sealed/enum-class?

    //FUNCTION
    fun Function(name: String, vararg paramTypes: Sort, returnType: Sort): FuncDecl = z3.mkFuncDecl(name, paramTypes, returnType)
    
//    inline fun <reified P1, reified P2, reified R> Function(name: String)
//        where P1: Sortish, P2: Sortish, R: Sortish {
//        TODO()
//    }

    fun Implies(cause: BoolExpr, result: BoolExpr): BoolExpr = z3.mkImplies(cause, result)

    //misc
    fun Double.asZ3Real(): ArithExpr = z3.mkReal(this.toString())

    //TODO: `in` via contains?

    //without a wrapper that embeds more type information theres not much we can do here.
    inline operator fun <reified T: Expr> FuncDecl.invoke(arg1: Expr, arg2: Expr): T = this.apply(arg1, arg2) as T

}

interface Sortish
object Real: Sortish{                 
    fun makeSortIn(z3: Context): Sort = z3.realSort
}
