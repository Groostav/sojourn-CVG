package com.empowerops.sojourn

import com.microsoft.z3.*

inline fun <R> Context.configure(mutator: ContextConfigurator.() -> R): R = ContextConfigurator(this).mutator()

class ContextConfigurator(val z3: Context) {

    val E: ArithExpr get() = TODO("fish e constant out of Native.rcfMkPi()")
    val PI: ArithExpr get() = TODO("fish e constant out of Native.rcfMkPi()")

    infix fun ArithExpr.gt(right: ArithExpr): BoolExpr = z3.mkGt(this, right)
    infix fun ArithExpr.gte(right: ArithExpr): BoolExpr = z3.mkGe(this, right)
    infix fun ArithExpr.lt(right: ArithExpr): BoolExpr = z3.mkLt(this, right)
    infix fun ArithExpr.lte(right: ArithExpr): BoolExpr = z3.mkLe(this, right)

    operator fun BoolExpr.not() = z3.mkNot(this)

    operator fun ArithExpr.times(right: ArithExpr): ArithExpr = z3.mkMul(this, right)
    operator fun ArithExpr.div(right: ArithExpr): ArithExpr = z3.mkDiv(this, right)
    operator fun ArithExpr.plus(right: ArithExpr): ArithExpr = z3.mkAdd(this, right)
    operator fun ArithExpr.minus(right: ArithExpr): ArithExpr = z3.mkSub(this, right)
    operator fun ArithExpr.rem(right: ArithExpr): ArithExpr = TODO("TBD: https://github.com/Z3Prover/z3/issues/557, stick to C-style remainder semantics?")
    //note kotlin will use left-associativity here.
    infix fun ArithExpr.pow(right: ArithExpr): ArithExpr = z3.mkPower(this, right)

    //expr
    infix fun Expr.eq(right: Expr): BoolExpr = z3.mkEq(this, right)

    //CONSTS
    fun Real(name: String) = z3.mkRealConst(name)
    fun Real(name: Symbol) = z3.mkRealConst(name)
    fun Int(name: String) = z3.mkIntConst(name)
    fun Int(name: Symbol) = z3.mkIntConst(name)

    //vals
    val Int.z get() = z3.mkInt(this)

    //SOLVER
    fun Solver(tactic: Tactic): Solver = z3.mkSolver(tactic)
    operator fun Solver.plusAssign(expr: BoolExpr): Unit = add(expr)

    //TACTIC
    fun Tactic(name: String): Tactic = z3.mkTactic(name) //TBD: generated sealed/enum-class?

    //misc
    fun Double.asZ3Real(): ArithExpr = z3.mkReal(this.toString())


    //TODO: `in` via contains?
    

}
