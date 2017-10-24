package com.empowerops.sojourn

import com.microsoft.z3.ArithExpr
import com.microsoft.z3.Context
import org.testng.annotations.Test

class Z3Fixture {

    @Test
    fun `asdf`(){
        val z3 = Context()

        val s = z3.mkSolver(z3.mkTactic("qfnra-nlsat"))
//        z3.mkConst("pi", z3.mkRealSort())             

//        s.add(z3.mkGt(z3.mkCos))
        val sin = z3.mkFuncDecl("sin", z3.realSort, z3.realSort)
        val pi = z3.mkConst("pi", z3.realSort)
        
        val theta = z3.mkConst("theta", z3.realSort)

//        s.add(z3.parseSMTLIB2String(
//                """
//                  |(declare-fun theta () Real)
//                  |(declare-fun offset () Real)
//                  |;(assert (= (cos theta) (/ 1 2)))
//                  |(assert (= (sin (+ offset 2)) pi))
//                  |;(check-sat-using qfnra-nlsat)
//                  |;(get-model)
//                  """.trimMargin(),
//                arrayOf(),
//                arrayOf(),
//                arrayOf(),
//                arrayOf()
//        ))

        s.add(z3.mkGt(sin.apply(theta) as ArithExpr, pi as ArithExpr))

        println(s.check())
        val m = s.model

        println(s)
        println(m)

        val x = 4;
    }
}