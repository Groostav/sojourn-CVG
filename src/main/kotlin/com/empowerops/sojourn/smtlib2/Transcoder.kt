package com.empowerops.sojourn.smtlib2

import com.empowerops.babel.BabelParser
import com.empowerops.sojourn.InputVariable


typealias SMTLIB2LispDocument = String

//the p118 document transcoded:
/*
; vars
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(declare-fun x7 () Real)
(declare-fun x8 () Real)
(declare-fun x9 () Real)
(declare-fun x10 () Real)
(declare-fun x11 () Real)
(declare-fun x12 () Real)
(declare-fun x13 () Real)
(declare-fun x14 () Real)
(declare-fun x15 () Real)

; trivial bounds
(assert (> x1 0.0))
(assert (< x1 21.0))
(assert (> x2 0.0))
(assert (< x2 57.0))
(assert (> x3 0.0))
(assert (< x3 16.0))
(assert (> x4 0.0))
(assert (< x4 90.0))
(assert (> x5 0.0))
(assert (< x5 120.0))
(assert (> x6 0.0))
(assert (< x6 60.0))
(assert (> x7 0.0))
(assert (< x7 90.0))
(assert (> x8 0.0))
(assert (< x8 120.0))
(assert (> x9 0.0))
(assert (< x9 60.0))
(assert (> x10 0.0))
(assert (< x10 90.0))
(assert (> x11 0.0))
(assert (< x11 120.0))
(assert (> x12 0.0))
(assert (< x12 60.0))
(assert (> x13 0.0))
(assert (< x13 90.0))
(assert (> x14 0.0))
(assert (< x14 120.0))
(assert (> x15 0.0))
(assert (< x15 60.0))

; babel constraints
(assert (> 0.0 (- (+ (- x4) x1) 7.0)))
(assert (> 0.0 (- (- x4 x1) 6.0)))
(assert (> 0.0 (- (+ (- x5) x2) 7.0)))
(assert (> 0.0 (- (- x5 x2) 7.0)))
(assert (> 0.0 (- (+ (- x6) x3) 7.0)))
(assert (> 0.0 (- (- x6 x3) 6.0)))
(assert (> 0.0 (- (+ (- x7) x4) 7.0)))
(assert (> 0.0 (- (- x7 x4) 6.0)))
(assert (> 0.0 (- (+ (- x8) x5) 7.0)))
(assert (> 0.0 (- (- x8 x5) 7.0)))
(assert (> 0.0 (- (+ (- x9) x6) 7.0)))
(assert (> 0.0 (- (- x9 x6) 6.0)))
(assert (> 0.0 (- (+ (- x10) x7) 7.0)))
(assert (> 0.0 (- (- x10 x7) 6.0)))
(assert (> 0.0 (- (+ (- x11) x8) 7.0)))
(assert (> 0.0 (- (- x11 x8) 7.0)))
(assert (> 0.0 (- (+ (- x12) x9) 7.0)))
(assert (> 0.0 (- (- x12 x9) 6.0)))
(assert (> 0.0 (- (+ (- x13) x10) 7.0)))
(assert (> 0.0 (- (- x13 x10) 6.0)))
(assert (> 0.0 (- (+ (- x14) x11) 7.0)))
(assert (> 0.0 (- (- x14 x11) 7.0)))
(assert (> 0.0 (- (+ (- x15) x12) 7.0)))
(assert (> 0.0 (- (- x15 x12) 6.0)))
(assert (let ((a!1 (+ (- (- (- x1) x2) x3) 60.0)))
  (> 0.0 a!1)))
(assert (let ((a!1 (+ (- (- (- x4) x5) x6) 50.0)))
  (> 0.0 a!1)))
(assert (let ((a!1 (+ (- (- (- x7) x8) x9) 70.0)))
  (> 0.0 a!1)))
(assert (let ((a!1 (+ (- (- (- x10) x11) x12) 85.0)))
  (> 0.0 a!1)))
(assert (let ((a!1 (+ (- (- (- x13) x14) x15) 100.0)))
  (> 0.0 a!1)))

; helpers -- for the sgn() function, etc.


; ?? -- OK so rise4fun crashes if you include this. This might be trying to declare something about real value bindings? not sure.
(rmodel->model-converter-wrapper
x7 -> 1.0
x9 -> 1.0
x13 -> 1.0
x8 -> 1.0
x14 -> 1.0
x2 -> 1.0
x10 -> 1.0
x1 -> 1.0
x6 -> 1.0
x3 -> 1.0
x12 -> 1.0
x15 -> 1.0
x4 -> 1.0
x5 -> 1.0
x11 -> 1.0
)

;; ask for output
(check-sat)
(get-model)
 */

data class Var(val name: String)
data class TrivialBound(val lowerBound: Double, val upperBound: Double, val stepSize: Double)
data class ConstraintExpression(val expr: BabelParser.ScalarExprContext)

fun babelToSMBLIB2TranscodingWalker(inputs: List<InputVariable>, expr: BabelParser.ExpressionContext): SMTLIB2LispDocument {
    TODO()
}