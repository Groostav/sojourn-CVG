package com.empowerops.babel

import kotlinx.collections.immutable.ImmutableList
import org.chocosolver.solver.Model
import org.chocosolver.solver.Solver
import org.chocosolver.solver.constraints.real.RealConstraint

class ChocoIbexSolvingPool: ConstraintSolvingPool {

    override fun makeNewPointGeneration(pointCount: Int): ImmutableList<InputVector> {

        TODO()
    }

    class Factory: ConstraintSolvingPoolFactory {
        override fun create(
                inputSpec: List<InputVariable>,
                constraints: List<BabelExpression>
        ): ConstraintSolvingPool {

            val aliases = inputSpec
                    .mapIndexed { idx, v -> v to idx }
                    .toMap()
                    .mapValues { "{${it.value}}" }

            val expressions = constraints
                    .map { it.expressionLiteral }
                    //TODO: this should be done by a visitor to find context-sensitive usages.
                    //but thats hard work, and im lazy.
                    .map { aliases.toList().fold(it){ expr, alias -> expr.replace(alias.first.name, alias.second) } }

            val model = Model()

            val vars = inputSpec.map { input ->
                val precision = input.run { upperBound - lowerBound } / 1_000.0
                model.realVar(input.name, input.lowerBound, input.upperBound, precision)
            }

            val ex = expressions.joinToString(";")

            model.realIbexGenericConstraint(ex, *vars.toTypedArray())

            val solver = model.solver

            val satisfied = solver.solve()

            val x = 3;

            TODO()
        }
    }
}
