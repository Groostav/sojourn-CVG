package com.empowerops.babel;

import com.empowerops.linqalike.LinqingSet;
import com.empowerops.linqalike.Queryable;
import com.empowerops.babel.todo_deleteme.BabelParserBaseListener;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ErrorNode;

public class SyntaxErrorFindingWalker extends BabelParserBaseListener {

    private final LinqingSet<BabelExpressionProblem> problems = new LinqingSet<>();

    @Override
    public void visitErrorNode(@NotNull ErrorNode node) {
        problems.add(new BabelExpressionProblem("syntax error", node));
    }

    public Queryable<BabelExpressionProblem> getErrors() {
        return problems;
    }
}
