package com.empowerops.babel;

import com.empowerops.jargon.model.VariableSymbol;
import com.empowerops.linqalike.LinqingMap;
import com.empowerops.babel.todo_deleteme.BabelParser.*;
import com.empowerops.babel.todo_deleteme.BabelParserBaseListener;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.antlr.v4.runtime.tree.TerminalNodeImpl;

import static com.empowerops.linqalike.Factories.from;
import static com.empowerops.problem_definition.parser.BabelLexer.FLOAT;

/**
 * Created by Justin Casol on 1/19/2015.
 */
public class BooleanRewritingWalker extends BabelParserBaseListener {

    private boolean isBooleanExpression = false;

    public BooleanRewritingWalker() {
    }
    public BooleanRewritingWalker(LinqingMap<VariableSymbol, Double> map) {
        this.variableMap = map;
    }

    public LinqingMap<VariableSymbol, Double> variableMap;

    public static final Double Epsilon = Double.MIN_NORMAL;

    @Override public void exitExpr(@NotNull ExprContext ctx) {
        if (ctx.children == null) { throw new IllegalArgumentException(); }

        ParseTree operation = from(ctx.children).where(this::isOperation).firstOrDefault().orElse(null);
        if (operation instanceof LteqContext) {
            swapInequalityWithSubtraction(ctx, "ASTREWRITE<=");
            isBooleanExpression = true;
        }
        else if (operation instanceof EqContext) {
            swapInequalityWithSubtraction(ctx, "ASTREWRITE=");
            isBooleanExpression = true;
        }
        else if (operation instanceof GteqContext) {
            swapLiteralChildren(ctx);
            swapInequalityWithSubtraction(ctx, "ASTREWRITE>=");
            isBooleanExpression = true;
        }
        else if (operation instanceof LtContext) {
            swapInequalityWithSubtraction(ctx, "ASTREWRITE<");
            addEpsilonAdditionASTLayer(ctx);
            isBooleanExpression = true;
        }
        else if (operation instanceof GtContext) {
            swapLiteralChildren(ctx);
            swapInequalityWithSubtraction(ctx, "ASTREWRITE<");
            addEpsilonAdditionASTLayer(ctx);
            isBooleanExpression = true;
        }
        else {
            isBooleanExpression = false;
        }
    }

    public boolean isBooleanExpression() {
        return isBooleanExpression;
    }

    private void addEpsilonAdditionASTLayer(ExprContext ctx) {
        ParserRuleContext parent = ctx.getParent();
        ExprContext superExpression = new ExprContext(parent, 20);
        parent.children.add(parent.children.indexOf(ctx), superExpression);
        parent.children.remove(ctx);
        superExpression.addChild(ctx);
        ctx.parent = superExpression;

        PlusContext plusContext = new PlusContext(superExpression, 20);
        TerminalNode terminalNode = new TerminalNodeImpl(new CommonToken(20, "ADDFOREPSILON"));
        plusContext.addChild(terminalNode);
        superExpression.addChild(plusContext);

        addValue(superExpression, Epsilon);
    }

    private void addValue(ExprContext superExpression, double value) {
        ExprContext valueExpr = new ExprContext(superExpression, 1);
        LiteralContext valueContext = new LiteralContext(valueExpr, 1);
        TerminalNode valueTerminalNode = new TerminalNodeImpl(new CommonToken(FLOAT, Double.toString(value)));
        superExpression.addChild(valueExpr);
        valueExpr.addChild(valueContext);
        valueContext.addChild(valueTerminalNode);
    }

    private void swapInequalityWithSubtraction(ExprContext ctx, String literalNodeMessage) {
        ctx.children.remove(1);
        MinusContext minusContext = new MinusContext(ctx, 21);
        TerminalNode terminalNode = new TerminalNodeImpl(new CommonToken(FLOAT, literalNodeMessage));
        minusContext.addChild(terminalNode);
        ctx.children.add(1, minusContext);
    }

    private void swapLiteralChildren(ExprContext ctx) {

        ParseTree firstChild = ctx.children.remove(0);
        ParseTree lastChild = ctx.children.remove(1);
        ctx.children.add(0,lastChild);
        ctx.children.add(firstChild);
    }

    @Override public void exitLt(@NotNull LtContext ctx) {
        super.exitLt(ctx);
    }

    private boolean isOperation(ParseTree parseTree) {
        return parseTree.getChildCount() == 1 && (parseTree.getChild(0) instanceof TerminalNode);
    }
}
