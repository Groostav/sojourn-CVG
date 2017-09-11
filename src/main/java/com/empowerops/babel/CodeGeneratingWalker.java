package com.empowerops.babel;

import com.empowerops.common.ExceptionUtilities;
import com.empowerops.linqalike.Factories;
import com.empowerops.linqalike.Queryable;
import com.empowerops.problem_definition.babel.RunningBabelCodeMap.*;
import com.empowerops.babel.todo_deleteme.BabelParser.*;
import com.empowerops.babel.todo_deleteme.BabelParserBaseListener;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;

import javax.annotation.Nonnull;

import static com.empowerops.linqalike.CommonDelegates.Not;
import static com.empowerops.problem_definition.babel.RuntimeNumerics.*;

/**
 * Created by Justin Casol on 1/7/2015.
 */
public class CodeGeneratingWalker extends BabelParserBaseListener {

    private static final int IndexStartsFromOne = 1;
    private ContextFreeNumericExecutable rootExecutor;

    private final SymbolTable         symbolTable;
    private final RunningBabelCodeMap codeMap;
    private final RuntimeNumerics operations = new RuntimeNumerics();

    public CodeGeneratingWalker(SymbolTable symbolTable) {
        this.codeMap = new RunningBabelCodeMap();
        this.symbolTable = symbolTable;
    }

    @Override public void exitExpression(@Nonnull ExpressionContext ctx) {
        TerminalNode last = (TerminalNode) TreeHelper.childrenOf(ctx).last();
        assert TreeHelper.childrenOf(ctx).size() == 2 && last.getSymbol().getType() == Token.EOF;
        rootExecutor = codeMap.contextFreeNumericExecutable(TreeHelper.childrenOf(ctx).first());
    }

    @Override public void exitExpr(@Nonnull ExprContext ctx) {

        codeMap.putExecutable(ctx, () -> {

            ParseTree operationNode = findOperation(TreeHelper.childrenOf(ctx));
            Queryable<ParseTree> argumentNodes = TreeHelper.childrenOf(ctx)
                    .where(Not(node -> node instanceof TerminalNode))
                    .except(operationNode);

            // all boolean expressions expressed as numeric ones, with +ve being false and -ve (or 0) being true.
            NumericOperation operation = codeMap.numericOperation(operationNode);
            Queryable<ContextFreeExecutable> arguments = argumentNodes.select(codeMap::contextFreeExecutable).immediately();

            return operation.execute(arguments);
        });
    }

    private ParseTree findOperation(Queryable<ParseTree> children) {
            return children.firstOrDefault(child -> ! (child instanceof TerminalNode || child instanceof ExprContext))
                    .orElse(children.first(child -> ! (child instanceof TerminalNode)));
    }

    @Override public void exitLambdaExpr(@Nonnull LambdaExprContext ctx) {
        ExprContext executingNode = TreeHelper.childrenOf(ctx).ofType(ExprContext.class).single();
        codeMap.putExecutable(ctx, () -> codeMap.contextFreeNumericExecutable(executingNode).execute());
    }

    @Override public void exitPlus(@Nonnull PlusContext ctx) { codeMap.putExecutable(ctx, Addition); }
    @Override public void exitMinus(@Nonnull MinusContext ctx) { codeMap.putExecutable(ctx, Subtraction); }
    @Override public void exitMult(@Nonnull MultContext ctx) { codeMap.putExecutable(ctx, Multiplication); }
    @Override public void exitDiv(@Nonnull DivContext ctx) { codeMap.putExecutable(ctx, Division); }
    @Override public void exitMod(@Nonnull ModContext ctx) { codeMap.putExecutable(ctx, Modulo); }

    /***
     * Left associative. After discussion and thought, If there is something complex in an exponent, it should be
     * surrounded by brackets. IfnS we wish this to change,
     * we will have to exclude this from the expr visit, and change the grammar
     * for exponent to be expr ( ^ expr)*
     */
    @Override public void exitExponent(@Nonnull ExponentContext ctx) { codeMap.putExecutable(ctx, Exponentiation); }

    @Override public void exitBinaryFunction(@Nonnull BinaryFunctionContext ctx) {
        String function = ctx.getText();
        codeMap.putExecutable(ctx, operations.findBinaryFunctionNamed(function));
    }

    @Override public void exitUnaryFunction(@Nonnull UnaryFunctionContext ctx) {
        String function = ctx.getText();
        codeMap.putExecutable(ctx, operations.findUnaryFunctionNamed(function));
    }

    @Override public void exitDynamicVariableAccess(@Nonnull DynamicVariableAccessContext ctx) {
        codeMap.putExecutable(ctx, (int index) -> symbolTable.getSymbolForIndex(index - IndexStartsFromOne));
    }

    @Override public void exitNegate(@Nonnull NegateContext ctx) {
        codeMap.putExecutable(ctx, (double arg) -> - arg);
    }

    @Override public void exitSum(@Nonnull SumContext ctx) {
        codeMap.putExecutable(
                ctx,
                (lower, upper, subExpression) -> aggregate(ctx, lower, upper + 1, subExpression, 0.0, Addition)
        );
    }

    @Override public void exitProd(@Nonnull ProdContext ctx) {
        codeMap.putExecutable(
                ctx,
                (lower, upper, subExpression) -> aggregate(ctx, lower, upper + 1, subExpression, 1.0, Multiplication)
        );
    }

    // in babel bounds are inclusive,
    // but in java the upperbound is always exclusive by convention!
    private double aggregate(RuleContext ctx,
                             int lowerInclusive,
                             int upperExclusive,
                             ContextFreeNumericExecutable subExpression,
                             double seed,
                             BinaryDecimalOperation opToAggregate) {

        LambdaExprContext lambdaScopeKey = TreeHelper.siblingsOf(ctx).ofType(LambdaExprContext.class).single();
        String lambdaParam = symbolTable.getSymbolesDeclaredIn(lambdaScopeKey).single();

        double aggretate = seed;
        for (int index : Factories.range(lowerInclusive, upperExclusive)) {
            symbolTable.setSymbolValue(lambdaScopeKey , lambdaParam, index);
            //note: now that the symbol table value for lambdaParam has changed,
            //the closed lambda 'subExpression' will give a different result
            Number subExpressionResult = subExpression.execute();
            aggretate = opToAggregate.execute(aggretate, subExpressionResult.doubleValue());
        }

        return aggretate;
    }

    @Override public void exitVariable(@Nonnull VariableContext ctx) {
        String variable = ctx.getText();
        codeMap.putExecutable(ctx, () -> symbolTable.findLocalValueFor(ctx, variable));
    }

    @Override public void exitLiteral(@Nonnull LiteralContext ctx) {
        Number value = ctx.CONSTANT() != null ? operations.findValueForConstant(ctx.getText()) :
                       ctx.INTEGER() != null ? Integer.parseInt(ctx.getText()) :
                       ctx.FLOAT() != null ? Double.parseDouble(ctx.getText()) :
                               ExceptionUtilities.otherwiseThrow(new IllegalStateException());

        codeMap.putExecutable(ctx, () -> value);
    }

    public ContextFreeNumericExecutable getRootExecutor(){
        return rootExecutor;
    }

    @Deprecated
    public double getResult() {
        return rootExecutor.execute().doubleValue();
    }
}