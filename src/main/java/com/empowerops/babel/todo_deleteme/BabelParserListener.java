// Generated from C:\Users\Geoff\Code\OASIS/Problem-Definition//pre-src/BabelParser.g4 by ANTLR 4.5.3
package com.empowerops.babel.todo_deleteme;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link BabelParser}.
 */
public interface BabelParserListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link BabelParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpression(BabelParser.ExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpression(BabelParser.ExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#expr}.
	 * @param ctx the parse tree
	 */
	void enterExpr(BabelParser.ExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#expr}.
	 * @param ctx the parse tree
	 */
	void exitExpr(BabelParser.ExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#lambdaExpr}.
	 * @param ctx the parse tree
	 */
	void enterLambdaExpr(BabelParser.LambdaExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#lambdaExpr}.
	 * @param ctx the parse tree
	 */
	void exitLambdaExpr(BabelParser.LambdaExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#plus}.
	 * @param ctx the parse tree
	 */
	void enterPlus(BabelParser.PlusContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#plus}.
	 * @param ctx the parse tree
	 */
	void exitPlus(BabelParser.PlusContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#minus}.
	 * @param ctx the parse tree
	 */
	void enterMinus(BabelParser.MinusContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#minus}.
	 * @param ctx the parse tree
	 */
	void exitMinus(BabelParser.MinusContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#mult}.
	 * @param ctx the parse tree
	 */
	void enterMult(BabelParser.MultContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#mult}.
	 * @param ctx the parse tree
	 */
	void exitMult(BabelParser.MultContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#div}.
	 * @param ctx the parse tree
	 */
	void enterDiv(BabelParser.DivContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#div}.
	 * @param ctx the parse tree
	 */
	void exitDiv(BabelParser.DivContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#mod}.
	 * @param ctx the parse tree
	 */
	void enterMod(BabelParser.ModContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#mod}.
	 * @param ctx the parse tree
	 */
	void exitMod(BabelParser.ModContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#exponent}.
	 * @param ctx the parse tree
	 */
	void enterExponent(BabelParser.ExponentContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#exponent}.
	 * @param ctx the parse tree
	 */
	void exitExponent(BabelParser.ExponentContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#sum}.
	 * @param ctx the parse tree
	 */
	void enterSum(BabelParser.SumContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#sum}.
	 * @param ctx the parse tree
	 */
	void exitSum(BabelParser.SumContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#prod}.
	 * @param ctx the parse tree
	 */
	void enterProd(BabelParser.ProdContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#prod}.
	 * @param ctx the parse tree
	 */
	void exitProd(BabelParser.ProdContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#dynamicVariableAccess}.
	 * @param ctx the parse tree
	 */
	void enterDynamicVariableAccess(BabelParser.DynamicVariableAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#dynamicVariableAccess}.
	 * @param ctx the parse tree
	 */
	void exitDynamicVariableAccess(BabelParser.DynamicVariableAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#binaryFunction}.
	 * @param ctx the parse tree
	 */
	void enterBinaryFunction(BabelParser.BinaryFunctionContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#binaryFunction}.
	 * @param ctx the parse tree
	 */
	void exitBinaryFunction(BabelParser.BinaryFunctionContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#unaryFunction}.
	 * @param ctx the parse tree
	 */
	void enterUnaryFunction(BabelParser.UnaryFunctionContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#unaryFunction}.
	 * @param ctx the parse tree
	 */
	void exitUnaryFunction(BabelParser.UnaryFunctionContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#negate}.
	 * @param ctx the parse tree
	 */
	void enterNegate(BabelParser.NegateContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#negate}.
	 * @param ctx the parse tree
	 */
	void exitNegate(BabelParser.NegateContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#lt}.
	 * @param ctx the parse tree
	 */
	void enterLt(BabelParser.LtContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#lt}.
	 * @param ctx the parse tree
	 */
	void exitLt(BabelParser.LtContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#lteq}.
	 * @param ctx the parse tree
	 */
	void enterLteq(BabelParser.LteqContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#lteq}.
	 * @param ctx the parse tree
	 */
	void exitLteq(BabelParser.LteqContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#gt}.
	 * @param ctx the parse tree
	 */
	void enterGt(BabelParser.GtContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#gt}.
	 * @param ctx the parse tree
	 */
	void exitGt(BabelParser.GtContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#gteq}.
	 * @param ctx the parse tree
	 */
	void enterGteq(BabelParser.GteqContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#gteq}.
	 * @param ctx the parse tree
	 */
	void exitGteq(BabelParser.GteqContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#eq}.
	 * @param ctx the parse tree
	 */
	void enterEq(BabelParser.EqContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#eq}.
	 * @param ctx the parse tree
	 */
	void exitEq(BabelParser.EqContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#variable_only}.
	 * @param ctx the parse tree
	 */
	void enterVariable_only(BabelParser.Variable_onlyContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#variable_only}.
	 * @param ctx the parse tree
	 */
	void exitVariable_only(BabelParser.Variable_onlyContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#name}.
	 * @param ctx the parse tree
	 */
	void enterName(BabelParser.NameContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#name}.
	 * @param ctx the parse tree
	 */
	void exitName(BabelParser.NameContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#variable}.
	 * @param ctx the parse tree
	 */
	void enterVariable(BabelParser.VariableContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#variable}.
	 * @param ctx the parse tree
	 */
	void exitVariable(BabelParser.VariableContext ctx);
	/**
	 * Enter a parse tree produced by {@link BabelParser#literal}.
	 * @param ctx the parse tree
	 */
	void enterLiteral(BabelParser.LiteralContext ctx);
	/**
	 * Exit a parse tree produced by {@link BabelParser#literal}.
	 * @param ctx the parse tree
	 */
	void exitLiteral(BabelParser.LiteralContext ctx);
}