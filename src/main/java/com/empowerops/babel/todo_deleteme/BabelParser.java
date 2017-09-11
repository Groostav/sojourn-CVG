// Generated from C:\Users\Geoff\Code\OASIS/Problem-Definition//pre-src/BabelParser.g4 by ANTLR 4.5.3
package com.empowerops.babel.todo_deleteme;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;

import java.util.List;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class BabelParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.5.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		INTEGER=1, FLOAT=2, DIGIT=3, COS=4, SIN=5, TAN=6, ATAN=7, ACOS=8, ASIN=9, 
		SINH=10, COSH=11, TANH=12, COT=13, LN=14, LOG=15, ABS=16, SQRT=17, CBRT=18, 
		SQR=19, CUBE=20, CIEL=21, FLOOR=22, MAX=23, MIN=24, CONSTANT=25, SUM=26, 
		PROD=27, DYN_VAR=28, VARIABLE=29, LAMBDA=30, LT=31, LTEQ=32, GT=33, GTEQ=34, 
		EQ=35, MULT=36, DIV=37, MOD=38, PLUS=39, MINUS=40, EXPONENT=41, OPEN_PAREN=42, 
		CLOSE_PAREN=43, OPEN_BRACKET=44, CLOSE_BRACKET=45, COMMA=46, LINEBREAKS=47;
	public static final int
		RULE_expression = 0, RULE_expr = 1, RULE_lambdaExpr = 2, RULE_plus = 3, 
		RULE_minus = 4, RULE_mult = 5, RULE_div = 6, RULE_mod = 7, RULE_exponent = 8, 
		RULE_sum = 9, RULE_prod = 10, RULE_dynamicVariableAccess = 11, RULE_binaryFunction = 12, 
		RULE_unaryFunction = 13, RULE_negate = 14, RULE_lt = 15, RULE_lteq = 16, 
		RULE_gt = 17, RULE_gteq = 18, RULE_eq = 19, RULE_variable_only = 20, RULE_name = 21, 
		RULE_variable = 22, RULE_literal = 23;
	public static final String[] ruleNames = {
		"expression", "expr", "lambdaExpr", "plus", "minus", "mult", "div", "mod", 
		"exponent", "sum", "prod", "dynamicVariableAccess", "binaryFunction", 
		"unaryFunction", "negate", "lt", "lteq", "gt", "gteq", "eq", "variable_only", 
		"name", "variable", "literal"
	};

	private static final String[] _LITERAL_NAMES = {
		null, null, null, null, "'cos'", "'sin'", "'tan'", "'atan'", "'acos'", 
		"'asin'", "'sinh'", "'cosh'", "'tanh'", "'cot'", "'ln'", "'log'", "'abs'", 
		"'sqrt'", "'cbrt'", "'sqr'", "'cube'", "'ceil'", "'floor'", "'max'", "'min'", 
		null, "'sum'", "'prod'", "'var'", null, "'->'", "'<'", "'<='", "'>'", 
		"'>='", "'=='", "'*'", "'/'", "'%'", "'+'", "'-'", "'^'", "'('", "')'", 
		"'['", "']'", "','"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, "INTEGER", "FLOAT", "DIGIT", "COS", "SIN", "TAN", "ATAN", "ACOS", 
		"ASIN", "SINH", "COSH", "TANH", "COT", "LN", "LOG", "ABS", "SQRT", "CBRT", 
		"SQR", "CUBE", "CIEL", "FLOOR", "MAX", "MIN", "CONSTANT", "SUM", "PROD", 
		"DYN_VAR", "VARIABLE", "LAMBDA", "LT", "LTEQ", "GT", "GTEQ", "EQ", "MULT", 
		"DIV", "MOD", "PLUS", "MINUS", "EXPONENT", "OPEN_PAREN", "CLOSE_PAREN", 
		"OPEN_BRACKET", "CLOSE_BRACKET", "COMMA", "LINEBREAKS"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "BabelParser.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public BabelParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class ExpressionContext extends ParserRuleContext {
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public TerminalNode EOF() { return getToken(BabelParser.EOF, 0); }
		public ExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_expression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitExpression(this);
		}
	}

	public final ExpressionContext expression() throws RecognitionException {
		ExpressionContext _localctx = new ExpressionContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_expression);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(48);
			expr(0);
			setState(49);
			match(EOF);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExprContext extends ParserRuleContext {
		public LiteralContext literal() {
			return getRuleContext(LiteralContext.class,0);
		}
		public VariableContext variable() {
			return getRuleContext(VariableContext.class,0);
		}
		public List<ExprContext> expr() {
			return getRuleContexts(ExprContext.class);
		}
		public ExprContext expr(int i) {
			return getRuleContext(ExprContext.class,i);
		}
		public LambdaExprContext lambdaExpr() {
			return getRuleContext(LambdaExprContext.class,0);
		}
		public SumContext sum() {
			return getRuleContext(SumContext.class,0);
		}
		public ProdContext prod() {
			return getRuleContext(ProdContext.class,0);
		}
		public BinaryFunctionContext binaryFunction() {
			return getRuleContext(BinaryFunctionContext.class,0);
		}
		public UnaryFunctionContext unaryFunction() {
			return getRuleContext(UnaryFunctionContext.class,0);
		}
		public DynamicVariableAccessContext dynamicVariableAccess() {
			return getRuleContext(DynamicVariableAccessContext.class,0);
		}
		public NegateContext negate() {
			return getRuleContext(NegateContext.class,0);
		}
		public MultContext mult() {
			return getRuleContext(MultContext.class,0);
		}
		public DivContext div() {
			return getRuleContext(DivContext.class,0);
		}
		public ModContext mod() {
			return getRuleContext(ModContext.class,0);
		}
		public PlusContext plus() {
			return getRuleContext(PlusContext.class,0);
		}
		public MinusContext minus() {
			return getRuleContext(MinusContext.class,0);
		}
		public LtContext lt() {
			return getRuleContext(LtContext.class,0);
		}
		public LteqContext lteq() {
			return getRuleContext(LteqContext.class,0);
		}
		public GtContext gt() {
			return getRuleContext(GtContext.class,0);
		}
		public GteqContext gteq() {
			return getRuleContext(GteqContext.class,0);
		}
		public EqContext eq() {
			return getRuleContext(EqContext.class,0);
		}
		public ExponentContext exponent() {
			return getRuleContext(ExponentContext.class,0);
		}
		public ExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_expr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitExpr(this);
		}
	}

	public final ExprContext expr() throws RecognitionException {
		return expr(0);
	}

	private ExprContext expr(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ExprContext _localctx = new ExprContext(_ctx, _parentState);
		ExprContext _prevctx = _localctx;
		int _startState = 2;
		enterRecursionRule(_localctx, 2, RULE_expr, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(92);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				{
				setState(54);
				switch (_input.LA(1)) {
				case INTEGER:
				case FLOAT:
				case CONSTANT:
					{
					setState(52);
					literal();
					}
					break;
				case VARIABLE:
					{
					setState(53);
					variable();
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				}
				break;
			case 2:
				{
				setState(56);
				match(OPEN_PAREN);
				setState(57);
				expr(0);
				setState(58);
				match(CLOSE_PAREN);
				}
				break;
			case 3:
				{
				setState(62);
				switch (_input.LA(1)) {
				case SUM:
					{
					setState(60);
					sum();
					}
					break;
				case PROD:
					{
					setState(61);
					prod();
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				setState(64);
				match(OPEN_PAREN);
				setState(65);
				expr(0);
				setState(66);
				match(COMMA);
				setState(67);
				expr(0);
				setState(68);
				match(COMMA);
				setState(69);
				lambdaExpr();
				setState(70);
				match(CLOSE_PAREN);
				}
				break;
			case 4:
				{
				setState(72);
				binaryFunction();
				setState(73);
				match(OPEN_PAREN);
				setState(74);
				expr(0);
				setState(75);
				match(COMMA);
				setState(76);
				expr(0);
				setState(77);
				match(CLOSE_PAREN);
				}
				break;
			case 5:
				{
				setState(79);
				unaryFunction();
				setState(80);
				match(OPEN_PAREN);
				setState(81);
				expr(0);
				setState(82);
				match(CLOSE_PAREN);
				}
				break;
			case 6:
				{
				setState(84);
				dynamicVariableAccess();
				setState(85);
				match(OPEN_BRACKET);
				setState(86);
				expr(0);
				setState(87);
				match(CLOSE_BRACKET);
				}
				break;
			case 7:
				{
				setState(89);
				negate();
				setState(90);
				expr(5);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(131);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(129);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,7,_ctx) ) {
					case 1:
						{
						_localctx = new ExprContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_expr);
						setState(94);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(98);
						switch (_input.LA(1)) {
						case MULT:
							{
							setState(95);
							mult();
							}
							break;
						case DIV:
							{
							setState(96);
							div();
							}
							break;
						case MOD:
							{
							setState(97);
							mod();
							}
							break;
						default:
							throw new NoViableAltException(this);
						}
						setState(100);
						expr(4);
						}
						break;
					case 2:
						{
						_localctx = new ExprContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_expr);
						setState(102);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(105);
						switch (_input.LA(1)) {
						case PLUS:
							{
							setState(103);
							plus();
							}
							break;
						case MINUS:
							{
							setState(104);
							minus();
							}
							break;
						default:
							throw new NoViableAltException(this);
						}
						setState(107);
						expr(3);
						}
						break;
					case 3:
						{
						_localctx = new ExprContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_expr);
						setState(109);
						if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
						setState(115);
						switch (_input.LA(1)) {
						case LT:
							{
							setState(110);
							lt();
							}
							break;
						case LTEQ:
							{
							setState(111);
							lteq();
							}
							break;
						case GT:
							{
							setState(112);
							gt();
							}
							break;
						case GTEQ:
							{
							setState(113);
							gteq();
							}
							break;
						case EQ:
							{
							setState(114);
							eq();
							}
							break;
						default:
							throw new NoViableAltException(this);
						}
						setState(117);
						expr(2);
						}
						break;
					case 4:
						{
						_localctx = new ExprContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_expr);
						setState(119);
						if (!(precpred(_ctx, 4))) throw new FailedPredicateException(this, "precpred(_ctx, 4)");
						setState(120);
						exponent();
						setState(127);
						switch (_input.LA(1)) {
						case OPEN_PAREN:
							{
							{
							setState(121);
							match(OPEN_PAREN);
							setState(122);
							expr(0);
							setState(123);
							match(CLOSE_PAREN);
							}
							}
							break;
						case INTEGER:
						case FLOAT:
						case CONSTANT:
							{
							setState(125);
							literal();
							}
							break;
						case VARIABLE:
							{
							setState(126);
							variable();
							}
							break;
						default:
							throw new NoViableAltException(this);
						}
						}
						break;
					}
					} 
				}
				setState(133);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class LambdaExprContext extends ParserRuleContext {
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public LambdaExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_lambdaExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterLambdaExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitLambdaExpr(this);
		}
	}

	public final LambdaExprContext lambdaExpr() throws RecognitionException {
		LambdaExprContext _localctx = new LambdaExprContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_lambdaExpr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(134);
			name();
			setState(135);
			match(LAMBDA);
			setState(136);
			expr(0);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class PlusContext extends ParserRuleContext {
		public PlusContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_plus; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterPlus(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitPlus(this);
		}
	}

	public final PlusContext plus() throws RecognitionException {
		PlusContext _localctx = new PlusContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_plus);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(138);
			match(PLUS);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MinusContext extends ParserRuleContext {
		public MinusContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_minus; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterMinus(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitMinus(this);
		}
	}

	public final MinusContext minus() throws RecognitionException {
		MinusContext _localctx = new MinusContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_minus);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(140);
			match(MINUS);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MultContext extends ParserRuleContext {
		public MultContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_mult; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterMult(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitMult(this);
		}
	}

	public final MultContext mult() throws RecognitionException {
		MultContext _localctx = new MultContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_mult);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(142);
			match(MULT);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DivContext extends ParserRuleContext {
		public DivContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_div; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterDiv(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitDiv(this);
		}
	}

	public final DivContext div() throws RecognitionException {
		DivContext _localctx = new DivContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_div);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(144);
			match(DIV);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ModContext extends ParserRuleContext {
		public ModContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_mod; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterMod(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitMod(this);
		}
	}

	public final ModContext mod() throws RecognitionException {
		ModContext _localctx = new ModContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_mod);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(146);
			match(MOD);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExponentContext extends ParserRuleContext {
		public ExponentContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_exponent; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterExponent(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitExponent(this);
		}
	}

	public final ExponentContext exponent() throws RecognitionException {
		ExponentContext _localctx = new ExponentContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_exponent);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(148);
			match(EXPONENT);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SumContext extends ParserRuleContext {
		public SumContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_sum; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterSum(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitSum(this);
		}
	}

	public final SumContext sum() throws RecognitionException {
		SumContext _localctx = new SumContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_sum);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(150);
			match(SUM);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ProdContext extends ParserRuleContext {
		public ProdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_prod; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterProd(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitProd(this);
		}
	}

	public final ProdContext prod() throws RecognitionException {
		ProdContext _localctx = new ProdContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_prod);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(152);
			match(PROD);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DynamicVariableAccessContext extends ParserRuleContext {
		public DynamicVariableAccessContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_dynamicVariableAccess; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterDynamicVariableAccess(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitDynamicVariableAccess(this);
		}
	}

	public final DynamicVariableAccessContext dynamicVariableAccess() throws RecognitionException {
		DynamicVariableAccessContext _localctx = new DynamicVariableAccessContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_dynamicVariableAccess);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(154);
			match(DYN_VAR);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BinaryFunctionContext extends ParserRuleContext {
		public BinaryFunctionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_binaryFunction; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterBinaryFunction(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitBinaryFunction(this);
		}
	}

	public final BinaryFunctionContext binaryFunction() throws RecognitionException {
		BinaryFunctionContext _localctx = new BinaryFunctionContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_binaryFunction);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(156);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << LOG) | (1L << MAX) | (1L << MIN))) != 0)) ) {
			_errHandler.recoverInline(this);
			} else {
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class UnaryFunctionContext extends ParserRuleContext {
		public UnaryFunctionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_unaryFunction; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterUnaryFunction(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitUnaryFunction(this);
		}
	}

	public final UnaryFunctionContext unaryFunction() throws RecognitionException {
		UnaryFunctionContext _localctx = new UnaryFunctionContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_unaryFunction);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(158);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << COS) | (1L << SIN) | (1L << TAN) | (1L << ATAN) | (1L << ACOS) | (1L << ASIN) | (1L << SINH) | (1L << COSH) | (1L << TANH) | (1L << COT) | (1L << LN) | (1L << LOG) | (1L << ABS) | (1L << SQRT) | (1L << CBRT) | (1L << SQR) | (1L << CUBE) | (1L << CIEL) | (1L << FLOOR))) != 0)) ) {
			_errHandler.recoverInline(this);
			} else {
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class NegateContext extends ParserRuleContext {
		public NegateContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_negate; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterNegate(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitNegate(this);
		}
	}

	public final NegateContext negate() throws RecognitionException {
		NegateContext _localctx = new NegateContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_negate);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(160);
			match(MINUS);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LtContext extends ParserRuleContext {
		public LtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_lt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterLt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitLt(this);
		}
	}

	public final LtContext lt() throws RecognitionException {
		LtContext _localctx = new LtContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_lt);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(162);
			match(LT);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LteqContext extends ParserRuleContext {
		public LteqContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_lteq; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterLteq(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitLteq(this);
		}
	}

	public final LteqContext lteq() throws RecognitionException {
		LteqContext _localctx = new LteqContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_lteq);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(164);
			match(LTEQ);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class GtContext extends ParserRuleContext {
		public GtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_gt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterGt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitGt(this);
		}
	}

	public final GtContext gt() throws RecognitionException {
		GtContext _localctx = new GtContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_gt);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(166);
			match(GT);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class GteqContext extends ParserRuleContext {
		public GteqContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_gteq; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterGteq(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitGteq(this);
		}
	}

	public final GteqContext gteq() throws RecognitionException {
		GteqContext _localctx = new GteqContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_gteq);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(168);
			match(GTEQ);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EqContext extends ParserRuleContext {
		public EqContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_eq; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterEq(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitEq(this);
		}
	}

	public final EqContext eq() throws RecognitionException {
		EqContext _localctx = new EqContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_eq);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(170);
			match(EQ);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Variable_onlyContext extends ParserRuleContext {
		public VariableContext variable() {
			return getRuleContext(VariableContext.class,0);
		}
		public TerminalNode EOF() { return getToken(BabelParser.EOF, 0); }
		public Variable_onlyContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_variable_only; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterVariable_only(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitVariable_only(this);
		}
	}

	public final Variable_onlyContext variable_only() throws RecognitionException {
		Variable_onlyContext _localctx = new Variable_onlyContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_variable_only);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(172);
			variable();
			setState(173);
			match(EOF);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class NameContext extends ParserRuleContext {
		public TerminalNode VARIABLE() { return getToken(BabelParser.VARIABLE, 0); }
		public NameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_name; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitName(this);
		}
	}

	public final NameContext name() throws RecognitionException {
		NameContext _localctx = new NameContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_name);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(175);
			match(VARIABLE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VariableContext extends ParserRuleContext {
		public TerminalNode VARIABLE() { return getToken(BabelParser.VARIABLE, 0); }
		public VariableContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_variable; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterVariable(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitVariable(this);
		}
	}

	public final VariableContext variable() throws RecognitionException {
		VariableContext _localctx = new VariableContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_variable);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(177);
			match(VARIABLE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LiteralContext extends ParserRuleContext {
		public TerminalNode INTEGER() { return getToken(BabelParser.INTEGER, 0); }
		public TerminalNode FLOAT() { return getToken(BabelParser.FLOAT, 0); }
		public TerminalNode CONSTANT() { return getToken(BabelParser.CONSTANT, 0); }
		public LiteralContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override
        public int getRuleIndex() { return RULE_literal; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).enterLiteral(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BabelParserListener ) ((BabelParserListener)listener).exitLiteral(this);
		}
	}

	public final LiteralContext literal() throws RecognitionException {
		LiteralContext _localctx = new LiteralContext(_ctx, getState());
		enterRule(_localctx, 46, RULE_literal);
		int _la;
		try {
			setState(181);
			switch (_input.LA(1)) {
			case INTEGER:
			case FLOAT:
				enterOuterAlt(_localctx, 1);
				{
				setState(179);
				_la = _input.LA(1);
				if ( !(_la==INTEGER || _la==FLOAT) ) {
				_errHandler.recoverInline(this);
				} else {
					consume();
				}
				}
				break;
			case CONSTANT:
				enterOuterAlt(_localctx, 2);
				{
				setState(180);
				match(CONSTANT);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 1:
			return expr_sempred((ExprContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean expr_sempred(ExprContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 3);
		case 1:
			return precpred(_ctx, 2);
		case 2:
			return precpred(_ctx, 1);
		case 3:
			return precpred(_ctx, 4);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\3\61\u00ba\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\3\2\3\2\3\2\3\3\3\3\3\3\5\39\n\3\3\3\3\3\3\3\3\3\3\3\3\3\5\3A\n\3\3\3"+
		"\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3"+
		"\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\5\3_\n\3\3\3\3\3\3\3\3\3\5\3e\n"+
		"\3\3\3\3\3\3\3\3\3\3\3\5\3l\n\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\5\3v\n"+
		"\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\5\3\u0082\n\3\7\3\u0084\n\3"+
		"\f\3\16\3\u0087\13\3\3\4\3\4\3\4\3\4\3\5\3\5\3\6\3\6\3\7\3\7\3\b\3\b\3"+
		"\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\16\3\16\3\17\3\17\3\20\3\20"+
		"\3\21\3\21\3\22\3\22\3\23\3\23\3\24\3\24\3\25\3\25\3\26\3\26\3\26\3\27"+
		"\3\27\3\30\3\30\3\31\3\31\5\31\u00b8\n\31\3\31\2\3\4\32\2\4\6\b\n\f\16"+
		"\20\22\24\26\30\32\34\36 \"$&(*,.\60\2\5\4\2\21\21\31\32\3\2\6\30\3\2"+
		"\3\4\u00b7\2\62\3\2\2\2\4^\3\2\2\2\6\u0088\3\2\2\2\b\u008c\3\2\2\2\n\u008e"+
		"\3\2\2\2\f\u0090\3\2\2\2\16\u0092\3\2\2\2\20\u0094\3\2\2\2\22\u0096\3"+
		"\2\2\2\24\u0098\3\2\2\2\26\u009a\3\2\2\2\30\u009c\3\2\2\2\32\u009e\3\2"+
		"\2\2\34\u00a0\3\2\2\2\36\u00a2\3\2\2\2 \u00a4\3\2\2\2\"\u00a6\3\2\2\2"+
		"$\u00a8\3\2\2\2&\u00aa\3\2\2\2(\u00ac\3\2\2\2*\u00ae\3\2\2\2,\u00b1\3"+
		"\2\2\2.\u00b3\3\2\2\2\60\u00b7\3\2\2\2\62\63\5\4\3\2\63\64\7\2\2\3\64"+
		"\3\3\2\2\2\658\b\3\1\2\669\5\60\31\2\679\5.\30\28\66\3\2\2\28\67\3\2\2"+
		"\29_\3\2\2\2:;\7,\2\2;<\5\4\3\2<=\7-\2\2=_\3\2\2\2>A\5\24\13\2?A\5\26"+
		"\f\2@>\3\2\2\2@?\3\2\2\2AB\3\2\2\2BC\7,\2\2CD\5\4\3\2DE\7\60\2\2EF\5\4"+
		"\3\2FG\7\60\2\2GH\5\6\4\2HI\7-\2\2I_\3\2\2\2JK\5\32\16\2KL\7,\2\2LM\5"+
		"\4\3\2MN\7\60\2\2NO\5\4\3\2OP\7-\2\2P_\3\2\2\2QR\5\34\17\2RS\7,\2\2ST"+
		"\5\4\3\2TU\7-\2\2U_\3\2\2\2VW\5\30\r\2WX\7.\2\2XY\5\4\3\2YZ\7/\2\2Z_\3"+
		"\2\2\2[\\\5\36\20\2\\]\5\4\3\7]_\3\2\2\2^\65\3\2\2\2^:\3\2\2\2^@\3\2\2"+
		"\2^J\3\2\2\2^Q\3\2\2\2^V\3\2\2\2^[\3\2\2\2_\u0085\3\2\2\2`d\f\5\2\2ae"+
		"\5\f\7\2be\5\16\b\2ce\5\20\t\2da\3\2\2\2db\3\2\2\2dc\3\2\2\2ef\3\2\2\2"+
		"fg\5\4\3\6g\u0084\3\2\2\2hk\f\4\2\2il\5\b\5\2jl\5\n\6\2ki\3\2\2\2kj\3"+
		"\2\2\2lm\3\2\2\2mn\5\4\3\5n\u0084\3\2\2\2ou\f\3\2\2pv\5 \21\2qv\5\"\22"+
		"\2rv\5$\23\2sv\5&\24\2tv\5(\25\2up\3\2\2\2uq\3\2\2\2ur\3\2\2\2us\3\2\2"+
		"\2ut\3\2\2\2vw\3\2\2\2wx\5\4\3\4x\u0084\3\2\2\2yz\f\6\2\2z\u0081\5\22"+
		"\n\2{|\7,\2\2|}\5\4\3\2}~\7-\2\2~\u0082\3\2\2\2\177\u0082\5\60\31\2\u0080"+
		"\u0082\5.\30\2\u0081{\3\2\2\2\u0081\177\3\2\2\2\u0081\u0080\3\2\2\2\u0082"+
		"\u0084\3\2\2\2\u0083`\3\2\2\2\u0083h\3\2\2\2\u0083o\3\2\2\2\u0083y\3\2"+
		"\2\2\u0084\u0087\3\2\2\2\u0085\u0083\3\2\2\2\u0085\u0086\3\2\2\2\u0086"+
		"\5\3\2\2\2\u0087\u0085\3\2\2\2\u0088\u0089\5,\27\2\u0089\u008a\7 \2\2"+
		"\u008a\u008b\5\4\3\2\u008b\7\3\2\2\2\u008c\u008d\7)\2\2\u008d\t\3\2\2"+
		"\2\u008e\u008f\7*\2\2\u008f\13\3\2\2\2\u0090\u0091\7&\2\2\u0091\r\3\2"+
		"\2\2\u0092\u0093\7\'\2\2\u0093\17\3\2\2\2\u0094\u0095\7(\2\2\u0095\21"+
		"\3\2\2\2\u0096\u0097\7+\2\2\u0097\23\3\2\2\2\u0098\u0099\7\34\2\2\u0099"+
		"\25\3\2\2\2\u009a\u009b\7\35\2\2\u009b\27\3\2\2\2\u009c\u009d\7\36\2\2"+
		"\u009d\31\3\2\2\2\u009e\u009f\t\2\2\2\u009f\33\3\2\2\2\u00a0\u00a1\t\3"+
		"\2\2\u00a1\35\3\2\2\2\u00a2\u00a3\7*\2\2\u00a3\37\3\2\2\2\u00a4\u00a5"+
		"\7!\2\2\u00a5!\3\2\2\2\u00a6\u00a7\7\"\2\2\u00a7#\3\2\2\2\u00a8\u00a9"+
		"\7#\2\2\u00a9%\3\2\2\2\u00aa\u00ab\7$\2\2\u00ab\'\3\2\2\2\u00ac\u00ad"+
		"\7%\2\2\u00ad)\3\2\2\2\u00ae\u00af\5.\30\2\u00af\u00b0\7\2\2\3\u00b0+"+
		"\3\2\2\2\u00b1\u00b2\7\37\2\2\u00b2-\3\2\2\2\u00b3\u00b4\7\37\2\2\u00b4"+
		"/\3\2\2\2\u00b5\u00b8\t\4\2\2\u00b6\u00b8\7\33\2\2\u00b7\u00b5\3\2\2\2"+
		"\u00b7\u00b6\3\2\2\2\u00b8\61\3\2\2\2\f8@^dku\u0081\u0083\u0085\u00b7";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}