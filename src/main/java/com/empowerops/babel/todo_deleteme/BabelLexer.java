// Generated from C:\Users\Geoff\Code\OASIS/Problem-Definition//pre-src/BabelLexer.g4 by ANTLR 4.5.3
package com.empowerops.babel.todo_deleteme;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class BabelLexer extends Lexer {
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
	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"INTEGER", "FLOAT", "DIGIT", "COS", "SIN", "TAN", "ATAN", "ACOS", "ASIN", 
		"SINH", "COSH", "TANH", "COT", "LN", "LOG", "ABS", "SQRT", "CBRT", "SQR", 
		"CUBE", "CIEL", "FLOOR", "MAX", "MIN", "CONSTANT", "SUM", "PROD", "DYN_VAR", 
		"VARIABLE", "LAMBDA", "LT", "LTEQ", "GT", "GTEQ", "EQ", "MULT", "DIV", 
		"MOD", "PLUS", "MINUS", "EXPONENT", "OPEN_PAREN", "CLOSE_PAREN", "OPEN_BRACKET", 
		"CLOSE_BRACKET", "COMMA", "VARIABLE_START", "VARIABLE_PART", "LINEBREAKS"
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


	public BabelLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "BabelLexer.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\2\61\u012f\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31"+
		"\t\31\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t"+
		" \4!\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t"+
		"+\4,\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\3\2\6\2g\n\2\r"+
		"\2\16\2h\3\3\7\3l\n\3\f\3\16\3o\13\3\3\3\3\3\6\3s\n\3\r\3\16\3t\3\3\3"+
		"\3\5\3y\n\3\3\3\6\3|\n\3\r\3\16\3}\5\3\u0080\n\3\3\4\3\4\3\5\3\5\3\5\3"+
		"\5\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\b\3\t\3\t\3\t\3\t"+
		"\3\t\3\n\3\n\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f"+
		"\3\r\3\r\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\17\3\17\3\17\3\20\3\20\3\20"+
		"\3\20\3\21\3\21\3\21\3\21\3\22\3\22\3\22\3\22\3\22\3\23\3\23\3\23\3\23"+
		"\3\23\3\24\3\24\3\24\3\24\3\25\3\25\3\25\3\25\3\25\3\26\3\26\3\26\3\26"+
		"\3\26\3\27\3\27\3\27\3\27\3\27\3\27\3\30\3\30\3\30\3\30\3\31\3\31\3\31"+
		"\3\31\3\32\3\32\3\32\5\32\u00e6\n\32\3\33\3\33\3\33\3\33\3\34\3\34\3\34"+
		"\3\34\3\34\3\35\3\35\3\35\3\35\3\36\3\36\7\36\u00f7\n\36\f\36\16\36\u00fa"+
		"\13\36\3\37\3\37\3\37\3 \3 \3!\3!\3!\3\"\3\"\3#\3#\3#\3$\3$\3$\3%\3%\3"+
		"&\3&\3\'\3\'\3(\3(\3)\3)\3*\3*\3+\3+\3,\3,\3-\3-\3.\3.\3/\3/\3\60\3\60"+
		"\3\60\3\60\5\60\u0126\n\60\3\61\3\61\5\61\u012a\n\61\3\62\3\62\3\62\3"+
		"\62\2\2\63\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33"+
		"\17\35\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67"+
		"\359\36;\37= ?!A\"C#E$G%I&K\'M(O)Q*S+U,W-Y.[/]\60_\2a\2c\61\3\2\t\4\2"+
		"GGgg\5\2C\\aac|\4\2\2\u0101\ud802\udc01\3\2\ud802\udc01\3\2\udc02\ue001"+
		"\3\2\62;\5\2\f\f\17\17\"\"\u0137\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2"+
		"\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2"+
		"\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2"+
		"\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2"+
		"\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2"+
		"\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\2=\3\2\2\2\2?\3\2\2\2\2A\3\2\2\2"+
		"\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2\2\2I\3\2\2\2\2K\3\2\2\2\2M\3\2\2\2\2O"+
		"\3\2\2\2\2Q\3\2\2\2\2S\3\2\2\2\2U\3\2\2\2\2W\3\2\2\2\2Y\3\2\2\2\2[\3\2"+
		"\2\2\2]\3\2\2\2\2c\3\2\2\2\3f\3\2\2\2\5m\3\2\2\2\7\u0081\3\2\2\2\t\u0083"+
		"\3\2\2\2\13\u0087\3\2\2\2\r\u008b\3\2\2\2\17\u008f\3\2\2\2\21\u0094\3"+
		"\2\2\2\23\u0099\3\2\2\2\25\u009e\3\2\2\2\27\u00a3\3\2\2\2\31\u00a8\3\2"+
		"\2\2\33\u00ad\3\2\2\2\35\u00b1\3\2\2\2\37\u00b4\3\2\2\2!\u00b8\3\2\2\2"+
		"#\u00bc\3\2\2\2%\u00c1\3\2\2\2\'\u00c6\3\2\2\2)\u00ca\3\2\2\2+\u00cf\3"+
		"\2\2\2-\u00d4\3\2\2\2/\u00da\3\2\2\2\61\u00de\3\2\2\2\63\u00e5\3\2\2\2"+
		"\65\u00e7\3\2\2\2\67\u00eb\3\2\2\29\u00f0\3\2\2\2;\u00f4\3\2\2\2=\u00fb"+
		"\3\2\2\2?\u00fe\3\2\2\2A\u0100\3\2\2\2C\u0103\3\2\2\2E\u0105\3\2\2\2G"+
		"\u0108\3\2\2\2I\u010b\3\2\2\2K\u010d\3\2\2\2M\u010f\3\2\2\2O\u0111\3\2"+
		"\2\2Q\u0113\3\2\2\2S\u0115\3\2\2\2U\u0117\3\2\2\2W\u0119\3\2\2\2Y\u011b"+
		"\3\2\2\2[\u011d\3\2\2\2]\u011f\3\2\2\2_\u0125\3\2\2\2a\u0129\3\2\2\2c"+
		"\u012b\3\2\2\2eg\5\7\4\2fe\3\2\2\2gh\3\2\2\2hf\3\2\2\2hi\3\2\2\2i\4\3"+
		"\2\2\2jl\5\7\4\2kj\3\2\2\2lo\3\2\2\2mk\3\2\2\2mn\3\2\2\2np\3\2\2\2om\3"+
		"\2\2\2pr\7\60\2\2qs\5\7\4\2rq\3\2\2\2st\3\2\2\2tr\3\2\2\2tu\3\2\2\2u\177"+
		"\3\2\2\2vx\t\2\2\2wy\7/\2\2xw\3\2\2\2xy\3\2\2\2y{\3\2\2\2z|\5\7\4\2{z"+
		"\3\2\2\2|}\3\2\2\2}{\3\2\2\2}~\3\2\2\2~\u0080\3\2\2\2\177v\3\2\2\2\177"+
		"\u0080\3\2\2\2\u0080\6\3\2\2\2\u0081\u0082\4\62;\2\u0082\b\3\2\2\2\u0083"+
		"\u0084\7e\2\2\u0084\u0085\7q\2\2\u0085\u0086\7u\2\2\u0086\n\3\2\2\2\u0087"+
		"\u0088\7u\2\2\u0088\u0089\7k\2\2\u0089\u008a\7p\2\2\u008a\f\3\2\2\2\u008b"+
		"\u008c\7v\2\2\u008c\u008d\7c\2\2\u008d\u008e\7p\2\2\u008e\16\3\2\2\2\u008f"+
		"\u0090\7c\2\2\u0090\u0091\7v\2\2\u0091\u0092\7c\2\2\u0092\u0093\7p\2\2"+
		"\u0093\20\3\2\2\2\u0094\u0095\7c\2\2\u0095\u0096\7e\2\2\u0096\u0097\7"+
		"q\2\2\u0097\u0098\7u\2\2\u0098\22\3\2\2\2\u0099\u009a\7c\2\2\u009a\u009b"+
		"\7u\2\2\u009b\u009c\7k\2\2\u009c\u009d\7p\2\2\u009d\24\3\2\2\2\u009e\u009f"+
		"\7u\2\2\u009f\u00a0\7k\2\2\u00a0\u00a1\7p\2\2\u00a1\u00a2\7j\2\2\u00a2"+
		"\26\3\2\2\2\u00a3\u00a4\7e\2\2\u00a4\u00a5\7q\2\2\u00a5\u00a6\7u\2\2\u00a6"+
		"\u00a7\7j\2\2\u00a7\30\3\2\2\2\u00a8\u00a9\7v\2\2\u00a9\u00aa\7c\2\2\u00aa"+
		"\u00ab\7p\2\2\u00ab\u00ac\7j\2\2\u00ac\32\3\2\2\2\u00ad\u00ae\7e\2\2\u00ae"+
		"\u00af\7q\2\2\u00af\u00b0\7v\2\2\u00b0\34\3\2\2\2\u00b1\u00b2\7n\2\2\u00b2"+
		"\u00b3\7p\2\2\u00b3\36\3\2\2\2\u00b4\u00b5\7n\2\2\u00b5\u00b6\7q\2\2\u00b6"+
		"\u00b7\7i\2\2\u00b7 \3\2\2\2\u00b8\u00b9\7c\2\2\u00b9\u00ba\7d\2\2\u00ba"+
		"\u00bb\7u\2\2\u00bb\"\3\2\2\2\u00bc\u00bd\7u\2\2\u00bd\u00be\7s\2\2\u00be"+
		"\u00bf\7t\2\2\u00bf\u00c0\7v\2\2\u00c0$\3\2\2\2\u00c1\u00c2\7e\2\2\u00c2"+
		"\u00c3\7d\2\2\u00c3\u00c4\7t\2\2\u00c4\u00c5\7v\2\2\u00c5&\3\2\2\2\u00c6"+
		"\u00c7\7u\2\2\u00c7\u00c8\7s\2\2\u00c8\u00c9\7t\2\2\u00c9(\3\2\2\2\u00ca"+
		"\u00cb\7e\2\2\u00cb\u00cc\7w\2\2\u00cc\u00cd\7d\2\2\u00cd\u00ce\7g\2\2"+
		"\u00ce*\3\2\2\2\u00cf\u00d0\7e\2\2\u00d0\u00d1\7g\2\2\u00d1\u00d2\7k\2"+
		"\2\u00d2\u00d3\7n\2\2\u00d3,\3\2\2\2\u00d4\u00d5\7h\2\2\u00d5\u00d6\7"+
		"n\2\2\u00d6\u00d7\7q\2\2\u00d7\u00d8\7q\2\2\u00d8\u00d9\7t\2\2\u00d9."+
		"\3\2\2\2\u00da\u00db\7o\2\2\u00db\u00dc\7c\2\2\u00dc\u00dd\7z\2\2\u00dd"+
		"\60\3\2\2\2\u00de\u00df\7o\2\2\u00df\u00e0\7k\2\2\u00e0\u00e1\7p\2\2\u00e1"+
		"\62\3\2\2\2\u00e2\u00e3\7r\2\2\u00e3\u00e6\7k\2\2\u00e4\u00e6\7g\2\2\u00e5"+
		"\u00e2\3\2\2\2\u00e5\u00e4\3\2\2\2\u00e6\64\3\2\2\2\u00e7\u00e8\7u\2\2"+
		"\u00e8\u00e9\7w\2\2\u00e9\u00ea\7o\2\2\u00ea\66\3\2\2\2\u00eb\u00ec\7"+
		"r\2\2\u00ec\u00ed\7t\2\2\u00ed\u00ee\7q\2\2\u00ee\u00ef\7f\2\2\u00ef8"+
		"\3\2\2\2\u00f0\u00f1\7x\2\2\u00f1\u00f2\7c\2\2\u00f2\u00f3\7t\2\2\u00f3"+
		":\3\2\2\2\u00f4\u00f8\5_\60\2\u00f5\u00f7\5a\61\2\u00f6\u00f5\3\2\2\2"+
		"\u00f7\u00fa\3\2\2\2\u00f8\u00f6\3\2\2\2\u00f8\u00f9\3\2\2\2\u00f9<\3"+
		"\2\2\2\u00fa\u00f8\3\2\2\2\u00fb\u00fc\7/\2\2\u00fc\u00fd\7@\2\2\u00fd"+
		">\3\2\2\2\u00fe\u00ff\7>\2\2\u00ff@\3\2\2\2\u0100\u0101\7>\2\2\u0101\u0102"+
		"\7?\2\2\u0102B\3\2\2\2\u0103\u0104\7@\2\2\u0104D\3\2\2\2\u0105\u0106\7"+
		"@\2\2\u0106\u0107\7?\2\2\u0107F\3\2\2\2\u0108\u0109\7?\2\2\u0109\u010a"+
		"\7?\2\2\u010aH\3\2\2\2\u010b\u010c\7,\2\2\u010cJ\3\2\2\2\u010d\u010e\7"+
		"\61\2\2\u010eL\3\2\2\2\u010f\u0110\7\'\2\2\u0110N\3\2\2\2\u0111\u0112"+
		"\7-\2\2\u0112P\3\2\2\2\u0113\u0114\7/\2\2\u0114R\3\2\2\2\u0115\u0116\7"+
		"`\2\2\u0116T\3\2\2\2\u0117\u0118\7*\2\2\u0118V\3\2\2\2\u0119\u011a\7+"+
		"\2\2\u011aX\3\2\2\2\u011b\u011c\7]\2\2\u011cZ\3\2\2\2\u011d\u011e\7_\2"+
		"\2\u011e\\\3\2\2\2\u011f\u0120\7.\2\2\u0120^\3\2\2\2\u0121\u0126\t\3\2"+
		"\2\u0122\u0126\n\4\2\2\u0123\u0124\t\5\2\2\u0124\u0126\t\6\2\2\u0125\u0121"+
		"\3\2\2\2\u0125\u0122\3\2\2\2\u0125\u0123\3\2\2\2\u0126`\3\2\2\2\u0127"+
		"\u012a\t\7\2\2\u0128\u012a\5_\60\2\u0129\u0127\3\2\2\2\u0129\u0128\3\2"+
		"\2\2\u012ab\3\2\2\2\u012b\u012c\t\b\2\2\u012c\u012d\3\2\2\2\u012d\u012e"+
		"\b\62\2\2\u012ed\3\2\2\2\r\2hmtx}\177\u00e5\u00f8\u0125\u0129\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}