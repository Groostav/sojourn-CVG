package com.empowerops.babel;

import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;

import java.util.BitSet;
import java.util.logging.Logger;

/**
 * Created by Geoff on 2015-08-21.
 */
public class BailLexerErrorStrategy extends LoggingErrorStrategy {

    private static final Logger log = Logger.getLogger(BailLexerErrorStrategy.class.getCanonicalName());

    public static class LexerRecognitionException extends RuntimeException {

        private static final long serialVersionUID = 8739849222093704987L;

        public LexerRecognitionException(String message, Throwable cause) {
            super(message, cause);
        }
    }

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
        throw new LexerRecognitionException(msg, e);
    }
    @Override
    public void reportAmbiguity(Parser parser, DFA dfa, int i, int i1, boolean b, BitSet bitSet, ATNConfigSet atnConfigSet) {
        super.reportAmbiguity(parser, dfa, i, i1, b, bitSet, atnConfigSet);
    }
    @Override
    public void reportAttemptingFullContext(Parser parser, DFA dfa, int i, int i1, BitSet bitSet, ATNConfigSet atnConfigSet) {
        super.reportAttemptingFullContext(parser, dfa, i, i1, bitSet, atnConfigSet);
    }
    @Override
    public void reportContextSensitivity(Parser parser, DFA dfa, int i, int i1, int i2, ATNConfigSet atnConfigSet) {
        super.reportContextSensitivity(parser, dfa, i, i1, i2, atnConfigSet);
    }
}

