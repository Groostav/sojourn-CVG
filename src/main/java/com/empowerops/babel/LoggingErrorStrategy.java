package com.empowerops.babel;

import org.antlr.v4.runtime.ANTLRErrorListener;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;

import java.util.BitSet;
import java.util.logging.Logger;

/**
 * Created by Geoff on 4/23/2016.
 */
public class LoggingErrorStrategy implements ANTLRErrorListener {

    private static final Logger log = Logger.getLogger(LoggingErrorStrategy.class.getCanonicalName());

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
        log.warning("error with " + recognizer.getGrammarFileName() + ", line " + line + ":" + charPositionInLine + " " + msg);
    }
    @Override
    public void reportAmbiguity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, boolean exact, BitSet ambigAlts, ATNConfigSet configs) {
        log.warning("saw ambiguity in " + recognizer.getGrammarFileName());
    }
    @Override
    public void reportAttemptingFullContext(Parser recognizer, DFA dfa, int startIndex, int stopIndex, BitSet conflictingAlts, ATNConfigSet configs) {

    }
    @Override
    public void reportContextSensitivity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, int prediction, ATNConfigSet configs) {

    }
}
