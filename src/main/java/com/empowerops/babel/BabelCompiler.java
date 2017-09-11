package com.empowerops.babel;

import com.empowerops.babel.todo_deleteme.BabelLexer;
import com.empowerops.babel.todo_deleteme.BabelParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import javax.annotation.Nonnull;
import javax.inject.Inject;
import java.util.HashSet;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

import static java.util.logging.Level.CONFIG;

/**
 * Created by Geoff on 2015-10-14.
 */
public class BabelCompiler implements EvaluableCompiler{

    private static final Logger log = Logger.getLogger(BabelCompiler.class.getCanonicalName());

    public static class CompilationResult {

        public static final CompilationResult NullInstance = new Null();

        protected final Set<BabelExpressionProblem> problems = new HashSet<>();

        protected SymbolTable                                      symbolTable;
        protected RunningBabelCodeMap.ContextFreeNumericExecutable executable;
        protected boolean                                          booleanExpression = false;

        public Set<BabelExpressionProblem> getProblems() {
            return problems;
        }
        public SymbolTable getSymbolTable() {
            return symbolTable;
        }

        public RunningBabelCodeMap.ContextFreeNumericExecutable getExecutable() {
            return executable;
        }


        public static class Null extends CompilationResult {
            public Null() {
                symbolTable = new SymbolTable();
                getSymbolTable().freeze();
            }

            @Override public Queryable<BabelExpressionProblem> getProblems() {
                return from(new BabelExpressionProblem("[null executable]", null));
            }
        }
    }

    private final ParseTreeWalker walker = new ParseTreeWalker();

    @Inject
    public BabelCompiler() {
    }

    public boolean isLegalVariableName(@Nonnull String variableName) {
        CompilationResult result = compile(variableName, BabelParser::variable_only);
        return result.getProblems().isEmpty();
    }

    public CompilationResult compile(String functionLiteral) {
        return compile(functionLiteral, BabelParser::expression);
    }

    /**
     * Generates a babel expression for the supplied output symbol with the specified function literal.
     * <p>
     * <p>This call will always return a new babel expression,
     * regardless of whether or not the function literal contains errors. In the event the supplied
     * function literal does have problems, they can be accessed by calling {@link BabelExpression#getErrors()}
     *
     * @param resultSymbol    the result symbol for the resulting expression
     * @param expressionLiteral the literal text of the expression to be compiled
     * @return a new babel expression for the corresponding result var and function literal,
     * possibly containing errors.
     */
    @Nonnull public BabelExpression compile(@Nonnull VariableSymbol resultSymbol, @Nonnull String expressionLiteral) {
        CompilationResult compilation = compile(expressionLiteral, BabelParser::expression);
        return new BabelExpression(resultSymbol, expressionLiteral, compilation);
    }
    /**
     * Compiles the supplied string into an executable babel expression,
     * or generates a list of errors if no such executable could be created.
     */
    // synchronized out of an abundance of caution (as it was the root of the problem in #869)
    // there's no necessity for this method to complete quickly and
    // it is called from a number of different threading contexts,
    // which is begging for hiesen bugs. Right now this method is referentially transparent
    // (it doesn't modify any state, so there's no state for concurrency to corrupt)
    // but that's not good enough in my books, so we'll use a mutex to make sure.
    // request for testing written up in #900
    private synchronized CompilationResult compile(String sourceText, Func1<BabelParser, ParseTree> parseCall) {
        if(sourceText == null) { throw new IllegalArgumentException("sourceText"); }

        CompilationResult result = new CompilationResult();

        if ( ! sourceText.isEmpty()) try {
            BabelParser parser = setupTokenizerAndParser(sourceText);

            log.log(CONFIG, () -> "compiling expression '" + sourceText + "'");
            ParseTree currentRoot = parseCall.getFrom(parser);
            log.log(CONFIG, () -> "done compiling expression, got '" + currentRoot.toStringTree(parser) + "'");

            SyntaxErrorFindingWalker syntaxErrorFinder = walk(currentRoot, new SyntaxErrorFindingWalker());
            result.problems.addAll(syntaxErrorFinder.getErrors());

            BooleanRewritingWalker booleanRewritingWalker = walk(currentRoot, new BooleanRewritingWalker());
            result.booleanExpression = booleanRewritingWalker.isBooleanExpression();

            SymbolTableBuildingWalker symbolTableBuildingWalker = walk(currentRoot, new SymbolTableBuildingWalker());
            SymbolTable symbolTable = symbolTableBuildingWalker.getTable();
            symbolTable.freeze();
            result.problems.addAll(symbolTableBuildingWalker.getSemanticProblems());
            result.symbolTable = symbolTable;

            CodeGeneratingWalker codeGenerator = walk(currentRoot, new CodeGeneratingWalker(result.symbolTable));
            result.executable = codeGenerator.getRootExecutor();
        }
        catch (Exception compilationException) {
            result.symbolTable = new SymbolTable();
            result.symbolTable.freeze();
            log.log(
                    Level.FINE,
                    "compilation exception",
                    compilationException
            );
            result.problems.add(new BabelExpressionProblem(
                    compilationException.getMessage() == null ?
                            "compiler failure" :
                            "compiler failure: " + compilationException.getMessage(),
                    null
            ));
        }
        else {
            result.symbolTable = new SymbolTable();
            result.symbolTable.freeze();
            result.problems.add(new BabelExpressionProblem(
                    "expression is empty",
                    null
            ));
        }
        return result;
    }

    private BabelParser setupTokenizerAndParser(String functionLiteral) {
        ANTLRInputStream antlrStringStream = new ANTLRInputStream(functionLiteral);
        BabelLexer lexer = new BabelLexer(antlrStringStream);
        lexer.removeErrorListeners();
        lexer.addErrorListener(new BailLexerErrorStrategy());
        TokenStream tokens = new CommonTokenStream(lexer);
        BabelParser babelParser = new BabelParser(tokens);
        babelParser.setErrorHandler(new BailErrorStrategy());
        return babelParser;
    }

    private <TWalker extends ParseTreeListener> TWalker walk(ParseTree treeToWalk, TWalker walkListener) {
        walker.walk(walkListener, treeToWalk);
        return walkListener;
    }

    public static class CompilerException extends RuntimeException {

        private static final long serialVersionUID = - 7959984867193274534L;

        public CompilerException(String message, RunningBabelCodeMap babelCodeMap) {
            super(message + "\n" + babelCodeMap.toString());
        }

        public CompilerException(String message, RunningBabelCodeMap babelCodeMap, Exception instigator) {
            super(message + "\n" + babelCodeMap.toString(), instigator);
        }

    }
}
