package com.empowerops.babel;

import com.empowerops.problem_definition.babel.BabelCompiler.CompilerException;
import com.empowerops.common.ReflectionUtilities;
import com.empowerops.jargon.model.VariableSymbol;
import com.empowerops.linqalike.LinqingMap;
import com.empowerops.linqalike.Queryable;
import com.empowerops.linqalike.common.Formatting;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.Map;

import static com.empowerops.common.ReflectionUtilities.castOrFailNicely;

/**
 * Created by Justin Casol on 1/13/2015.
 */
public class RunningBabelCodeMap {

    private final LinqingMap<ParseTree, Executable> codeByNode  = new LinqingMap<>();

    private boolean locked;

    void putExecutable(ParseTree nodeKey, Executable executable)                             { codeByNode.put(nodeKey, executable); }
    void putExecutable(ParseTree nodeKey, ContextFreeExecutable executable)                  { codeByNode.put(nodeKey, executable); }
    void putExecutable(ParseTree nodeKey, ContextFreeSymbolRetrievingExecutable executable)  { codeByNode.put(nodeKey, executable); }
    void putExecutable(ParseTree nodeKey, ContextFreeNumericExecutable executable)           { codeByNode.put(nodeKey, executable); }
    void putExecutable(ParseTree nodeKey, NumericOperation executable)                       { codeByNode.put(nodeKey, executable); }
    void putExecutable(ParseTree nodeKey, UnaryIntegerOperation operation)                   { codeByNode.put(nodeKey, operation); }
    void putExecutable(ParseTree nodeKey, UnaryDecimalOperation operation)                   { codeByNode.put(nodeKey, operation); }
    void putExecutable(ParseTree nodeKey, BinaryDecimalOperation operation)                  { codeByNode.put(nodeKey, operation); }
    void putExecutable(ParseTree nodeKey, AggregateOperation operation)                      { codeByNode.put(nodeKey, operation); }

    ContextFreeNumericExecutable contextFreeNumericExecutable(ParseTree nodeKey) {
        return getOrThrowLocalized(ContextFreeNumericExecutable.class, nodeKey);
    }

    ContextFreeExecutable contextFreeExecutable(ParseTree nodeKey) {
        return getOrThrowLocalized(ContextFreeExecutable.class, nodeKey);
    }

    NumericOperation numericOperation(ParseTree operationNodeKey) {
        return getOrThrowLocalized(NumericOperation.class, operationNodeKey);
    }

    public Executable executable(ParseTree nodeKey) {
        return codeByNode.getValueFor(nodeKey);
    }

    /**
     * Base interface for a runnable expression chunk on OASIS.
     * All portions of an expression, at any level, are executable.
     *
     * <p>The {@link ContextFreeExecutable} derivatives are <code>Executables</code> who have been supplied
     * arguments, and thus do not need any args passed in (infact they'll thrown an exception if you pass
     * non-empty set of arguments in)
     *
     * <p>The {@link NumericOperation} derrivatives are <code>Executables</code> that still require arguments
     * and also yield a numeric result.
     */
    @FunctionalInterface
    public interface Executable {
        Object execute(Queryable<ContextFreeExecutable> args);
    }

    /**
     * Base interface for expressions that have a numeric result. <i>most</i> expressions are numeric,
     * such as arithmatic, sums, etc.
     */
    @FunctionalInterface
    public interface NumericOperation extends Executable {

        @Override
        Number execute(Queryable<ContextFreeExecutable> args);
    }

    /**
     * Base interface for what is effectively a getter. Each expression node closes the operation nodes by
     * supplying it with arguments. The result is a ContextFreeExecutable (an executable that can be evaluated
     * without arguments, as its arguments have alreayd beenb specified).
     */
    @FunctionalInterface
    public interface ContextFreeExecutable extends Executable {

        Object execute();

        @Override
        default Object execute(Queryable<ContextFreeExecutable> args){
            if(args.any()) { throw new IllegalStateException(); }

            return execute();
        }
    }

    /**
     * Specialization of {@link ContextFreeExecutable} to deal with code that gets back a Variable Symbol,
     * such as the variable declaration portion of an expression lambda. (the 'i' in <code>i -> (3*x1)^2...</code> )
     */
    @FunctionalInterface
    public interface ContextFreeSymbolRetrievingExecutable extends ContextFreeExecutable {

        @Override
        VariableSymbol execute();

        @Override
        default VariableSymbol execute(Queryable<ContextFreeExecutable> args){
            if(args.any()) { throw new IllegalStateException(); }

            return execute();
        }
    }

    /**
     * Specialization of {@link ContextFreeExecutable} that gets a numeric result. Can be an integer or double.
     */
    @FunctionalInterface
    public interface ContextFreeNumericExecutable extends ContextFreeExecutable, NumericOperation{

        @Override
        Number execute();

        @Override
        default Number execute(Queryable<ContextFreeExecutable> args){
            return execute();
        }
    }

    /**
     * Specialization of {@link NumericOperation} for <code>sum</code> and <code>prod</code>.
     */
    @FunctionalInterface
    public interface AggregateOperation extends NumericOperation{

        double execute(int lowerBound, int upperBound, ContextFreeNumericExecutable subExpression);

        @Override
        default Number execute(Queryable<ContextFreeExecutable> args) {
            assert args.count() == 3 : "aggregate operation should have 3 closures as args, but was: " + args.toList();
            int lower = convertToIntOrFailNicely(args.first().execute());
            int upper = convertToIntOrFailNicely(args.second().execute());
            ContextFreeNumericExecutable subExpression = castOrFailNicely(ContextFreeNumericExecutable.class, args.last());

            return execute(lower, upper, subExpression);
        }
    }

    /**
     * Specialization of {@link NumericOperation} for operations that take one decimal argument
     */
    @FunctionalInterface
    public interface UnaryDecimalOperation extends NumericOperation {

        double execute(double expr);

        @Override
        default Number execute(Queryable<ContextFreeExecutable> args) {
            double arg = convertToDoubleOrFailNicely(args.single().execute());
            return execute(arg);
        }
    }

    /**
     * Specialization of {@link NumericOperation} for operations that take one integer argument
     */
    @FunctionalInterface
    interface UnaryIntegerOperation extends NumericOperation {

        Number execute(int expr);

        @Override
        default Number execute(Queryable<ContextFreeExecutable> args) {
            int arg = convertToIntOrFailNicely(args.single().execute());
            return execute(arg);
        }
    }

    /**
     * Specialization of {@link NumericOperation} for operations that take two decimal arguments
     */
    @FunctionalInterface
    interface BinaryDecimalOperation extends NumericOperation {

        double execute(double left, double right);

        @Override
        default Number execute(Queryable<ContextFreeExecutable> args) {
            assert args.size() == 2 : "binary decimal op had more than 2 args: " + args.toList();
            double leftArg = convertToDoubleOrFailNicely(args.first().execute());
            double rightArg = convertToDoubleOrFailNicely(args.last().execute());
            return execute(leftArg, rightArg);
        }

    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder("babel Code Map {").append("\n");

        for (Map.Entry<ParseTree, Executable> nodeValuePair : codeByNode) {
            builder.append(nodeValuePair.getKey().getClass().getSimpleName());
            builder.append("@");
            builder.append(Formatting.postLimitCharacters(10, nodeValuePair.getKey().getText()));
            builder.append(" -> ");
            builder.append(ReflectionUtilities.getSimpleHumanReadableName(nodeValuePair.getValue()));
            builder.append(":");
            try {
                locked = true;
                builder.append(nodeValuePair.getValue() instanceof ContextFreeExecutable
                                ? ((ContextFreeExecutable) nodeValuePair.getValue()).execute()
                                : "[open " + nodeValuePair.getKey().getParent().getText() + " ]"
                );
            }
            catch(Exception e){
                builder.append("[Error evaluating exectuable '").append(e.getClass().getSimpleName()).append("'");
            }
            finally{
                locked = false;
            }
            builder.append("\n" + "\t");
        }

        builder.replace(builder.lastIndexOf("\t"), builder.length(), "");

        builder.replace(builder.lastIndexOf("\n" + "\t"), builder.length(), "");
        return builder.toString();
    }

    private <TNeeded extends Executable> TNeeded getOrThrowLocalized(Class<TNeeded> desiredExecutableType,
                                                                     ParseTree nodeToGetCodeFor) {
        if(locked){
            throw new IllegalStateException();
        }
        if(codeByNode.containsKey(nodeToGetCodeFor)) try {
            return desiredExecutableType.cast(codeByNode.getValueFor(nodeToGetCodeFor));
        }
        catch (ClassCastException exception){
            String message = ReflectionUtilities.getTypeErrorMessage(
                    codeByNode.getValueFor(nodeToGetCodeFor),
                    desiredExecutableType,
                    nodeToGetCodeFor.getClass().getSimpleName() + ":" + nodeToGetCodeFor.getText()
            );
            throw new CompilerException(message, this, exception);
        }
        else{
            throw new CompilerException(
                    "dont have any code for '" + nodeToGetCodeFor.getText() + "'",
                    this
            );
        }
    }

    private static double convertToDoubleOrFailNicely(Object valueToConvert){
        if(valueToConvert instanceof Integer){
            return ((Integer) valueToConvert).doubleValue();
        }
        else{
            return castOrFailNicely(Double.class, valueToConvert);
        }
    }

    private static int convertToIntOrFailNicely(Object valueToConvert){
        if(valueToConvert instanceof Double){
            //TODO type system to allow (and separate) Double from Integer?
            return (int) Math.round((double) valueToConvert);
        }
        else{
            return castOrFailNicely(Integer.class, valueToConvert);
        }
    }
}