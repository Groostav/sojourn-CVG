package com.empowerops.babel;

import com.empowerops.common.ReflectionUtilities;
import com.empowerops.linqalike.LinqingMap;
import com.empowerops.linqalike.QueryableMap;

import static com.empowerops.common.ReflectionUtilities.getStaticFieldValue;
import static java.lang.Math.tan;

/**
 * Class to adapt simple algebra within java into an executable & babel-consumable form.
 *
 * <p>Strategy here is to first consult a couple maps looking for the value or operation,
 * then dump the problem on Java.lang.Math to look up functions defined in the grammar but not
 * in the custom maps.
 */
public class RuntimeNumerics {

    private static final QueryableMap<String, RunningBabelCodeMap.UnaryDecimalOperation> additionalUnaryOpsByName = new LinqingMap<String, RunningBabelCodeMap.UnaryDecimalOperation>() {{
        put("cot", arg -> 1 / tan(arg));
        put("sqr", arg -> arg * arg);
        put("cube", arg -> arg * arg * arg);
        put("ln", Math::log); //dont like that 'log' is the natural logarithm and 'log10' is log base 10
        put("log", Math::log10);
    }};

    public Number findValueForConstant(String constantName) {
        return getStaticFieldValue(Math.class, constantName.toUpperCase());
    }

    public RunningBabelCodeMap.UnaryDecimalOperation findUnaryFunctionNamed(String functionName) {
        if (additionalUnaryOpsByName.containsTKey(functionName)) {
            return additionalUnaryOpsByName.getValueFor(functionName);
        }
        else {
            return wrap(
                    functionArg -> ReflectionUtilities.runStaticMethodReflectively(Math.class, functionName, functionArg),
                    "arg -> Math." + functionName + "(" + "arg" + ")"
            );
        }
    }

    public RunningBabelCodeMap.BinaryDecimalOperation findBinaryFunctionNamed(String functionName) {
        if (functionName.equals("log")) {
            return wrap((base, number) -> Math.log(number) / Math.log(base), "(base, number) -> Math.log(base, number)");
        }
        return wrap(
                (left, right) -> ReflectionUtilities.runStaticMethodReflectively(Math.class, functionName, left, right),
                "(left, right) -> Math." + functionName + "(" + "left" + ", " + "right" + ")"
        );
    }

    public static final RunningBabelCodeMap.UnaryDecimalOperation  Inversion      = wrap(arg -> - 1 * arg, "arg -> -1 * arg");
    public static final RunningBabelCodeMap.BinaryDecimalOperation Addition       = wrap((l, r) -> l + r, "(left, right) -> left + right");
    public static final RunningBabelCodeMap.BinaryDecimalOperation Subtraction    = wrap((l, r) -> l - r, "(left, right) -> left - right");
    public static final RunningBabelCodeMap.BinaryDecimalOperation Multiplication = wrap((l, r) -> l * r, "(left, right) -> left * right");
    public static final RunningBabelCodeMap.BinaryDecimalOperation Division       = wrap((l, r) -> l / r, "(left, right) -> left / right");
    public static final RunningBabelCodeMap.BinaryDecimalOperation Exponentiation = wrap(Math::pow, "(left, right) -> Math.pow(left, right)");
    public static final RunningBabelCodeMap.BinaryDecimalOperation Modulo         = wrap((l, r) -> l % r, "(left, right) -> left % right");

    private static RunningBabelCodeMap.BinaryDecimalOperation wrap(RunningBabelCodeMap.BinaryDecimalOperation operation, String description) {
        return new RunningBabelCodeMap.BinaryDecimalOperation() {
            @Override public double execute(double left, double right) {
                return operation.execute(left, right);
            }

            @Override public String toString() {
                return description;
            }
        };
    }

    private static RunningBabelCodeMap.UnaryDecimalOperation wrap(RunningBabelCodeMap.UnaryDecimalOperation operation, String description) {
        return new RunningBabelCodeMap.UnaryDecimalOperation() {
            @Override public double execute(double arg) {
                return operation.execute(arg);
            }

            @Override public String toString() {
                return description;
            }
        };
    }

}
