package com.empowerops.babel;

import com.empowerops.common.documentation.Ordered;
import com.empowerops.common.documentation.WrittenOnce;
import com.empowerops.linqalike.*;
import com.empowerops.problem_definition.parser.BabelParser;
import kotlin.collections.EmptyIterator;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.Map;

import static com.empowerops.linqalike.Factories.*;
import static java.lang.Double.isNaN;

/**
* Created by Justin Casol on 2/2/2015.
*/
public class SymbolTable {

    /**
     * marker value for a symbol table entry that has been reserved but not yet assigned.
     *
     * For example, in the middle of execution we will hit a stage where the compiler knows the variable 'i'
     * for a sum exists, but does not yet have a value for it. In such a case, an entry in the symbol table
     * 'i' -> OCCUPIED will be created.
     */
    private static final double OCCUPIED = Double.NaN;

    /**
     * Used as a key into the scope map, this is the node that the optimization variable symbols are defined under.
     * Rather than call one of ANTLR's icky constructor, we're just going to have our map contain an entry for
     * the null key --which is supported, even if its a little unusual.
     */
    static final RuleContext StaticVariableScopeKey = null;

    /**
     * Map of scopes keys (a parse tree node) to scopes (map of symbols to values).
     *
     * <p>this map will typically look like this,
     * for an expression that contains one 'sum' expression, using the variable 'i'
     * <pre>{@code
     * null ->
     *      x1 -> 12
     *      x2 -> 23
     *      x3 -> 45
     *      f1 -> 2.345
     *      //... other values from the cheap point.
     * sumSubExprContext ->
     *      i -> 5 //the current value for i
     * }</pre>
     *
     * <p>if our users were inclined to use a particularly annoying loop variable called 'x1'
     * (which would lead to a collision between the loop variable x1 and the optimization variable x1)
     * we would see this:
     *
     * <pre>{@code
     * null ->
     *      x1 -> 12
     *      x2 -> 23
     *      x3 -> 45
     *      f1 -> 2.345
     *      //... other values from the cheap point.
     * sumSubExprContext ->
     *      x1 -> 5 //the current value for x1 in the loop
     * }</pre>
     */
    private final LinqingMap<ParseTree, LinqingMap<String, Number>> symbolTablesByScope = new LinqingMap<>();
    private final LinqingSet<String> staticallyKnownSymbols = new LinqingSet<>();

    private boolean frozen = false;
    private boolean containsDynamicVarLookup;

    private QueryableMap<String, Number> getAggregateTable() {
        return symbolTablesByScope
                .rights()
                .<BiQueryable<String, Number>>unsafeCast()
                .aggregate(Factories.<String, Number>emptyBiQuery(), BiQueryable::union)
                .toMap();
    }

    public SymbolTable() {
        symbolTablesByScope.put(StaticVariableScopeKey, new LinqingMap<>());
    }

    public void setAsStaticScope(@Ordered("as per var[] order") QueryableMap<String, Double> newCoordinateValues) {
        if ( ! isFrozen()) { throw new IllegalStateException("compilation not yet finished"); }
        assert newCoordinateValues.keySet().isSupersetOf(staticallyKnownSymbols);

        //please note: we do nothing to preserve order here.
        LinqingMap<String, Number> staticScope = symbolTablesByScope.get(StaticVariableScopeKey);

        staticScope.clear();
        staticScope.addAll(newCoordinateValues.<Number>castValues());
    }

    public void clearCheapPointScope(){
        if ( ! isFrozen()) { throw new IllegalStateException("compilation not yet finished"); }

        LinqingMap<String, Number> cheapPointScope = symbolTablesByScope.get(SymbolTable.StaticVariableScopeKey);

        cheapPointScope.clear();
        staticallyKnownSymbols.forEach(key -> cheapPointScope.put(key, OCCUPIED));
    }

    public void declareSymbol(ParseTree scope, String symbol){
        assert scope instanceof BabelParser.LambdaExprContext;
        assert ! isFrozen();

        LinqingMap<String, Number> table = symbolTablesByScope.getOrMake(scope, LinqingMap::new);

        if(table.containsTKey(symbol)){
            throw new IllegalArgumentException(
                    "the scope for '" + scope + "' is full " +
                    "(already contains a declaration for '" + table.single().getKey() + ")"
            );
        }
        else{
            table.put(symbol, OCCUPIED);
        }
    }

    public void registerSymbolUsage(ParseTree scope, String symbol) {
        assert ! isFrozen();

        ParseTree scopeToTest = scope;
        do{
            if(getSymbolesDeclaredIn(scopeToTest).containsElement(symbol)){ return; }
            scopeToTest = scopeToTest.getParent();
        } while (scopeToTest != null);

        while( ! isNestedScope(scope) || scopeIsFull(scope)){
            scope = scope.getParent();
        }

        LinqingMap<String, Number> tableForScope = symbolTablesByScope.getOrMake(scope, LinqingMap::new);

        tableForScope.put(symbol, OCCUPIED);
        if(isStaticScope(scope)){
            staticallyKnownSymbols.add(symbol);
        }
    }

    private boolean scopeIsFull(ParseTree scope) {
        if(scope == StaticVariableScopeKey){
            return false;
        }
        if(getSymbolesDeclaredIn(scope).isEmpty()){
            return false;
        }
        return true;
    }

    private boolean isNestedScope(ParseTree scopeKey) {
        return scopeKey == StaticVariableScopeKey || scopeKey instanceof BabelParser.LambdaExprContext;
    }
    private boolean isStaticScope(ParseTree scopeKey) {
        return scopeKey == StaticVariableScopeKey;
    }

    public void setSymbolValue(ParseTree mostLocalScope, String symbol, Number value) {

        boolean madeEntry = false;
        for(ParseTree currentScope = mostLocalScope; currentScope != null; currentScope = currentScope.getParent()){

            if (! symbolTablesByScope.containsTKey(mostLocalScope)) { continue; }

            LinqingMap<String, Number> table = symbolTablesByScope.getValueFor(mostLocalScope);
            if( ! table.containsTKey(symbol)){ continue; }

            table.put(symbol, value);
            madeEntry = true;
            break;
        }

        if( ! madeEntry){
            throw new IllegalArgumentException("the symbol " + symbol + " has not yet been entered in the symbol table");
        }
    }


    public Number findLocalValueFor(ParseTree localNode, String symbol) {
        Number result = searchFor(localNode, symbol);

        if (result != null && ! isNaN(result.doubleValue())){
            return result;
        }

        if(getAggregateTable().containsTKey(symbol)){
            throw new IllegalArgumentException(
                    "the symbol '" + symbol + "' is in the symbol table, " +
                    "but it was not yet assigned a value (is not accessible from?) " + nodeToString(localNode) + ", \n" +
                    this.toString()
            );
        }
        else {
            throw new IllegalArgumentException("the symbol '" + symbol + "' does not exist in the symbol table.");
        }
    }

    private Number searchFor(ParseTree localNode, String symbol) {
        Queryable<ParseTree> scopesToCheck = through(localNode, ParseTree::getParent).union(StaticVariableScopeKey);

        for(ParseTree scope : scopesToCheck){
            if(!!!symbolTablesByScope.containsTKey(scope)){
                continue;
            }
            QueryableMap<String, Number> candidateScope = symbolTablesByScope.getValueFor(scope);
            if(!!!candidateScope.containsTKey(symbol)){
                continue;
            }

            return candidateScope.getValueFor(symbol);
        }

        return null;
    }

    public double getSymbolForIndex(int index) {
        return getStaticScope().values().toList().get(index);
    }

    public boolean isFrozen() {
        return frozen;
    }

    public void freeze() {
        if(this.isFrozen()) { throw new IllegalStateException(); }
        this.frozen = true;
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder("SymbolTable {");

        for(Map.Entry<ParseTree, LinqingMap<String, Number>> scope : symbolTablesByScope) {
            builder.append("\n\t");
            builder.append("scope for '");
            builder.append(nodeToString(scope.getKey()));
            builder.append("' ");
            builder.append("{");
            for(Map.Entry<String, Number> entry : scope.getValue()){
                builder.append("\n\t\t");
                String symbolValue = isNaN(entry.getValue().doubleValue())
                        ? "[NaN; declared but not assigned]"
                        : entry.getValue().toString();

                builder.append(entry.getKey()).append(" -> ").append(symbolValue);
            }
            builder.append("\n\t}");
        }

        builder.append("\n}");
        return builder.toString();
    }

    public Queryable<String> getSymbolesDeclaredIn(ParseTree scope) {
        return symbolTablesByScope.containsTKey(scope) ? symbolTablesByScope.get(scope).keySet() : empty();
    }


    public Queryable<String> getStaticallyUsedSymbols(){
        if( ! isFrozen()){
            throw new IllegalStateException("babel compilation not yet finished; make sure freeze() is called first");
        }
        return staticallyKnownSymbols;
    }

    public QueryableMap<String, Double> getStaticScope() {
        return getTableFor(StaticVariableScopeKey).castValues();
    }

    private QueryableMap<String, Number> getTableFor(ParseTree scopeKey) {
        return symbolTablesByScope.getValueFor(scopeKey);
    }
    public boolean containsDynamicVarLookup() {
        return containsDynamicVarLookup;
    }
    void setContainsDynamicVarLookup(boolean containsDynamicVarLookup){
        this.containsDynamicVarLookup = containsDynamicVarLookup;
    }

    private static String nodeToString(ParseTree localNode) {
        if(localNode == StaticVariableScopeKey) { return "[Static Variable Scope]"; }
        if(localNode == null) { return "<null>"; }
        return localNode.getClass().getSimpleName() + ":" + localNode.getText() + localNode.toString();
    }
}
