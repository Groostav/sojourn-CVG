package com.empowerops.babel


import com.empowerops.babel.todo_deleteme.BabelParser
import org.antlr.v4.runtime.RuleContext
import org.antlr.v4.runtime.tree.ParseTree

import java.util.Collections
import java.util.HashMap
import java.util.HashSet

import java.lang.Double.isNaN

/**
 * Created by Justin Casol on 2/2/2015.
 */
class SymbolTable {

    /**
     * Map of scopes keys (a parse tree node) to scopes (map of symbols to values).
     *
     *
     * this map will typically look like this,
     * for an expression that contains one 'sum' expression, using the variable 'i'
     * <pre>`null ->
     * x1 -> 12
     * x2 -> 23
     * x3 -> 45
     * f1 -> 2.345
     * //... other values from the cheap point.
     * sumSubExprContext ->
     * i -> 5 //the current value for i
    `</pre> *
     *
     *
     * if our users were inclined to use a particularly annoying loop variable called 'x1'
     * (which would lead to a collision between the loop variable x1 and the optimization variable x1)
     * we would see this:
     *
     * <pre>`null ->
     * x1 -> 12
     * x2 -> 23
     * x3 -> 45
     * f1 -> 2.345
     * //... other values from the cheap point.
     * sumSubExprContext ->
     * x1 -> 5 //the current value for x1 in the loop
    `</pre> *
     */
    private val symbolTablesByScope = HashMap<ParseTree, Map<String, Number>>()
    private val staticallyKnownSymbols = HashSet<String>()

    var isFrozen = false
        private set
    private var containsDynamicVarLookup: Boolean = false

    private val aggregateTable: Map<String, Number>
        get() {
            return symbolTablesByScope
                    .rights()
                    .unsafeCast()
                    .aggregate(Factories.emptyBiQuery(), ???({ BiQueryable.union() }))
            .toMap()
        }

    init {
        symbolTablesByScope.put(StaticVariableScopeKey, Map<String, Number>())
    }

    fun setAsStaticScope(newCoordinateValues: Map<String, Double>) {
        if (!isFrozen) {
            throw IllegalStateException("compilation not yet finished")
        }
        assert(newCoordinateValues.keys.isSupersetOf(staticallyKnownSymbols))

        //please note: we do nothing to preserve order here.
        val staticScope = symbolTablesByScope.get(StaticVariableScopeKey)

        staticScope.clear()
        staticScope.addAll(newCoordinateValues.castValues<Number>())
    }

    fun clearCheapPointScope() {
        if (!isFrozen) {
            throw IllegalStateException("compilation not yet finished")
        }

        val cheapPointScope = symbolTablesByScope.get(SymbolTable.StaticVariableScopeKey)

        cheapPointScope.clear()
        staticallyKnownSymbols.forEach { key -> cheapPointScope.put(key, OCCUPIED) }
    }

    fun declareSymbol(scope: ParseTree, symbol: String) {
        assert(scope is BabelParser.LambdaExprContext)
        assert(!isFrozen)

        val table = symbolTablesByScope.getOrMake(scope, ???({ Map() }))

        if (table.containsKey(symbol)) {
            throw IllegalArgumentException(
                    "the scope for '" + scope + "' is full " +
                            "(already contains a declaration for '" + table.single().getKey() + ")"
            )
        } else {
            table.put(symbol, OCCUPIED)
        }
    }

    fun registerSymbolUsage(scope: ParseTree, symbol: String) {
        var scope = scope
        assert(!isFrozen)

        var scopeToTest: ParseTree? = scope
        do {
            if (getSymbolesDeclaredIn(scopeToTest).contains(symbol)) {
                return
            }
            scopeToTest = scopeToTest!!.parent
        } while (scopeToTest != null)

        while (!isNestedScope(scope) || scopeIsFull(scope)) {
            scope = scope.parent
        }

        val tableForScope = symbolTablesByScope.getOrMake(scope, ???({ Map() }))

        tableForScope.put(symbol, OCCUPIED)
        if (isStaticScope(scope)) {
            staticallyKnownSymbols.add(symbol)
        }
    }

    private fun scopeIsFull(scope: ParseTree): Boolean {
        if (scope === StaticVariableScopeKey) {
            return false
        }
        return if (getSymbolesDeclaredIn(scope).isEmpty()) {
            false
        } else true
    }

    private fun isNestedScope(scopeKey: ParseTree): Boolean {
        return scopeKey === StaticVariableScopeKey || scopeKey is BabelParser.LambdaExprContext
    }

    private fun isStaticScope(scopeKey: ParseTree): Boolean {
        return scopeKey === StaticVariableScopeKey
    }

    fun setSymbolValue(mostLocalScope: ParseTree, symbol: String, value: Number) {

        var madeEntry = false
        var currentScope: ParseTree? = mostLocalScope
        while (currentScope != null) {

            if (!symbolTablesByScope.containsKey(mostLocalScope)) {
                currentScope = currentScope.parent
                continue
            }

            val table = symbolTablesByScope[mostLocalScope]
            if (!table.containsKey(symbol)) {
                currentScope = currentScope.parent
                continue
            }

            table.put(symbol, value)
            madeEntry = true
            break
            currentScope = currentScope.parent
        }

        if (!madeEntry) {
            throw IllegalArgumentException("the symbol $symbol has not yet been entered in the symbol table")
        }
    }


    fun findLocalValueFor(localNode: ParseTree, symbol: String): Number {
        val result = searchFor(localNode, symbol)

        if (result != null && !isNaN(result.toDouble())) {
            return result
        }

        if (aggregateTable.containsKey(symbol)) {
            throw IllegalArgumentException(
                    "the symbol '" + symbol + "' is in the symbol table, " +
                            "but it was not yet assigned a value (is not accessible from?) " + nodeToString(localNode) + ", \n" +
                            this.toString()
            )
        } else {
            throw IllegalArgumentException("the symbol '$symbol' does not exist in the symbol table.")
        }
    }

    private fun searchFor(localNode: ParseTree, symbol: String): Number? {
        val scopesToCheck = through(localNode, ???({ getParent() })).union(StaticVariableScopeKey)

        for (scope in scopesToCheck) {
            if (!!!symbolTablesByScope.containsKey(scope)) {
                continue
            }
            val candidateScope = symbolTablesByScope[scope]
            if (!!!candidateScope.containsKey(symbol)) {
                continue
            }

            return candidateScope[symbol]
        }

        return null
    }

    fun getSymbolForIndex(index: Int): Double {
        return staticScope.values.toList()[index]
    }

    fun freeze() {
        if (this.isFrozen) {
            throw IllegalStateException()
        }
        this.isFrozen = true
    }

    override fun toString(): String {
        val builder = StringBuilder("SymbolTable {")

        for ((key, value) in symbolTablesByScope) {
            builder.append("\n\t")
            builder.append("scope for '")
            builder.append(nodeToString(key))
            builder.append("' ")
            builder.append("{")
            for ((key1, value1) in value) {
                builder.append("\n\t\t")
                val symbolValue = if (isNaN(value1.toDouble()))
                    "[NaN; declared but not assigned]"
                else
                    value1.toString()

                builder.append(key1).append(" -> ").append(symbolValue)
            }
            builder.append("\n\t}")
        }

        builder.append("\n}")
        return builder.toString()
    }

    fun getSymbolesDeclaredIn(scope: ParseTree): Set<String> {
        return if (symbolTablesByScope.containsKey(scope)) symbolTablesByScope[scope].keys else emptySet()
    }


    val staticScope: Map<String, Double>
        get() = getTableFor(StaticVariableScopeKey)

    private fun getTableFor(scopeKey: ParseTree?): Map<String, Number> {
        return symbolTablesByScope.get(scopeKey)
    }

    fun containsDynamicVarLookup(): Boolean {
        return containsDynamicVarLookup
    }

    fun setContainsDynamicVarLookup(containsDynamicVarLookup: Boolean) {
        this.containsDynamicVarLookup = containsDynamicVarLookup
    }

    companion object {

        /**
         * marker value for a symbol table entry that has been reserved but not yet assigned.
         *
         * For example, in the middle of execution we will hit a stage where the compiler knows the variable 'i'
         * for a sum exists, but does not yet have a value for it. In such a case, an entry in the symbol table
         * 'i' -> OCCUPIED will be created.
         */
        private val OCCUPIED = java.lang.Double.NaN

        /**
         * Used as a key into the scope map, this is the node that the optimization variable symbols are defined under.
         * Rather than call one of ANTLR's icky constructor, we're just going to have our map contain an entry for
         * the null key --which is supported, even if its a little unusual.
         */
        internal val StaticVariableScopeKey: RuleContext? = null

        private fun nodeToString(localNode: ParseTree?): String {
            if (localNode === StaticVariableScopeKey) {
                return "[Static Variable Scope]"
            }
            return if (localNode == null) {
                "<null>"
            } else localNode.javaClass.simpleName + ":" + localNode.text + localNode.toString()
        }
    }
}
