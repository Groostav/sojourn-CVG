package com.empowerops.babel;

import com.empowerops.linqalike.Queryable;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import static com.empowerops.linqalike.Factories.empty;
import static com.empowerops.linqalike.Factories.from;

/**
* Created by Justin Casol on 2/3/2015.
*/
public class TreeHelper {
    public static Queryable<ParseTree> childrenOf(ParseTree ctx) {
        return ctx instanceof ParserRuleContext ? from(((ParserRuleContext) ctx).children) : empty();
    }

    public static Queryable<ParseTree> siblingsOf(ParseTree ctx){
        if(ctx.getParent() == null) { return empty(); }
        return childrenOf(ctx.getParent()).except(ctx).immediately(/*for debugger*/);
    }

}
