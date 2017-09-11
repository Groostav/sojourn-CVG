parser grammar BabelParser;

options { tokenVocab=BabelLexer; }

expression : expr EOF;

expr : (literal | variable)
     | '(' expr ')'
     | (sum | prod) '(' expr ',' expr ',' lambdaExpr ')'
     | binaryFunction '(' expr ',' expr ')'
     | unaryFunction '(' expr ')'
     | dynamicVariableAccess '[' expr ']'
     | negate expr
     | expr exponent (('(' expr ')') | literal | variable)
     | expr (mult | div | mod) expr
     | expr (plus | minus) expr
     | expr (lt | lteq | gt | gteq | eq) expr
     ;

lambdaExpr          : name '->' expr;

plus                : '+';
minus               : '-';

mult                : '*';
div                 : '/';
mod                 : '%';

exponent            : '^';

sum                 : 'sum';
prod                : 'prod';

dynamicVariableAccess : 'var';

binaryFunction      : 'max' | 'min' | 'log' ;

unaryFunction       : 'cos' | 'sin' | 'tan'
                    | 'atan' | 'acos' | 'asin'
                    | 'sinh' | 'cosh' | 'tanh'
                    | 'cot'
                    //override Javas default log & log10 with ln & log respectively
                    | 'ln' | 'log'
                    | 'abs'
                    | 'sqrt' | 'cbrt'
                    | 'sqr' | 'cube'
                    | 'ceil' | 'floor'
                    ;

negate              : '-';

lt                  : '<';
lteq                : '<=';
gt                  : '>';
gteq                : '>=';
eq                  : '==';

//used in validation of text fields supplied by the user
variable_only       : variable EOF;

name                : VARIABLE;
variable            : VARIABLE;

literal : (INTEGER | FLOAT) | CONSTANT ;
