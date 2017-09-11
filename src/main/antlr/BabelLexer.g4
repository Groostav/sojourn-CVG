lexer grammar BabelLexer;

INTEGER : DIGIT+ ;
FLOAT   : DIGIT* '.' DIGIT+ ( ('e'|'E') '-'? DIGIT+)? ;
DIGIT   : '0'..'9';

COS      :    'cos';
SIN      :    'sin';
TAN      :    'tan';
ATAN     :    'atan';
ACOS     :    'acos';
ASIN     :    'asin';
SINH     :    'sinh';
COSH     :    'cosh';
TANH     :    'tanh';
COT      :    'cot';
LN       :    'ln';
LOG      :    'log';
ABS      :    'abs';
SQRT     :    'sqrt';
CBRT     :    'cbrt';
SQR      :    'sqr';
CUBE     :    'cube';
CIEL     :    'ceil';
FLOOR    :    'floor';
MAX      :    'max';
MIN      :    'min';

CONSTANT
    : 'pi' | 'e';

SUM           : 'sum';
PROD          : 'prod';
DYN_VAR       : 'var' ;

VARIABLE      : VARIABLE_START VARIABLE_PART*;

LAMBDA        : '->' ;

LT            : '<' ;
LTEQ          : '<=' ;
GT            : '>' ;
GTEQ          : '>=' ;
EQ            : '==' ;

MULT          : '*' ;
DIV           : '/' ;
MOD           : '%' ;

PLUS          : '+' ;
MINUS         : '-' ;

EXPONENT      : '^' ;

OPEN_PAREN    : '(' ;
CLOSE_PAREN   : ')' ;
OPEN_BRACKET  : '[' ;
CLOSE_BRACKET : ']' ;

COMMA         : ',' ;

fragment
VARIABLE_START
    : [a-zA-Z_]
    | ~[\u0000-\u00FF\uD800-\uDBFF] //non 'surrogate' unicode
    | [\uD800-\uDBFF] [\uDC00-\uDFFF] // covers UTF-16 surrogate pair-encodings for U+10000 to U+10FFFF
    ;

fragment
VARIABLE_PART
    : [0-9]
    | VARIABLE_START
    ;

LINEBREAKS    : ('\r' | '\n' | ' ') -> skip ;