/*
MIT license
Author: Ken Domino, October 2023
Based on previous work of: Kazunori Sakamoto, Alexander Alexeev
Simplified for clj-antlr by removing semantic predicates
*/

grammar Lua;

// Parser rules

start_
    : chunk EOF
    ;

chunk
    : block
    ;

block
    : stat* retstat?
    ;

stat
    : ';'
    | varlist '=' explist
    | functioncall
    | label
    | 'break'
    | 'goto' NAME
    | 'do' block 'end'
    | 'while' exp 'do' block 'end'
    | 'repeat' block 'until' exp
    | 'if' exp 'then' block ('elseif' exp 'then' block)* ('else' block)? 'end'
    | 'for' NAME '=' exp ',' exp (',' exp)? 'do' block 'end'
    | 'for' namelist 'in' explist 'do' block 'end'
    | 'function' funcname funcbody
    | 'local' 'function' NAME funcbody
    | 'local' attnamelist ('=' explist)?
    ;

attnamelist
    : NAME attrib (',' NAME attrib)*
    ;

attrib
    : ('<' NAME '>')?
    ;

retstat
    : 'return' explist? ';'?
    ;

label
    : '::' NAME '::'
    ;

funcname
    : NAME ('.' NAME)* (':' NAME)?
    ;

varlist
    : var (',' var)*
    ;

namelist
    : NAME (',' NAME)*
    ;

explist
    : exp (',' exp)*
    ;

exp
    : 'nil'
    | 'false'
    | 'true'
    | number
    | string
    | '...'
    | functiondef
    | prefixexp
    | tableconstructor
    | <assoc = right> exp ('^') exp
    | ('not' | '#' | '-' | '~') exp
    | exp ('*' | '/' | '%' | '//') exp
    | exp ('+' | '-') exp
    | <assoc = right> exp ('..') exp
    | exp ('<<' | '>>') exp
    | exp ('&') exp
    | exp ('~') exp
    | exp ('|') exp
    | exp ('<' | '>' | '<=' | '>=' | '~=' | '==') exp
    | exp ('and') exp
    | exp ('or') exp
    ;

var
    : NAME
    | prefixexp ('[' exp ']' | '.' NAME)
    ;

prefixexp
    : NAME ( '[' exp ']' | '.' NAME )*
    | functioncall ( '[' exp ']' | '.' NAME )*
    | '(' exp ')' ( '[' exp ']' | '.' NAME )*
    ;

functioncall
    :  ( ( NAME | '(' exp ')' ) ( '[' exp ']' | '.' NAME )* ( args | ':' NAME args ) ) ( ( '[' exp ']' | '.' NAME )* ( args | ':' NAME args ) )*
    ;

args
    : '(' explist? ')'
    | tableconstructor
    | string
    ;

functiondef
    : 'function' funcbody
    ;

funcbody
    : '(' parlist ')' block 'end'
    ;

parlist
    : namelist (',' '...' NAME?)?
    | '...' NAME?
    |
    ;

tableconstructor
    : '{' fieldlist? '}'
    ;

fieldlist
    : field (fieldsep field)* fieldsep?
    ;

field
    : '[' exp ']' '=' exp
    | NAME '=' exp
    | exp
    ;

fieldsep
    : ','
    | ';'
    ;

number
    : INT
    | HEX
    | FLOAT
    | HEX_FLOAT
    ;

string
    : NORMALSTRING
    | CHARSTRING
    | LONGSTRING
    ;

// Lexer rules

SEMI : ';';
EQ   : '=';

BREAK    : 'break';
GOTO     : 'goto';
DO       : 'do';
END      : 'end';
WHILE    : 'while';
REPEAT   : 'repeat';
UNTIL    : 'until';
IF       : 'if';
THEN     : 'then';
ELSEIF   : 'elseif';
ELSE     : 'else';
FOR      : 'for';
COMMA    : ',';
IN       : 'in';
FUNCTION : 'function';
LOCAL    : 'local';
LT       : '<';
GT       : '>';
RETURN   : 'return';
CC       : '::';
NIL      : 'nil';
FALSE    : 'false';
TRUE     : 'true';
DOT      : '.';
SQUIG    : '~';
MINUS    : '-';
POUND    : '#';
OP       : '(';
CP       : ')';
NOT      : 'not';
LL       : '<<';
GG       : '>>';
AMP      : '&';
SS       : '//';
PER      : '%';
COL      : ':';
LE       : '<=';
GE       : '>=';
AND      : 'and';
OR       : 'or';
PLUS     : '+';
STAR     : '*';
OCU      : '{';
CCU      : '}';
OB       : '[';
CB       : ']';
EE       : '==';
DD       : '..';
PIPE     : '|';
CARET    : '^';
SLASH    : '/';
DDD      : '...';
SQEQ     : '~=';

NAME: [a-zA-Z_][a-zA-Z_0-9]*;

NORMALSTRING: '"' ( EscapeSequence | ~('\\' | '"'))* '"';

CHARSTRING: '\'' ( EscapeSequence | ~('\'' | '\\'))* '\'';

LONGSTRING: '[' NESTED_STR ']';

fragment NESTED_STR: '=' NESTED_STR '=' | '[' .*? ']';

INT: Digit+;

HEX: '0' [xX] HexDigit+;

FLOAT: Digit+ '.' Digit* ExponentPart? | '.' Digit+ ExponentPart? | Digit+ ExponentPart;

HEX_FLOAT:
    '0' [xX] HexDigit+ '.' HexDigit* HexExponentPart?
    | '0' [xX] '.' HexDigit+ HexExponentPart?
    | '0' [xX] HexDigit+ HexExponentPart
;

fragment ExponentPart: [eE] [+-]? Digit+;

fragment HexExponentPart: [pP] [+-]? Digit+;

fragment EscapeSequence:
    '\\' [abfnrtvz"'|$#\\]
    | '\\' '\r'? '\n'
    | DecimalEscape
    | HexEscape
    | UtfEscape
;

fragment DecimalEscape: '\\' Digit | '\\' Digit Digit | '\\' [0-2] Digit Digit;

fragment HexEscape: '\\' 'x' HexDigit HexDigit;

fragment UtfEscape: '\\' 'u{' HexDigit+ '}';

fragment Digit: [0-9];

fragment HexDigit: [0-9a-fA-F];

fragment SingleLineInputCharacter: ~[\r\n\u0085\u2028\u2029];

COMMENT: '--' ( '[' NESTED_STR ']' | ~[\r\n]* ) -> channel(HIDDEN);

WS: [ \t\u000B\u000C\r]+ -> channel(HIDDEN);

NL: [\n] -> channel(2);

SHEBANG: '#' '!' SingleLineInputCharacter* -> channel(HIDDEN);
