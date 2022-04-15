lexer grammar CPLexer;

options {
    language = JavaScript;
}


/* SKIPS */

Whitespaces
    :   [ \t\r\n]+ -> skip
    ;

LineComment
    :   '--' ~[\n]+ -> skip
    ;

BlockComment
    :   '{-' .*? '-}' -> skip
    ;


/* LITERALS */

IntLit
    :   [0-9]+ ('.' [0-9]+)? (('e' | 'E') ('+' | '-')? [0-9]+)?
    |   ('0x' | '0X') [0-9a-fA-F]+
    |   ('0o' | '0O') [0-7]+
    ;

StringLit
    :   '"' (~[\\\r\n"] | '\\' .)* '"'
    ;


/* KEYWORDS */

Type
    :   'type'
    ;

TypeRec
    :   'typerec'
    ;

ForAll
    :   'forall'
    ;

Int
    :   'Int'
    ;

Double
    :   'Double'
    ;

Bool
    :   'Bool'
    ;

String
    :   'String'
    ;

Top
    :   'Top'
    ;

Bot
    :   'Bot'
    ;

TraitType
    :   'Trait'
    ;

Trait
    :   'trait'
    ;

Implements
    :   'implements'
    ;

Inherits
    :   'inherits'
    ;

New
    :   'new'
    ;

If
    :   'if'
    ;

Then
    :   'then'
    ;

Else
    :   'else'
    ;

Let
    :   'let'
    ;

LetRec
    :   'letrec'
    ;

Open
    :   'open'
    ;

In
    :   'in'
    ;

With
    :   'with'
    ;

ToString
    :   'toString'
    ;

Fold
    :   'fold'
    ;

Unfold
    :   'unfold'
    ;

Override
    :   'override'
    ;

True_
    :   'true'
    ;

False_
    :   'false'
    ;

Undefined_
    :   'undefined'
    ;


/* IDENTIFIERS */

fragment
IdChar
    :   [a-zA-Z] | [0-9] | Underscore | '\''
    ;

Underscore
    :   '_'
    ;

LowerId
    :   [a-z] IdChar*
    ;

UpperId
    :   [A-Z] IdChar*
    ;


/* SYMBOLS */

Unit
    :   '()'
    ;

Backslash
    :   '\\'
    ;

SlashBackslash
    :   '/\\'
    ;

BackslashMinus
    :   '\\-'
    ;

DoubleBackslashes
    :   '\\\\'
    ;

Arrow
    :   '->'
    ;

FatArrow
    :   '=>'
    ;

LeftArrow
    :   '<-'
    ;

Intersect
    :   '&'
    ;

Plus
    :   '+'
    ;

Minus
    :   '-'
    ;

Asterisk
    :   '*'
    ;

Slash
    :   '/'
    ;

Modulo
    :   '%'
    ;

Not
    :   '!'
    ;

And
    :   '&&'
    ;

Or
    :   '||'
    ;

Less
    :   '<'
    ;

Greater
    :   '>'
    ;

LessEqual
    :   '<='
    ;

GreaterEqual
    :   '>='
    ;

Equal
    :   '=='
    ;

NotEqual
    :   '!='
    ;

Length
    :   '#'
    ;

Index
    :   '!!'
    ;

Append
    :   '++'
    ;

Forward
    :   '^'
    ;

At
    :   '@'
    ;

Merge
    :   ','
    |   ',,'
    ;

LeftistMerge
    :   '+,'
    ;

RightistMerge
    :   ',+'
    ;

Assign
    :   '='
    ;

Semicolon
    :   ';'
    ;

Colon
    :   ':'
    ;

Dot
    :   '.'
    ;

DotDot
    :   '..'
    ;

Dollar
    :   '$'
    ;

Question
    :   '?'
    ;


/* BRACKETS */

BracketOpen
    :   '['
    ;

BracketClose
    :   ']'
    ;

BraceOpen
    :   '{' -> pushMode(DEFAULT_MODE)
    ;

BraceClose
    :   '}' -> popMode
    ;

ParenOpen
    :   '(' -> pushMode(DEFAULT_MODE)
    ;

ParenClose
    :   ')' -> popMode
    ;

BacktickOpen
    :   '`' -> pushMode(DOC_MODE)
    ;


/* DOCUMENT */
mode DOC_MODE;

Command
    :   '\\' (LowerId | UpperId) -> pushMode(CMD_MODE)
    ;

Interpolation
    :   '\\(' -> pushMode(DEFAULT_MODE)
    ;

NewLine
    :   '\\\\'
    ; 

PlainText
    :   ~[\\\]`]+
    ;

BracketCloseInDoc
    :   ']' -> popMode
    ;

BacktickClose
    :   '`' -> popMode
    ;


/* COMMAND */
mode CMD_MODE;

BracketOpenAsArg
    :   '[' -> pushMode(DOC_MODE)
    ;

ParenOpenAsArg
    :   '(' -> pushMode(DEFAULT_MODE)
    ;

BraceOpenAsArg
    :   '{' -> pushMode(DEFAULT_MODE)
    ;

CommandAfterCmd
    :   '\\' (LowerId | UpperId)
    ;

InterpolationAfterCmd
    :   '\\(' -> popMode, pushMode(DEFAULT_MODE)
    ;

NewLineAfterCmd
    :   '\\\\' -> popMode
    ;

PlainTextAfterCmd
    :   ~[({[\]\\`]+ -> popMode
    ;

BracketCloseAfterCmd
    :   ']' -> popMode, popMode
    ;

BacktickCloseAfterCmd
    :   '`' -> popMode, popMode
    ;
