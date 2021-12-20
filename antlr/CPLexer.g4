lexer grammar CPLexer;

options {
    language = JavaScript;
}


Whitespaces
    :   [ \t]+ -> skip
    ;

LineComment
    :   '--' ~[\n]+ -> skip
    ;

BlockComment
    :   '{-' .*? '-}' -> skip
    ;


/* KEYWORDS */

Open
    :   'open'
    ;

Type
    :   'type'
    ;

ForAll
    :   'forall'
    ;

TraitCaps
    :   'Trait'
    ;

Mu
    :   'mu'
    ;

Int
    :   'Int'
    ;

Double
    :   'Double'
    ;

StringType
    :   'String'
    ;

Bool
    :   'Bool'
    ;

Top
    :   'Top'
    ;

Bot
    :   'Bot'
    ;

Let
    :   'let'
    ;

LetRec
    :   'letrec'
    ;

In
    :   'in'
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

TraitSmall
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

ToString
    :   'toString'
    ;

Fold
    :   'fold'
    ;

Unfold
    :   'unfold'
    ;

At
    :   '@'
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

Override
    :   'override'
    ;


/* NOT KEYWORDS */

Underscore
    : '_'
    ;

Lowerid
    :   [a-z] IdChar*
    ;

Upperid
    :   [A-Z] IdChar*
    ;

fragment
IdChar
    :   [a-zA-Z] | [0-9] | Underscore | '\''
    ;

Number
    :   [0-9]+ ('.' [0-9]+)? (('e' | 'E') ('+' | '-')? [0-9]+)?
    |   '0x' Hexit+
    |   '0X' Hexit+
    |   '0o' Octit+
    |   '0O' Octit+
    ;

fragment
Octit
    :   [0-7]
    ;

fragment
Hexit
    :   [0-9] | [a-fA-F]
    ;

BacktickOpen
    :   '`' -> pushMode(DOC_MODE)
    ;

// Document
//     :   '`' ~[`]* '`'
//     ;


String
    :   '"' (~[\\\r\n"] | '\\' .)*? '"'
    ;

Unit
    :   '()'
    ;

Arrow
    :   '->'
    ;

TraitArrow
    :   '=>'
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

Star
    :   '*'
    ;

Divide
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

Append
    :   '++'
    ;

Less
    :   '<'
    ;

Greater
    :   '>'
    ;

LessEqual
    :   '<' '='
    ;

GreaterEqual
    :   '>' '='
    ;

Equal
    :   '=='
    ;

NotEqual
    :   '!='
    ;

Merge
    :   ','
    ;

Forward
    :   '^'
    ;

Index
    :   '!!'
    ;

Length
    :   '#'
    ;

Assign
    :   '='
    ;

Newline
    :   (   '\r' '\n'?
        |   '\n'
        )
        -> skip
    ;

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

Semicolon
    :   ';'
    ;

Colon
    :   ':'
    ;

Backslash
    :   '\\'
    ;

SlashBackslash
    :   '/\\'
    ;

Dot
    :   '.'
    ;

Question
    :   '?'
    ;

Dollar
    :   '$'
    ;

Stick
    :   '|'
    ;

DotDot
    :   '..'
    ;


/* Document Mode */
mode DOC_MODE;

BacktickClose
    :   '`' -> popMode
    ;

BracketCloseInDoc
    :   ']'  -> popMode
    ;

LineBreak
    :   '\\\\'
    ; 

Tag
    :   '\\' (Lowerid | Upperid) -> pushMode(TAG_MODE)
    ;

BackslashParen
    :   '\\('    -> pushMode(DEFAULT_MODE)
    ;

Plaintext
    :   ~[\]\\`]+
    ;


/* TAG Mode */
mode TAG_MODE;

ParenOpenInTag
    :   '(' -> pushMode(DEFAULT_MODE)
    ;

BraceOpenInTag
    :   '{' -> pushMode(DEFAULT_MODE)
    ;

BracketOpenInTag
    :   '[' -> pushMode(DOC_MODE)
    ;

PlaintextAfterTag
    :   ~[({[\]\\`]+ -> popMode
    ;

BracketCloseAfterTag
    :   ']' ->  popMode, popMode
    ;

BacktickCloseAfterTag
    :   '`' ->  popMode, popMode
    ;

TagAfterTag
    :   '\\' (Lowerid | Upperid)
    ;

LinebreakAfterTag
    :   '\\\\'
    ;

BackslashParenAfterTag
    :   '\\('   -> pushMode(DEFAULT_MODE)
    ;
