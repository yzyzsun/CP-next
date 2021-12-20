parser grammar CPParser;

options {
    language = JavaScript;
    tokenVocab = CPLexer;
}

program
    :   open* definition* expression
    ;

open
    :   Open ((Lowerid | Upperid) Divide)* (Upperid | Lowerid) Semicolon
    ;

definition
    :   typeDef
    |   termDef
    ;

typeDef
    :   Type typeNameDecl (Less typeNameDecl Greater)* typeNameDecl* Assign type Semicolon
    ;

termDef
    :   termNameDecl typeParam* termParam* (Colon type)? Assign expression Semicolon
    ;

type
    :   btype
    |   <assoc=left> type Intersect type
    |   <assoc=right> type Arrow type
    ;

btype
    :   atype (atype | Less sort Greater)*
    |   ForAll typeParam+ Dot type
    |   TraitCaps Less type (TraitArrow type)? Greater
    |   Mu typeNameDecl Dot type
    ;

atype
    :   Int
    |   Double
    |   StringType
    |   Bool
    |   Top
    |   Bot
    |   typeName
    |   recordType
    |   BracketOpen type BracketClose
    |   ParenOpen type ParenClose
    ;

recordType
    :   BraceOpen (recordTypeElement Semicolon)* recordTypeElement? BraceClose
    ;

recordTypeElement
    :   labelDecl Question? Colon type
    ;

expression
    :   opexpr (Colon type | Backslash type)?
    ;

opexpr
    :   lexpr                       
    |   (Minus | Not | Length) opexpr
    |   <assoc=left> opexpr Index opexpr
    |   <assoc=left> opexpr (Modulo | Divide | Star) opexpr
    |   <assoc=left> opexpr (Minus | Plus) opexpr
    |   <assoc=left> opexpr Append opexpr
    |   opexpr (Less | Greater | LessEqual | GreaterEqual | Equal | NotEqual) opexpr
    |   <assoc=right> opexpr And opexpr
    |   <assoc=right> opexpr Or opexpr
    |   <assoc=left> opexpr Forward opexpr
    |   <assoc=left> opexpr Merge opexpr
    ;

lexpr
    :   fexpr
    |   lambda
    |   bigLambda
    |   let_
    |   letRec
    |   open_
    |   ifElse
    |   trait
    |   new_
    |   toString_
    |   fold
    |   unfold
    ;

lambda
    :   Backslash termParam+ Arrow expression
    ;

bigLambda
    :   SlashBackslash typeParam+ Dot expression
    ;

let_
    :   Let termNameDecl typeParam* termParam* Assign expression In expression
    ;

letRec
    :   LetRec termNameDecl typeParam* termParam* Colon type Assign expression In expression
    ;

open_
    :   Open expression In expression
    ;

ifElse
    :   If expression Then expression Else expression
    ;

trait
    :   TraitSmall selfAnno? (Implements type)? (Inherits opexpr)? TraitArrow opexpr
    |   TraitSmall selfAnno? (Inherits opexpr)? (Implements type)? TraitArrow opexpr   
    ;

new_
    :   New opexpr
    ;

toString_
    :   ToString dotexpr
    ;

fold
    :   Fold At atype dotexpr
    ;

unfold
    :   Unfold At atype dotexpr
    ;

fexpr
    :   (typeNameDecl | dotexpr) (dotexpr | At atype)*
    ;

dotexpr
    :   aexpr (Dot label)*
    ;

aexpr
    :   termName
    |   Number
    |   document
    |   String
    |   Unit
    |   True_
    |   False_
    |   Undefined_
    |   array
    |   record
    |   recordUpdate
    |   Dollar typeNameDecl
    |   ParenOpen expression ParenClose
    ;

array
    :   BracketOpen (expression Semicolon)* expression? BracketClose
    ;

record
    :   BraceOpen
            ((recordField | methodPattern | defaultPattern) Semicolon)*
            ((recordField | methodPattern | defaultPattern))?
        BraceClose
    ;

// record
//     :   BraceOpen 
//             ((Override? recordField | Override? methodPattern | (Underscore | selfAnno) Dot recordField) Semicolon)*
//             (Override? recordField | Override? methodPattern | (Underscore | selfAnno) Dot recordField)?
//         BraceClose
//     ;

recordField
    :   Override? selfAnno? labelDecl termParam* Assign expression
    ;

recordUpdate
    :   BraceOpen expression Stick ((labelDecl Assign expression) Semicolon)* (labelDecl Assign expression)? BraceClose
    ;

methodPattern
    :   Override? (selfAnno At)? ParenOpen labelDecl termParam* ParenClose Dot labelDecl termParam* Assign expression
    ;

defaultPattern
    :   Override? (Underscore | selfAnno) Dot labelDecl termParam* Assign expression
    ;

typeParam
    :   typeNameDecl
    |   ParenOpen typeNameDecl Star type ParenClose
    ;

termParam
    :   termId
    |   ParenOpen termId Colon type ParenClose
    |   wildcard
    ;

termId
    :   Underscore
    |   termNameDecl
    ;

wildcard
    :   BraceOpen ((labelDecl Assign expression) Semicolon)* (labelDecl Assign expression)? DotDot BraceClose
    ;

selfAnno
    :   BracketOpen termNameDecl (Colon type)? BracketClose
    ;

sort
    :   type (TraitArrow type)?
    ;

typeNameDecl
    :   Upperid
    ;

typeName
    :   Upperid
    ;

termNameDecl
    :   Lowerid
    ;

termName
    :   Lowerid | Upperid
    ;

labelDecl
    :   Lowerid | Upperid
    ;

label
    :   Lowerid | Upperid
    ;

/* Documents */

document
    :   BacktickOpen docElement* (BacktickClose | BacktickCloseAfterTag)
    ;

docElement
    :   command
    |   interpolation
    |   newline
    |   plaintext
    ;

command
    :   (Tag | TagAfterTag) arg*
    ;

interpolation
    :   (BackslashParen | BackslashParenAfterTag) expression ParenClose
    ;

newline
    :   (LineBreak | LinebreakAfterTag)
    ;

plaintext
    :   (Plaintext | PlaintextAfterTag)
    ;

arg
    :   ParenOpenInTag expression ParenClose
    |   BraceOpenInTag (recordArgField Semicolon)* (recordArgField)? BraceClose
    |   BracketOpenInTag docElement* (BracketCloseInDoc | BracketCloseAfterTag)
    ;

recordArgField
    :   labelDecl termParam* Assign expression
    ;
