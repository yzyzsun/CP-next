parser grammar CPParser;

options {
    language = JavaScript;
    tokenVocab = CPLexer;
}

program
    :   definition* expression EOF
    ;

definition
    :   typeDef
    |   termDef
    ;

typeDef
    :   (Type | TypeRec) typeNameDecl (Less typeNameDecl Greater)* typeNameDecl* Assign type Semicolon
    ;

termDef
    :   termNameDecl typeParam* termParam* (Colon type)? Assign expression Semicolon
    ;

type
    :   <assoc=left> type Intersect type
    |   <assoc=left> type Backslash type
    |   <assoc=right> type Arrow type
    |   ForAll typeParam+ Dot type
    |   TraitType Less type (FatArrow type)? Greater
    |   btype btype*
    ;

btype
    :   atype (Less sort Greater)*
    ;

atype
    :   Int
    |   Double
    |   Bool
    |   String
    |   Top
    |   Bot
    |   typeName
    |   recordType
    |   BracketOpen type BracketClose
    |   ParenOpen type ParenClose
    ;

recordType
    :   BraceOpen (recordTypeField Semicolon)* recordTypeField? BraceClose
    ;

recordTypeField
    :   labelDecl Question? Colon type
    ;

expression
    :   opexpr (Colon type | Backslash type)?
    ;

opexpr
    :   lexpr                       
    |   (Minus | Not | Length) opexpr
    |   <assoc=left> opexpr Index opexpr
    |   <assoc=left> opexpr (Asterisk | Slash | Modulo) opexpr
    |   <assoc=left> opexpr (Plus | Minus) opexpr
    |   <assoc=left> opexpr Append opexpr
    |   opexpr (Less | Greater | LessEqual | GreaterEqual | Equal | NotEqual) opexpr
    |   <assoc=right> opexpr And opexpr
    |   <assoc=right> opexpr Or opexpr
    |   <assoc=left> opexpr Forward opexpr
    |   <assoc=left> opexpr (Merge | LeftistMerge | RightistMerge) opexpr
    ;

lexpr
    :   fexpr
    |   lambda
    |   bigLambda
    |   letIn
    |   letRec
    |   openIn
    |   ifElse
    |   trait
    |   newTrait
    |   toStr
    |   fold
    |   unfold
    ;

lambda
    :   Backslash termParam+ Arrow expression
    ;

bigLambda
    :   SlashBackslash typeParam+ Dot expression
    ;

letIn
    :   Let termNameDecl typeParam* termParam* Assign expression In expression
    ;

letRec
    :   LetRec termNameDecl typeParam* termParam* Colon type Assign expression In expression
    ;

openIn
    :   Open expression In expression
    ;

ifElse
    :   If expression Then expression Else expression
    ;

trait
    :   Trait selfAnno? (Implements type)? (Inherits opexpr)? FatArrow opexpr
    |   Trait selfAnno? (Inherits opexpr)? (Implements type)? FatArrow opexpr
    ;

newTrait
    :   New opexpr
    ;

toStr
    :   ToString dotexpr
    ;

fold
    :   Fold typeArg dotexpr
    ;

unfold
    :   Unfold typeArg dotexpr
    ;

fexpr
    :   (ctorName | dotexpr) (dotexpr | typeArg)*
    ;

dotexpr
    :   aexpr (Dot label)*
    ;

aexpr
    :   termName
    |   IntLit
    |   StringLit
    |   document
    |   Unit
    |   True_
    |   False_
    |   Undefined_
    |   array
    |   record
    |   recordUpdate
    |   Dollar ctorName
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

recordField
    :   Override? selfAnno? labelDecl termParam* Assign expression
    ;

methodPattern
    :   Override? (selfAnno At)? ParenOpen labelDecl termParam* ParenClose Dot labelDecl termParam* Assign expression
    ;

defaultPattern
    :   (Underscore | selfAnno) Dot labelDecl termParam* Assign expression
    ;

recordUpdate
    :   BraceOpen expression With ((labelDecl Assign expression) Semicolon)* (labelDecl Assign expression)? BraceClose
    ;

typeArg
    :   At btype
    ;

typeParam
    :   typeNameDecl
    |   ParenOpen typeNameDecl Asterisk type ParenClose
    ;

termParam
    :   termNameDecl
    |   Underscore
    |   ParenOpen (termNameDecl | Underscore) Colon type ParenClose
    |   wildcard
    ;

wildcard
    :   BraceOpen ((labelDecl Assign expression) Semicolon)* DotDot BraceClose
    ;

selfAnno
    :   BracketOpen termNameDecl (Colon type)? BracketClose
    ;

sort
    :   type (FatArrow type)?
    ;

typeNameDecl
    :   UpperId
    ;

typeName
    :   UpperId
    ;

termNameDecl
    :   LowerId
    ;

ctorName
    :   UpperId
    ;

termName
    :   LowerId | UpperId
    ;

labelDecl
    :   LowerId | UpperId
    ;

label
    :   LowerId | UpperId
    ;

/* Documents */

document
    :   BacktickOpen docElement* (BacktickClose | BacktickCloseAfterCmd)
    ;

docElement
    :   command
    |   interpolation
    |   newline
    |   plaintext
    ;

command
    :   (Command | CommandAfterCmd) docArg*
    ;

interpolation
    :   (Interpolation | InterpolationAfterCmd) expression ParenClose
    ;

newline
    :   (NewLine | NewLineAfterCmd)
    ;

plaintext
    :   (PlainText | PlainTextAfterCmd)
    ;

docArg
    :   BracketOpenAsArg docElement* (BracketCloseInDoc | BracketCloseAfterCmd)
    |   ParenOpenAsArg expression ParenClose
    |   BraceOpenAsArg (recordArgField Semicolon)* (recordArgField)? BraceClose
    ;

recordArgField
    :   labelDecl termParam* Assign expression
    ;
