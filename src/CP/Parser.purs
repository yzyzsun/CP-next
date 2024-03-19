module Language.CP.Parser where

import Prelude hiding (between)

import Control.Alt ((<|>))
import Control.Lazy (fix)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Identity (Identity)
import Data.List (List, foldl, many, null, some, toUnfoldable)
import Data.List.NonEmpty (toList)
import Data.Maybe (Maybe(..), isJust, isNothing, optional)
import Data.String.CodeUnits as SCU
import Data.String.Regex.Flags (noFlags)
import Data.Tuple (Tuple(..))
import Language.CP.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), LogicOp(..), UnOp(..))
import Language.CP.Syntax.Source (Bias(..), Def(..), MethodPattern(..), Prog(..), RcdField(..), RcdTy(..), SelfAnno, Tm(..), TmParam(..), Ty(..), TyParam, TypeDef(..))
import Language.CP.Util (foldl1, isCapitalized)
import Parsing (Parser, fail, position)
import Parsing.Combinators (between, choice, endBy, option, sepEndBy, sepEndBy1, try)
import Parsing.Expr (Assoc(..), Operator(..), OperatorTable, buildExprParser)
import Parsing.Language (haskellStyle)
import Parsing.String (char, regex)
import Parsing.String.Basic (lower, upper)
import Parsing.Token (GenLanguageDef(..), LanguageDef, TokenParser, makeTokenParser, unGenLanguageDef)
import Partial.Unsafe (unsafeCrashWith)

type SParser a = Parser String a

-- Program --

program :: SParser Prog
program = do
  defs <- many def
  optExpr <- optional expr
  pure $ Prog defs $ case optExpr of
    Just e -> e
    Nothing -> TmUnit

def :: SParser Def
def = interface <|> tyDef <|> tmDef

interface :: SParser Def
interface = do
  reserved "interface"
  a <- upperIdentifier
  sorts <- many (angles upperIdentifier)
  params <- many upperIdentifier
  typeDef <- option Interface (reserved "extends" *> bty ty <#> InterfaceExtends)
  t <- recordTy
  symbol ";"
  pure $ TyDef typeDef a sorts params t

tyDef :: SParser Def
tyDef = do
  reserved "type"
  a <- upperIdentifier
  sorts <- many (angles upperIdentifier)
  params <- many upperIdentifier
  symbol "="
  t <- ty
  symbol ";"
  pure $ TyDef TypeAlias a sorts params t

tmDef :: SParser Def
tmDef = do
  d <- try do
    x <- lowerIdentifier
    tys <- many $ try $ tyParams false
    tms <- many tmParams
    t <- optional (symbol ":" *> ty)
    symbol "="
    pure $ TmDef x tys tms t
  e <- expr
  symbol ";"
  pure $ d e

-- Expressions --

expr :: SParser Tm
expr = fix $ \e -> position >>= \p -> TmPos p <$> colonexpr e

colonexpr :: SParser Tm -> SParser Tm
colonexpr e = opexpr e >>= \e' ->
  TmAnno e' <$ symbol ":" <*> ty <|> pure e'

opexpr :: SParser Tm -> SParser Tm
opexpr e = buildExprParser operators $ lexpr e

lexpr :: SParser Tm -> SParser Tm
lexpr e = fexpr e <|> lambdaAbs <|> tyLambdaAbs <|> trait <|> new <|>
          ifThenElse <|> letIn <|> letrec <|> open <|> toString <|>
          fixpoint <|> fold <|> unfold <|> ref

fexpr :: SParser Tm -> SParser Tm
fexpr e = do
  Tuple isCtor f <- Tuple true <<< TmVar <$> upperIdentifier <|>
                    Tuple false <$> excludexpr e
  args <- many $ flip TmTApp <$> tyArg <|>
                 flip TmApp  <$> excludexpr e
  pure $ (if isCtor then TmNew else identity) (foldl (#) f args)

excludexpr :: SParser Tm -> SParser Tm
excludexpr e = renamexpr e >>= \e' ->
  TmExclude e' <$ symbol "\\\\" <*> bty ty <|>
  TmRemoval e' <$ symbol "\\" <*> identifier <|>
  pure e'

renamexpr :: SParser Tm -> SParser Tm
renamexpr e = dotexpr e >>= \e' -> option e' $ try $ brackets do
  l1 <- identifier
  symbol "<-"
  l2 <- identifier
  pure $ TmRename e' l1 l2

dotexpr :: SParser Tm -> SParser Tm
dotexpr e = bangexpr e >>= \e' -> foldl (#) e' <$>
  many (flip TmPrj <$ char '.' <*> identifier)

-- prevent `arr!!i` from being parsed as `arr (!(!i))`
bangexpr :: SParser Tm -> SParser Tm
bangexpr e = try (symbol "!" *> aexpr e <#> TmDeref) <|> aexpr e

aexpr :: SParser Tm -> SParser Tm
aexpr e = choice [ naturalOrFloat <#> fromIntOrNumber
                 , between (char '`') (symbol "`") $ document e
                 , stringLiteral <#> TmString
                 , reserved "true"  $> TmBool true
                 , reserved "false" $> TmBool false
                 , symbol "()" $> TmUnit
                 , reserved "undefined" $> TmUndefined
                 , lowerIdentifier <#> TmVar
                 , upperIdentifier <#> TmVar >>> TmNew
                 , char '$' *> upperIdentifier <#> TmVar
                 , brackets $ TmArray <<< toUnfoldable <$> sepEndBySemi e
                 , braces $ recordUpdate e <|> recordLit e
                 , parens e
                 ]

lambdaAbs :: SParser Tm
lambdaAbs = do
  symbol "\\"
  xs <- some tmParams
  symbol "->"
  e <- expr
  pure $ TmAbs xs e

tyLambdaAbs :: SParser Tm
tyLambdaAbs = do
  symbol "/\\"
  xs <- some (tyParams true)
  symbol "."
  e <- expr
  pure $ TmTAbs xs e

trait :: SParser Tm
trait = do
  reserved "trait"
  self <- selfAnno
  sig <- optional (reserved "implements" *> ty)
  e1 <- optional (reserved "inherits" *> expr)
  sig' <- optional (reserved "implements" *> ty)
  symbol "=>"
  e2 <- expr
  pure $ TmTrait self (sig <|> sig') e1 e2

new :: SParser Tm
new = do
  reserved "new"
  e <- opexpr expr
  pure $ TmNew e

ifThenElse :: SParser Tm
ifThenElse = do
  reserved "if"
  e1 <- expr
  reserved "then"
  e2 <- expr
  reserved "else"
  e3 <- expr
  pure $ TmIf e1 e2 e3

letIn :: SParser Tm
letIn = do
  reserved "let"
  x <- lowerIdentifier
  tys <- many $ try $ tyParams false
  tms <- many tmParams
  symbol "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  pure $ TmLet x tys tms e1 e2

letrec :: SParser Tm
letrec = do
  reserved "letrec"
  x <- lowerIdentifier
  tys <- many $ try $ tyParams false
  tms <- many tmParams
  symbol ":"
  t <- ty
  symbol "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  pure $ TmLetrec x tys tms t e1 e2

open :: SParser Tm
open = do
  reserved "open"
  e1 <- expr
  reserved "in"
  e2 <- expr
  pure $ TmOpen e1 e2

toString :: SParser Tm
toString = do
  reserved "toString"
  e <- dotexpr expr
  pure $ TmToString e

fixpoint :: SParser Tm
fixpoint = do
  reserved "fix"
  x <- lowerIdentifier
  symbol ":"
  t <- ty
  symbol "."
  e <- opexpr expr
  pure $ TmFix x e t

fold :: SParser Tm
fold = do
  reserved "fold"
  t <- tyArg
  e <- dotexpr expr
  pure $ TmFold t e

unfold :: SParser Tm
unfold = do
  reserved "unfold"
  t <- tyArg
  e <- dotexpr expr
  pure $ TmUnfold t e

ref :: SParser Tm
ref = do
  reserved "ref"
  e <- dotexpr expr
  pure $ TmRef e

document :: SParser Tm -> SParser Tm
document p = position >>= \pos -> TmPos pos <<< TmDoc <$> do
  docs <- many (backslash <|> plaintext)
  pure $ if null docs then newStr (TmString "") else foldl1 newComp docs
  where
    backslash = char '\\' *> (command <|> interpolation <|> newline)
    command = do
      pos <- position
      cmd <- identifier
      targs <- many tyArg
      args <- many $ choice [ parensWithoutTrailingSpace p
                            , bracesWithoutTrailingSpace recordArg
                            , bracketsWithoutConsumingSpace $ document p
                            ]
      let f = if isCapitalized cmd then TmNew else identity
      pure $ TmPos pos (f (foldl TmApp (foldl TmTApp (TmVar cmd) targs) args))
    recordArg = TmRcd <$> sepEndBySemi (recordField p false)
    interpolation = newStr <<< TmToString <$> parensWithoutTrailingSpace p
    newline = char '\\' $> newEndl
    plaintext = newStr <<< TmString <$> re
    re = either unsafeCrashWith identity $ regex """[^\\\]`]+""" noFlags
    newEndl = TmNew (TmVar "Endl")
    newStr s = TmNew (TmApp (TmVar "Str") s)
    newComp x y = TmNew (TmApp (TmApp (TmVar "Comp") x) y)

parensWithoutTrailingSpace :: forall a. SParser a -> SParser a
parensWithoutTrailingSpace = between (symbol "(") (char ')')

bracesWithoutTrailingSpace :: forall a. SParser a -> SParser a
bracesWithoutTrailingSpace = between (symbol "{") (char '}')

bracketsWithoutConsumingSpace :: forall a. SParser a -> SParser a
bracketsWithoutConsumingSpace = between (char '[') (char ']')

recordUpdate :: SParser Tm -> SParser Tm
recordUpdate p = do
  rcd <- try $ p <* reserved "with"
  fields <- sepEndBySemi1 (Tuple <$> identifier <* symbol "=" <*> p)
  pure $ TmUpdate rcd fields

recordLit :: SParser Tm -> SParser Tm
recordLit p = TmRcd <$> sepEndBySemi do
  o <- isJust <$> optional (reserved "override")
  self <- selfAnno
  recordField p o <|> methodPattern p o self <|> defaultPattern p self

recordField :: SParser Tm -> Boolean -> SParser RcdField
recordField p o = do
  l <- identifier
  params <- many tmParams
  symbol "="
  e <- p
  pure $ RcdField o l params (Left e)

methodPattern :: SParser Tm -> Boolean -> SelfAnno -> SParser RcdField
methodPattern p o self = do
  if isJust self then symbol "@" else pure unit
  symbol "("
  l <- identifier
  params <- many tmParams
  symbol ")"
  symbol "."
  l' <- identifier
  params' <- many tmParams
  symbol "="
  e <- p
  pure $ RcdField o l params (Right (MethodPattern self l' params' e))

defaultPattern :: SParser Tm -> SelfAnno -> SParser RcdField
defaultPattern p self = do
  if isNothing self then symbol "_" else pure unit
  symbol "."
  l <- identifier
  params <- many tmParams
  symbol "="
  e <- p
  pure $ DefaultPattern (MethodPattern self l params e)

operators :: OperatorTable Identity String Tm
operators = [ [ Prefix (reservedOp "-" $> TmUnary Neg)
              , Prefix (reservedOp "#" $> TmUnary Len)
              , Prefix (reservedOp "√" $> TmUnary Sqrt)
              ]
            , [ Infix (reservedOp "!!" $> TmBinary Index) AssocLeft ]
            , [ Infix (reservedOp "*" $> TmBinary (Arith Mul)) AssocLeft
              , Infix (reservedOp "/" $> TmBinary (Arith Div)) AssocLeft
              , Infix (reservedOp "%" $> TmBinary (Arith Mod)) AssocLeft
              ]
            , [ Infix (reservedOp "+" $> TmBinary (Arith Add)) AssocLeft
              , Infix (reservedOp "-" $> TmBinary (Arith Sub)) AssocLeft
              ]
            , [ Infix (reservedOp "++" $> TmBinary Append) AssocLeft ]
            , [ Infix (reservedOp "==" $> TmBinary (Comp Eql)) AssocNone
              , Infix (reservedOp "!=" $> TmBinary (Comp Neq)) AssocNone
              , Infix (reservedOp "<"  $> TmBinary (Comp  Lt)) AssocNone
              , Infix (reservedOp "<=" $> TmBinary (Comp  Le)) AssocNone
              , Infix (reservedOp ">"  $> TmBinary (Comp  Gt)) AssocNone
              , Infix (reservedOp ">=" $> TmBinary (Comp  Ge)) AssocNone
              ]
            , [ Infix (reservedOp "&&" $> TmBinary (Logic And)) AssocRight ]
            , [ Infix (reservedOp "||" $> TmBinary (Logic  Or)) AssocRight ]
            , [ Infix (reservedOp "^" $> TmForward) AssocLeft ]
            , [ Infix (reservedOp ",," $> TmMerge  Neutral) AssocLeft
              , Infix (reservedOp ","  $> TmMerge  Neutral) AssocLeft
              , Infix (reservedOp "+," $> TmMerge  Leftist) AssocLeft
              , Infix (reservedOp ",+" $> TmMerge Rightist) AssocLeft
              , Infix (reservedOp "\\-" $> TmDiff) AssocLeft
              ]
            , [ Infix (reservedOp ":=" $> TmAssign) AssocNone ]
            , [ Infix (reservedOp ">>" $> TmSeq)  AssocLeft ]
            ]

-- Types --

ty :: SParser Ty
ty = fix \t -> buildExprParser toperators $ cty t

cty :: SParser Ty -> SParser Ty
cty t = foldl TyApp <$> bty t <*> many (bty t) <|>
        forallTy <|> muTy <|> refTy <|> traitTy <|> absTy

bty :: SParser Ty -> SParser Ty
bty t = foldl TyApp <$> aty t <*> many (sortTy t)

aty :: SParser Ty -> SParser Ty
aty t = choice [ reserved "Int"    $> TyInt
               , reserved "Double" $> TyDouble
               , reserved "String" $> TyString
               , reserved "Bool"   $> TyBool
               , symbol   "()"     $> TyUnit
               , reserved "Top"    $> TyTop
               , reserved "Bot"    $> TyBot
               , upperIdentifier <#> TyVar
               , brackets t <#> TyArray
               , recordTy
               , parens t
               ]

sortTy :: SParser Ty -> SParser Ty
sortTy t = angles do
  ti <- t
  to <- optional (symbol "=>" *> t)
  pure $ TySort ti to

forallTy :: SParser Ty
forallTy = do
  reserved "forall"
  xs <- some (tyParams true)
  symbol "."
  t <- ty
  pure $ TyForall xs t

muTy :: SParser Ty
muTy = do
  reserved "mu"
  x <- upperIdentifier
  symbol "."
  t <- ty
  pure $ TyRec x t

refTy :: SParser Ty
refTy = do
  reserved "Ref"
  t <- bty ty
  pure $ TyRef t

traitTy :: SParser Ty
traitTy = do
  reserved "Trait"
  angles do
    ti <- optional (try (ty <* symbol "=>"))
    to <- ty
    pure $ TyTrait ti to

-- used for serialization of type aliases
absTy :: SParser Ty
absTy = do
  symbol "\\"
  e <- choice [ Left <$> try upperIdentifier
              , Right <$> angles (Tuple <$> upperIdentifier <* symbol "," <*> upperIdentifier)
              ]
  symbol "->"
  t <- ty
  pure $ case e of Left a -> TyAbs a t
                   Right (Tuple a b) -> TySig a b t

recordTy :: SParser Ty
recordTy = braces $ TyRcd <$> sepEndBySemi do
  l <- identifier
  opt <- isJust <$> optional (symbol "?")
  symbol ":"
  t <- ty
  pure $ RcdTy l t opt

toperators :: OperatorTable Identity String Ty
toperators = [ [ Infix (reservedOp "&"  $> TyAnd) AssocLeft  ]
             , [ Infix (reservedOp "\\" $> TyDiff) AssocLeft ]
             , [ Infix (reservedOp "->" $> TyArrow) AssocRight ]
             ]

-- Helpers --

fromIntOrNumber :: Either Int Number -> Tm
fromIntOrNumber (Left int) = TmInt int
fromIntOrNumber (Right number) = TmDouble number

tyArg :: SParser Ty
tyArg = char '@' *> bty ty

tyParams :: Boolean -> SParser TyParam
tyParams us = Tuple <$> id <*> pure Nothing <|>
              parens (Tuple <$> id <* symbol "*" <*> (Just <$> ty))
  where id = if us then underscore <|> upperIdentifier else upperIdentifier

tmParams :: SParser TmParam
tmParams = choice [ parensNameColonType
                  , TmParam <$> id <@> Nothing
                  , WildCard <$> braces (endBySemi defaultField <* symbol "..")
                  ]
  where id = lowerIdentifier <|> underscore
        parensNameColonType = parens do
          x <- id
          symbol ":"
          t <- ty
          pure $ TmParam x (Just t)
        defaultField = do
          x <- lowerIdentifier
          symbol "="
          e <- expr
          pure $ Tuple x e

selfAnno :: SParser SelfAnno
selfAnno = optional $ brackets $
  Tuple <$> lowerIdentifier <*> optional (symbol ":" *> ty)

-- Lexer --

langDef :: LanguageDef
langDef = LanguageDef (unGenLanguageDef haskellStyle) { reservedNames =
  [ "true", "false", "undefined", "if", "then", "else", "toString", "fix"
  , "trait", "implements", "inherits", "override", "new", "fold", "unfold"
  , "let", "letrec", "open", "in", "with", "ref"
  , "type", "interface", "extends", "forall", "mu"
  , "Int", "Double", "String", "Bool", "Top", "Bot", "Trait", "Ref"
  ]
}

lang :: TokenParser
lang = makeTokenParser langDef

identifier :: SParser String
identifier = lang.identifier

reserved :: String -> SParser Unit
reserved = lang.reserved

operator :: SParser String
operator = lang.operator

reservedOp :: String -> SParser Unit
reservedOp = lang.reservedOp

stringLiteral :: SParser String
stringLiteral = lang.stringLiteral

naturalOrFloat :: SParser (Either Int Number)
naturalOrFloat = lang.naturalOrFloat

symbol :: String -> SParser Unit
symbol s = lang.symbol s $> unit

underscore :: SParser String
underscore = lang.symbol "_"

lexeme :: forall a. SParser a -> SParser a
lexeme = lang.lexeme

whiteSpace :: SParser Unit
whiteSpace = lang.whiteSpace

parens :: forall a. SParser a -> SParser a
parens = lang.parens

braces :: forall a. SParser a -> SParser a
braces = lang.braces

angles :: forall a. SParser a -> SParser a
angles = lang.angles

brackets :: forall a. SParser a -> SParser a
brackets = lang.brackets

sepEndBySemi1 :: forall a. SParser a -> SParser (List a)
sepEndBySemi1 p = toList <$> sepEndBy1 p (symbol ";")

sepEndBySemi :: forall a. SParser a -> SParser (List a)
sepEndBySemi = flip sepEndBy $ symbol ";"

endBySemi :: forall a. SParser a -> SParser (List a)
endBySemi = flip endBy $ symbol ";"

ident :: SParser Char -> SParser String
ident identStart = lexeme $ try do
  let languageDef = unGenLanguageDef langDef
  c <- identStart
  cs <- Array.many languageDef.identLetter
  let word = SCU.singleton c <> SCU.fromCharArray cs
  if not (Array.elem word languageDef.reservedNames) then pure word
  else fail $ "Unexpected reserved word " <> show word

lowerIdentifier :: SParser String
lowerIdentifier = ident lower

upperIdentifier :: SParser String
upperIdentifier = ident upper
