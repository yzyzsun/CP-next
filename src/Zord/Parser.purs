module Zord.Parser where

import Prelude hiding (between)

import Control.Alt ((<|>))
import Control.Lazy (fix)
import Data.Array as Array
import Data.Char.Unicode (isLower)
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.List (List, foldl, many, some, toUnfoldable)
import Data.Maybe (Maybe(..), isJust, optional)
import Data.String (null)
import Data.String.CodeUnits as CodeUnits
import Data.Tuple (Tuple(..))
import Text.Parsing.Parser (Parser, fail, position)
import Text.Parsing.Parser.Combinators (between, choice, lookAhead, manyTill, sepEndBy, try)
import Text.Parsing.Parser.Expr (Assoc(..), Operator(..), OperatorTable, buildExprParser)
import Text.Parsing.Parser.Language (haskellStyle)
import Text.Parsing.Parser.String (anyChar, char, satisfy, string)
import Text.Parsing.Parser.Token (GenLanguageDef(..), LanguageDef, TokenParser, makeTokenParser, unGenLanguageDef, upper)
import Zord.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), LogicOp(..), Name, UnOp(..))
import Zord.Syntax.Source (MethodPattern(..), RcdField(..), Tm(..), Ty(..))

type SParser a = Parser String a

-- Program --

program :: SParser Tm
program = fix $ \p -> tyDef p <|> try (tmDef p) <|> expr

tyDef :: SParser Tm -> SParser Tm
tyDef p = do
  reserved "type"
  a <- upperIdentifier
  sorts <- many (angles upperIdentifier)
  parms <- many upperIdentifier
  t1 <- optional (reserved "extends" *> ty)
  symbol "="
  t2 <- ty
  symbol ";"
  e <- p
  pure $ TmType a sorts parms t1 t2 e

tmDef :: SParser Tm -> SParser Tm
tmDef p = do
  x <- lowerIdentifier
  tyParams <- many (try (params upperIdentifier "*"))
  tmParams <- many (params lowerIdentifier ":")
  t <- optional (symbol ":" *> ty)
  symbol "="
  e1 <- expr
  symbol ";"
  e2 <- p
  pure $ TmDef x tyParams tmParams t e1 e2

-- Expressions --

expr :: SParser Tm
expr = fix $ \e -> position >>= \p -> TmPos p <$> colonexpr e

colonexpr :: SParser Tm -> SParser Tm
colonexpr e = opexpr e >>= \e' -> TmAnno e' <$ symbol ":" <*> ty <|> pure e'

opexpr :: SParser Tm -> SParser Tm
opexpr e = buildExprParser operators $ lexpr e

lexpr :: SParser Tm -> SParser Tm
lexpr e = fexpr e <|> lambdaAbs <|> tyLambdaAbs <|> trait <|> new <|>
          ifThenElse <|> letIn <|> letrec <|> open <|> toString

fexpr :: SParser Tm -> SParser Tm
fexpr e = dotexpr e >>= \e' -> foldl (#) e' <$>
  many (flip TmTApp <$ char '@' <*> aty ty <|> flip TmApp <$> dotexpr e)

dotexpr :: SParser Tm -> SParser Tm
dotexpr e = aexpr e >>= \e' -> foldl (#) e' <$>
  many (flip TmPrj <$ char '.' <*> identifier)

aexpr :: SParser Tm -> SParser Tm
aexpr e = choice [ naturalOrFloat <#> fromIntOrNumber
                 , lexeme $ hereDocument e
                 , stringLiteral <#> TmString
                 , reserved "true"  $> TmBool true
                 , reserved "false" $> TmBool false
                 , symbol "()" $> TmUnit
                 , identifier <#> TmVar
                 , brackets $ TmArray <<< toUnfoldable <$> sepEndBySemi expr
                 , recordLit e
                 , parens e
                 ]

lambdaAbs :: SParser Tm
lambdaAbs = do
  symbol "\\"
  xs <- some (params lowerIdentifier ":")
  symbol "->"
  e <- expr
  pure $ TmAbs xs e

tyLambdaAbs :: SParser Tm
tyLambdaAbs = do
  symbol "/\\"
  xs <- some (params upperIdentifier "*")
  symbol "."
  e <- expr
  pure $ TmTAbs xs e

trait :: SParser Tm
trait = do
  reserved "trait"
  self <- optional selfAnno
  sig <- optional (reserved "implements" *> ty)
  e1 <- optional (reserved "inherits" *> expr)
  symbol "=>"
  e2 <- expr
  pure $ TmTrait self sig e1 e2

new :: SParser Tm
new = do
  reserved "new"
  e <- expr
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
  symbol "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  pure $ TmLet x e1 e2

letrec :: SParser Tm
letrec = do
  reserved "letrec"
  x <- lowerIdentifier
  symbol ":"
  t <- ty
  symbol "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  pure $ TmLetrec x t e1 e2

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

hereDocument :: SParser Tm -> SParser Tm
hereDocument p = between tripleQuotes tripleQuotes (document p) <#>
                 \arr -> newApp (TmVar "Doc") (TmArray arr)

document :: SParser Tm -> SParser (Array Tm)
document p = do
  s <- stringTill (char '\\' <|> char ']' <|> tripleQuotes $> '"')
  let str = if null s then [] else [newApp (TmVar "Str") (TmString s)]
  bs <- optional (char '\\')
  if isJust bs then do
    e <- between (symbol "(") (char ')') p <|> TmVar <$> stringTill (char '[')
    doc <- optional $ between (char '[') (char ']') (document p)
    let res = case doc of Just arr -> newApp e (TmArray arr)
                          Nothing -> newApp (TmVar "Str") (TmToString e)
    more <- document p
    pure $ str <> [res] <> more
  else pure str

newApp :: Tm -> Tm -> Tm
newApp x y = TmNew (TmApp x y)

recordLit :: SParser Tm -> SParser Tm
recordLit p = braces $ TmRcd <$> sepEndBySemi (recordField p <|> methodPattern p)

recordField :: SParser Tm -> SParser RcdField
recordField p = do
  o <- override
  l <- identifier
  symbol "="
  e <- p
  pure $ RcdField o l (Left e)

methodPattern :: SParser Tm -> SParser RcdField
methodPattern p = do
  o <- override
  symbol "("
  l <- identifier
  parms <- many (params lowerIdentifier ":")
  self <- optional selfAnno
  symbol ")"
  symbol "."
  l' <- identifier
  symbol "="
  e <- p
  pure $ RcdField o l (Right (MethodPattern parms self l' e))

operators :: OperatorTable Identity String Tm
operators = [ [ Prefix (reservedOp "-" $> TmUnary Neg)
              , Prefix (reservedOp "!" $> TmUnary Not)
              , Prefix (reservedOp "#" $> TmUnary Len)
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
              , Infix (reservedOp "<"  $> TmBinary (Comp Lt )) AssocNone
              , Infix (reservedOp "<=" $> TmBinary (Comp Le )) AssocNone
              , Infix (reservedOp ">"  $> TmBinary (Comp Gt )) AssocNone
              , Infix (reservedOp ">=" $> TmBinary (Comp Ge )) AssocNone
              ]
            , [ Infix (reservedOp "&&" $> TmBinary (Logic And)) AssocRight ]
            , [ Infix (reservedOp "||" $> TmBinary (Logic Or )) AssocRight ]
            , [ Infix (reservedOp "," $> TmMerge) AssocLeft ]
            ]

-- Types --

ty :: SParser Ty
ty = fix \t -> buildExprParser toperators $ bty t

bty :: SParser Ty -> SParser Ty
bty t = foldl TyApp <$> aty t <*> many (aty t <|> sortTy t) <|>
        forallTy <|> traitTy <|> arrayTy

aty :: SParser Ty -> SParser Ty
aty t = choice [ reserved "Int"    $> TyInt
               , reserved "Double" $> TyDouble
               , reserved "String" $> TyString
               , reserved "Bool"   $> TyBool
               , reserved "Top"    $> TyTop
               , reserved "Bot"    $> TyBot
               , upperIdentifier <#> TyVar
               , recordTy
               , parens t
               ]

sortTy :: SParser Ty -> SParser Ty
sortTy t = angles do
  ti <- t
  to <- optional (symbol "%" *> t)
  pure $ TySort ti to

forallTy :: SParser Ty
forallTy = do
  reserved "forall"
  xs <- some (params upperIdentifier "*")
  symbol "."
  t <- ty
  pure $ TyForall xs t

traitTy :: SParser Ty
traitTy = do
  reserved "Trait"
  ti <- optional (try (ty <* symbol "%"))
  to <- aty ty
  pure $ TyTrait ti to

arrayTy :: SParser Ty
arrayTy = do
  reserved "Array"
  te <- aty ty
  pure $ TyArray te

recordTy :: SParser Ty
recordTy = braces $ TyRcd <$> sepEndBySemi do
  l <- identifier
  symbol ":"
  t <- ty
  pure $ Tuple l t

toperators :: OperatorTable Identity String Ty
toperators = [ [ Infix (reservedOp "&"  $> TyAnd) AssocLeft  ]
             , [ Infix (reservedOp "->" $> TyArrow) AssocRight ]
             ]

-- Helpers --

fromIntOrNumber :: Either Int Number -> Tm
fromIntOrNumber (Left int) = TmInt int
fromIntOrNumber (Right number) = TmDouble number

params :: SParser String -> String -> SParser (Tuple Name (Maybe Ty))
params id s = Tuple <$> param <*> pure Nothing <|>
              parens (Tuple <$> param <* symbol s <*> (Just <$> ty))
  where param = id <|> underscore

selfAnno :: SParser (Tuple Name Ty)
selfAnno = brackets $ Tuple <$> lowerIdentifier <* symbol ":" <*> ty

override :: SParser Boolean
override = do
  m <- optional (reserved "override")
  pure $ isJust m

-- Lexer --

zordDef :: LanguageDef
zordDef = LanguageDef (unGenLanguageDef haskellStyle) { reservedNames =
  [ "true", "false", "trait", "implements", "inherits", "override", "new"
  , "if", "then", "else", "let", "letrec", "open", "in", "toString"
  , "type", "extends", "forall"
  , "Int", "Double", "String", "Bool", "Top", "Bot", "Trait", "Array"
  ]
}

zord :: TokenParser
zord = makeTokenParser zordDef

identifier :: SParser String
identifier = zord.identifier

reserved :: String -> SParser Unit
reserved = zord.reserved

operator :: SParser String
operator = zord.operator

reservedOp :: String -> SParser Unit
reservedOp = zord.reservedOp

stringLiteral :: SParser String
stringLiteral = zord.stringLiteral

naturalOrFloat :: SParser (Either Int Number)
naturalOrFloat = zord.naturalOrFloat

symbol :: String -> SParser Unit
symbol s = zord.symbol s $> unit

underscore :: SParser String
underscore = zord.symbol "_"

tripleQuotes :: SParser String
tripleQuotes = string "\"\"\""

lexeme :: forall a. SParser a -> SParser a
lexeme = zord.lexeme

whiteSpace :: SParser Unit
whiteSpace = zord.whiteSpace

parens :: forall a. SParser a -> SParser a
parens = zord.parens

braces :: forall a. SParser a -> SParser a
braces = zord.braces

angles :: forall a. SParser a -> SParser a
angles = zord.angles

brackets :: forall a. SParser a -> SParser a
brackets = zord.brackets

sepEndBySemi :: forall a. SParser a -> SParser (List a)
sepEndBySemi p = sepEndBy p (symbol ";")

lower :: SParser Char
lower = satisfy isLower

ident :: SParser Char -> SParser String
ident identStart = lexeme $ try do
  let languageDef = unGenLanguageDef zordDef
  c <- identStart
  cs <- Array.many languageDef.identLetter
  let word = CodeUnits.singleton c <> CodeUnits.fromCharArray cs
  if not (Array.elem word languageDef.reservedNames) then pure word
  else fail $ "reserved word " <> show word

lowerIdentifier :: SParser String
lowerIdentifier = ident lower

upperIdentifier :: SParser String
upperIdentifier = ident upper

stringTill :: forall a. SParser a -> SParser String
stringTill p =
  CodeUnits.fromCharArray <<< toUnfoldable <$> manyTill anyChar (lookAhead p)
