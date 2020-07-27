module Zord.Parser where

import Prelude hiding (between)

import Control.Alt ((<|>))
import Control.Lazy (fix)
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.List (List, foldl, many, some)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Text.Parsing.Parser (Parser, position)
import Text.Parsing.Parser.Combinators (choice)
import Text.Parsing.Parser.Expr (Assoc(..), Operator(..), OperatorTable, buildExprParser)
import Text.Parsing.Parser.Language (haskellStyle)
import Text.Parsing.Parser.String (char)
import Text.Parsing.Parser.Token (GenLanguageDef(..), LanguageDef, TokenParser, makeTokenParser, unGenLanguageDef)
import Zord.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), LogicOp(..), UnOp(..), Name, foldl1)
import Zord.Syntax.Source (Tm(..), Ty(..))

type SParser a = Parser String a

-- Expressions --

expr :: SParser Tm
expr = fix $ \e -> position >>= \p -> TmPos p <$> colonexpr e

colonexpr :: SParser Tm -> SParser Tm
colonexpr e = opexpr e >>= \e' -> TmAnno e' <$ symbol ":" <*> ty <|> pure e'

opexpr :: SParser Tm -> SParser Tm
opexpr e = buildExprParser operators $ lexpr e

lexpr :: SParser Tm -> SParser Tm
lexpr e = fexpr e <|> lambdaAbs <|> tyLambdaAbs <|>
          ifThenElse <|> letIn <|> letrec <|> open

fexpr :: SParser Tm -> SParser Tm
fexpr e = dotexpr e >>= \e' -> foldl (#) e' <$>
  many (flip TmTApp <$ char '@' <*> aty ty <|> flip TmApp <$> dotexpr e)

dotexpr :: SParser Tm -> SParser Tm
dotexpr e = aexpr e >>= \e' -> foldl (#) e' <$>
  many (flip TmPrj <$ char '.' <*> identifier)

aexpr :: SParser Tm -> SParser Tm
aexpr e = choice [ naturalOrFloat <#> fromIntOrNumber
                 , stringLiteral  <#> TmString
                 , reserved "true"  $> TmBool true
                 , reserved "false" $> TmBool false
                 , symbol "()" $> TmUnit
                 , identifier <#> TmVar
                 , recordLit
                 , parens e
                 ]

lambdaAbs :: SParser Tm
lambdaAbs = do
  symbol "\\"
  xs <- some (params ":")
  symbol "->"
  e <- expr
  pure $ TmAbs xs e

tyLambdaAbs :: SParser Tm
tyLambdaAbs = do
  symbol "/\\"
  xs <- some (params "*")
  symbol "."
  e <- expr
  pure $ TmTAbs xs e

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
  x <- identifier
  symbol "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  pure $ TmLet x e1 e2

letrec :: SParser Tm
letrec = do
  reserved "letrec"
  x <- identifier
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

-- TODO: reject "{}"
recordLit :: SParser Tm
recordLit = braces $ TmRcd <$> semiSep do
  l <- identifier
  symbol "="
  e <- expr
  pure $ Tuple l e

operators :: OperatorTable Identity String Tm
operators = [ [ Prefix (reservedOp "-" $> TmUnary Neg)
              , Prefix (reservedOp "!" $> TmUnary Not)
              ]
            , [ Infix (reservedOp "*" $> TmBinary (Arith Mul)) AssocLeft
              , Infix (reservedOp "/" $> TmBinary (Arith Div)) AssocLeft
              , Infix (reservedOp "%" $> TmBinary (Arith Mod)) AssocLeft
              ]
            , [ Infix (reservedOp "+" $> TmBinary (Arith Add)) AssocLeft
              , Infix (reservedOp "-" $> TmBinary (Arith Sub)) AssocLeft
              ]
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
bty t = foldl1 TyApp <$> some (aty t) <|> forallTy

aty :: SParser Ty -> SParser Ty
aty t = choice [ reserved "Int"    $> TyInt
               , reserved "Double" $> TyDouble
               , reserved "String" $> TyString
               , reserved "Bool"   $> TyBool
               , reserved "Top"    $> TyTop
               , reserved "Bot"    $> TyBot
               , identifier <#> TyVar
               , recordTy
               , parens t
               ]

forallTy :: SParser Ty
forallTy = do
  reserved "forall"
  xs <- some (params "*")
  symbol "."
  t <- ty
  pure $ TyForall xs t

-- TODO: reject "{}"
recordTy :: SParser Ty
recordTy = braces $ TyRcd <$> semiSep do
  l <- identifier
  symbol ":"
  t <- ty
  pure $ Tuple l t

toperators :: OperatorTable Identity String Ty
toperators = [ [ Infix (reservedOp "&"  $> TyAnd) AssocLeft  ]
             , [ Infix (reservedOp "->" $> TyArr) AssocRight ]
             ]

-- Helpers --

fromIntOrNumber :: Either Int Number -> Tm
fromIntOrNumber (Left int) = TmInt int
fromIntOrNumber (Right number) = TmDouble number

params :: String -> SParser (Tuple Name (Maybe Ty))
params s = Tuple <$> identifier <*> pure Nothing <|>
           parens (Tuple <$> identifier <* symbol s <*> (Just <$> ty))

-- Lexer --

zordDef :: LanguageDef
zordDef = LanguageDef (unGenLanguageDef haskellStyle) { reservedNames =
  [ "true", "false", "if", "then", "else", "let", "letrec", "open", "in"
  , "forall", "Int", "Double", "String", "Bool", "Top", "Bot"
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

parens :: forall a. SParser a -> SParser a
parens = zord.parens

braces :: forall a. SParser a -> SParser a
braces = zord.braces

angles :: forall a. SParser a -> SParser a
angles = zord.angles

brackets :: forall a. SParser a -> SParser a
brackets = zord.brackets

semiSep :: forall a. SParser a -> SParser (List a)
semiSep = zord.semiSep
