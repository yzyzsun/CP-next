module Zord.Parser where

import Prelude hiding (between)

import Control.Alt ((<|>))
import Control.Lazy (fix)
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.List (List(..), foldl, many)
import Partial.Unsafe (unsafeCrashWith)
import Text.Parsing.Parser (Parser)
import Text.Parsing.Parser.Combinators (choice)
import Text.Parsing.Parser.Expr (Assoc(..), Operator(..), OperatorTable, buildExprParser)
import Text.Parsing.Parser.Language (haskellStyle)
import Text.Parsing.Parser.String (char)
import Text.Parsing.Parser.Token (GenLanguageDef(..), LanguageDef, TokenParser, makeTokenParser, unGenLanguageDef)
import Zord.Syntax (ArithOp(..), BinOp(..), CompOp(..), Expr(..), LogicOp(..), Ty(..), UnOp(..))

type SParser a = Parser String a

foldl1 :: forall a. (a -> a -> a) -> List a -> a
foldl1 _ Nil = unsafeCrashWith "foldl1: empty list"
foldl1 f (Cons x xs) = foldl f x xs

-- Expressions --

expr :: SParser Expr
expr = fix $ \e -> opexpr e
  >>= \e' -> TmAnno e' <$ symbol ":" <*> ty <|> pure e'

opexpr :: SParser Expr -> SParser Expr
opexpr e = buildExprParser operators $ lexpr e

lexpr :: SParser Expr -> SParser Expr
lexpr e = fexpr e <|> lambdaAbs <|> fixedPoint <|> tyLambdaAbs <|>
          ifThenElse <|> letIn <|> openIn

fexpr :: SParser Expr -> SParser Expr
fexpr e = dotexpr e >>= \e' -> foldl (#) e' <$>
  many (flip TmTApp <$ char '@' <*> aty ty <|> flip TmApp <$> dotexpr e)

dotexpr :: SParser Expr -> SParser Expr
dotexpr e = aexpr e >>= \e' -> TmPrj e' <$ char '.' <*> identifier <|> pure e'

aexpr :: SParser Expr -> SParser Expr
aexpr e = choice [ naturalOrFloat <#> fromIntOrNumber
                 , stringLiteral  <#> TmString
                 , reserved "true"  $> TmBool true
                 , reserved "false" $> TmBool false
                 , symbol "()" $> TmUnit
                 , identifier <#> TmVar
                 , recordLit
                 , parens e
                 ]

lambdaAbs :: SParser Expr
lambdaAbs = do
  symbol "\\"
  x <- identifier
  symbol "->"
  e <- expr
  case e of
    TmAnno e' t -> case t of
      TyArr targ tret -> pure $ TmAbs x e' targ tret
      _ -> unsafeCrashWith "Zord.Parser.lambdaAbs: expected an arrow type in the annotation"
    _ -> unsafeCrashWith "Zord.Parser.lambdaAbs: must be annotated with a function type"

fixedPoint :: SParser Expr
fixedPoint = do
  reserved "fix"
  x <- identifier
  symbol "->"
  e <- expr
  case e of
    TmAnno e' t -> pure $ TmFix x e' t
    _ -> unsafeCrashWith "Zord.Parser.fixedPoint: must be annotated with a type"

tyLambdaAbs :: SParser Expr
tyLambdaAbs = do
  symbol "/\\"
  a <- identifier
  symbol "*"
  td <- ty
  symbol "."
  e <- expr
  case e of
    TmAnno e' t -> pure $ TmTAbs a td e' t
    _ -> unsafeCrashWith "Zord.Parser.tyLambdaAbs: must be annotated with a type"

ifThenElse :: SParser Expr
ifThenElse = do
  reserved "if"
  e1 <- expr
  reserved "then"
  e2 <- expr
  reserved "else"
  e3 <- expr
  pure $ TmIf e1 e2 e3

letIn :: SParser Expr
letIn = do
  reserved "let"
  x <- identifier
  symbol "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  pure $ TmLet x e1 e2

openIn :: SParser Expr
openIn = do
  reserved "open"
  e1 <- expr
  reserved "in"
  e2 <- expr
  pure $ TmOpen e1 e2

recordLit :: SParser Expr
recordLit = braces do
  l <- identifier
  symbol "="
  e <- expr
  pure $ TmRec l e

fromIntOrNumber :: Either Int Number -> Expr
fromIntOrNumber (Left int) = TmInt int
fromIntOrNumber (Right number) = TmDouble number

operators :: OperatorTable Identity String Expr
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
            , [ Infix (reservedOp ",," $> TmMerge) AssocLeft ]
            ]

-- Types --

ty :: SParser Ty
ty = fix \t -> buildExprParser toperators $ bty t

bty :: SParser Ty -> SParser Ty
bty t = aty t <|> forallTy

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
  a <- identifier
  symbol "*"
  td <- ty
  symbol "."
  t <- ty
  pure $ TyForall a td t

recordTy :: SParser Ty
recordTy = braces do
  l <- identifier
  symbol ":"
  t <- ty
  pure $ TyRec l t

toperators :: OperatorTable Identity String Ty
toperators = [ [ Infix (reservedOp "&"  $> TyAnd) AssocLeft  ]
             , [ Infix (reservedOp "->" $> TyArr) AssocRight ]
             ]

-- Lexer --

zordDef :: LanguageDef
zordDef = LanguageDef (unGenLanguageDef haskellStyle) { reservedNames =
  [ "true", "false", "fix", "if", "then", "else", "let", "open", "in"
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

commaSep :: forall a. SParser a -> SParser (List a)
commaSep = zord.commaSep
