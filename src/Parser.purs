module Zord.Parser where

import Prelude hiding (between)

import Control.Alt ((<|>))
import Control.Lazy (fix)
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.List (List(..), foldl, some)
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
  >>= \e' -> Anno e' <$ colon <*> ty <|> pure e'

opexpr :: SParser Expr -> SParser Expr
opexpr e = buildExprParser operators $ lexpr e

lexpr :: SParser Expr -> SParser Expr
lexpr e = fexpr e <|> lambdaAbs <|> fixedPoint

fexpr :: SParser Expr -> SParser Expr
fexpr e = some (dotexpr e) <#> foldl1 App

dotexpr :: SParser Expr -> SParser Expr
dotexpr e = aexpr e >>= \e' -> RecPrj e' <$ char '.' <*> identifier <|> pure e'

aexpr :: SParser Expr -> SParser Expr
aexpr e = choice [ naturalOrFloat <#> fromIntOrNumber
                 , stringLiteral <#> StrLit
                 , reserved "true" $> BoolLit true
                 , reserved "false" $> BoolLit false
                 , reservedOp "()" $> UnitLit
                 , identifier <#> Var
                 , recordLit
                 , parens e
                 ]

lambdaAbs :: SParser Expr
lambdaAbs = do
  reservedOp "\\"
  x <- identifier
  reservedOp "->"
  e <- expr
  case e of
    Anno e' t -> case t of
      Arr targ tret -> pure $ Abs x e' targ tret
      _ -> unsafeCrashWith "Zord.Parser.lambdaAbs: expected an arrow type in the annotation"
    _ -> unsafeCrashWith "Zord.Parser.lambdaAbs: must be annotated with a function type"

fixedPoint :: SParser Expr
fixedPoint = do
  reserved "fix"
  x <- identifier
  reservedOp "->"
  e <- expr
  case e of
    Anno e' t -> pure $ Fix x e' t
    _ -> unsafeCrashWith "Zord.Parser.fixedPoint: must be annotated with a type"

recordLit :: SParser Expr
recordLit = braces do
  l <- identifier
  reservedOp "="
  e <- expr
  pure $ RecLit l e

fromIntOrNumber :: Either Int Number -> Expr
fromIntOrNumber (Left int) = IntLit int
fromIntOrNumber (Right number) = DoubleLit number

operators :: OperatorTable Identity String Expr
operators = [ [ Prefix (reservedOp "-" $> Unary Neg)
              , Prefix (reservedOp "!" $> Unary Not)
              ]
            , [ Infix (reservedOp "*" $> Binary (Arith Mul)) AssocLeft
              , Infix (reservedOp "/" $> Binary (Arith Div)) AssocLeft
              , Infix (reservedOp "%" $> Binary (Arith Mod)) AssocLeft
              ]
            , [ Infix (reservedOp "+" $> Binary (Arith Add)) AssocLeft
              , Infix (reservedOp "-" $> Binary (Arith Sub)) AssocLeft
              ]
            , [ Infix (reservedOp "==" $> Binary (Comp Eql)) AssocNone
              , Infix (reservedOp "!=" $> Binary (Comp Neq)) AssocNone
              , Infix (reservedOp "<"  $> Binary (Comp Lt )) AssocNone
              , Infix (reservedOp "<=" $> Binary (Comp Le )) AssocNone
              , Infix (reservedOp ">"  $> Binary (Comp Gt )) AssocNone
              , Infix (reservedOp ">=" $> Binary (Comp Ge )) AssocNone
              ]
            , [ Infix (reservedOp "&&" $> Binary (Logic And)) AssocRight ]
            , [ Infix (reservedOp "||" $> Binary (Logic Or )) AssocRight ]
            , [ Infix (reservedOp ",," $> Merge) AssocLeft ]
            ]

-- Types --

ty :: SParser Ty
ty = fix \t -> buildExprParser toperators $ aty t

aty :: SParser Ty -> SParser Ty
aty t = choice [ reserved "Int"    $> Integer
               , reserved "Double" $> Double
               , reserved "String" $> Str
               , reserved "Bool"   $> Bool
               , reserved "Top"    $> Top
               , reserved "Bot"    $> Bot
               , recordTy
               , parens t
               ]

recordTy :: SParser Ty
recordTy = braces do
  l <- identifier
  _ <- colon
  t <- ty
  pure $ Rec l t

toperators :: OperatorTable Identity String Ty
toperators = [ [ Infix (reservedOp "&" $> Intersect) AssocLeft ]
             , [ Infix (reservedOp "->" $> Arr) AssocRight ]
             ]

-- Lexer --

zordDef :: LanguageDef
zordDef = LanguageDef (unGenLanguageDef haskellStyle)
            { reservedNames = []
            , reservedOpNames = []
            }

zord :: TokenParser
zord = makeTokenParser zordDef

identifier :: SParser String
identifier = zord.identifier

reserved :: String -> SParser Unit
reserved = zord.reserved

reservedOp :: String -> SParser Unit
reservedOp = zord.reservedOp

stringLiteral :: SParser String
stringLiteral = zord.stringLiteral

naturalOrFloat :: SParser (Either Int Number)
naturalOrFloat = zord.naturalOrFloat

parens :: forall a. SParser a -> SParser a
parens = zord.parens

braces :: forall a. SParser a -> SParser a
braces = zord.braces

angles :: forall a. SParser a -> SParser a
angles = zord.angles

brackets :: forall a. SParser a -> SParser a
brackets = zord.brackets

semi :: SParser String
semi = zord.semi

comma :: SParser String
comma = zord.comma

colon :: SParser String
colon = zord.colon

dot :: SParser String
dot = zord.dot

semiSep :: forall a. SParser a -> SParser (List a)
semiSep = zord.semiSep

commaSep :: forall a. SParser a -> SParser (List a)
commaSep = zord.commaSep
