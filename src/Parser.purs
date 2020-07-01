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
import Text.Parsing.Parser.Token (GenLanguageDef(..), LanguageDef, TokenParser, makeTokenParser, unGenLanguageDef)
import Zord.Syntax (ArithOp(..), BinOp(..), CompOp(..), Expr(..), LogicOp(..), Ty(..), UnOp(..))

type SParser a = Parser String a

foldl1 :: forall a. (a -> a -> a) -> List a -> a
foldl1 _ Nil = unsafeCrashWith "foldl1: empty list"
foldl1 f (Cons x xs) = foldl f x xs

-- Expressions --

expr :: SParser Expr
expr = fix $ \e -> opexpr e
  >>= \e' -> Anno e' <$ reservedOp ":" <*> ty <|> pure e'

opexpr :: SParser Expr -> SParser Expr
opexpr e = buildExprParser operators $ lexpr e

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
            ]

lexpr :: SParser Expr -> SParser Expr
lexpr e = choice [ fexpr e
                 , lambdaAbstraction
                 ]

lambdaAbstraction :: SParser Expr
lambdaAbstraction = do
  reservedOp "\\"
  reservedOp "("
  x <- identifier
  reservedOp ":"
  t <- ty
  reservedOp ")"
  reservedOp "->"
  e <- expr
  pure $ Abs x t e

fexpr :: SParser Expr -> SParser Expr
fexpr e = some (aexpr e) <#> foldl1 App

aexpr :: SParser Expr -> SParser Expr
aexpr e = choice [ naturalOrFloat <#> fromIntOrNumber
                 , stringLiteral <#> StrLit
                 , reserved "true" $> BoolLit true
                 , reserved "false" $> BoolLit false
                 , reservedOp "()" $> UnitLit
                 , identifier <#> Var
                 , parens e
                 ]

fromIntOrNumber :: Either Int Number -> Expr
fromIntOrNumber (Left int) = IntLit int
fromIntOrNumber (Right number) = DoubleLit number

-- Types --

ty :: SParser Ty
ty = fix \t -> buildExprParser toperators $ aty t

toperators :: OperatorTable Identity String Ty
toperators = [[ Infix (reservedOp "->" $> Arr) AssocRight ]]

aty :: SParser Ty -> SParser Ty
aty t = choice [ reserved "Int"    $> Integer
               , reserved "Double" $> Double
               , reserved "String" $> Str
               , reserved "Bool"   $> Bool
               , reserved "Top"    $> Top
               , reserved "Bot"    $> Bot
               , parens t
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
