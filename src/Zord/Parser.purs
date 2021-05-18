module Zord.Parser where

import Prelude hiding (between)

import Control.Alt ((<|>))
import Control.Lazy (fix)
import Control.Monad.State (gets, modify_)
import Data.Array as Array
import Data.Array.NonEmpty (head)
import Data.CodePoint.Unicode (isLower, isUpper)
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.List (List, foldl, many, null, some, toUnfoldable)
import Data.Maybe (Maybe(..), fromMaybe, isJust, optional)
import Data.String (codePointAt, codePointFromChar)
import Data.String.CodeUnits as SCU
import Data.String.Regex (Regex, match, regex, replace)
import Data.String.Regex.Flags (noFlags)
import Data.Tuple (Tuple(..))
import Text.Parsing.Parser (ParseState(..), Parser, fail, position)
import Text.Parsing.Parser.Combinators (between, choice, sepEndBy, try)
import Text.Parsing.Parser.Expr (Assoc(..), Operator(..), OperatorTable, buildExprParser)
import Text.Parsing.Parser.Language (haskellStyle)
import Text.Parsing.Parser.Pos (updatePosString)
import Text.Parsing.Parser.String (char, satisfy, skipSpaces)
import Text.Parsing.Parser.Token (GenLanguageDef(..), LanguageDef, TokenParser, makeTokenParser, unGenLanguageDef, upper)
import Zord.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), LogicOp(..), Name, UnOp(..))
import Zord.Syntax.Source (MethodPattern(..), RcdField(..), Tm(..), TmParam(..), Ty(..), TyParam)
import Zord.Util (foldl1, unsafeFromJust, unsafeFromRight)

type SParser a = Parser String a

-- Program --

program :: SParser Tm
program = fix $ \p -> tyDef p <|> tmDef p <|> expr

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
  def <- try do
    x <- lowerIdentifier
    tys <- many (try $ tyParams false)
    tms <- many tmParams
    t <- optional (symbol ":" *> ty)
    symbol "="
    pure $ TmDef x tys tms t
  e1 <- expr
  symbol ";"
  e2 <- p
  pure $ def e1 e2

-- Expressions --

expr :: SParser Tm
expr = fix $ \e -> position >>= \p -> TmPos p <$> colonexpr e

colonexpr :: SParser Tm -> SParser Tm
colonexpr e = opexpr e >>= \e' ->
  TmAnno e' <$ symbol ":" <*> ty <|>
  TmExclude e' <$ symbol "\\" <*> ty <|>
  pure e'

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
                 , between (char '`') (symbol "`") $ document e
                 , stringLiteral <#> TmString
                 , reserved "true"  $> TmBool true
                 , reserved "false" $> TmBool false
                 , symbol "()" $> TmUnit
                 , reserved "undefined" $> TmUndefined
                 , identifier <#> TmVar
                 , brackets $ TmArray <<< toUnfoldable <$> sepEndBySemi e
                 , recordLit e
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

document :: SParser Tm -> SParser Tm
document p = do
  docs <- many (backslash <|> plaintext)
  pure $ if null docs then newStr (TmString "") else foldl1 newComp docs
  where
    backslash = char '\\' *> (command <|> interpolation <|> newline)
    command = do
      cmd <- identifier
      e <- optional $ recordArg cmd <|> juxtaArgs cmd
      docs <- many $ try $ skipSpaces *> bracketsWithoutConsumingSpace (document p)
      let f = if isUpper $ unsafeFromJust $ codePointAt 0 cmd then TmNew else identity
      pure $ f (foldl TmApp (fromMaybe (TmVar cmd) e) docs)
    recordArg cmd = TmApp (TmVar cmd) <<< TmRcd <$>
      between (symbol "{") (char '}') (sepEndBySemi $ recordField p false)
    juxtaArgs cmd = foldl TmApp (TmVar cmd) <$>
      parensWithoutTrailingSpace (many (dotexpr p))
    interpolation = newStr <<< TmToString <$> parensWithoutTrailingSpace p
    newline = char '\\' $> newEndl
    plaintext = newStr <<< TmString <$> stringMatching re
    re = unsafeFromRight $ regex """^[^\\\]`]+""" noFlags

parensWithoutTrailingSpace :: forall a. SParser a -> SParser a
parensWithoutTrailingSpace = between (symbol "(") (char ')')

bracketsWithoutConsumingSpace :: forall a. SParser a -> SParser a
bracketsWithoutConsumingSpace = between (char '[') (char ']')

newCtor :: String -> Tm
newCtor = TmNew <<< TmVar

newEndl :: Tm
newEndl = newCtor "Endl"

newStr :: Tm -> Tm
newStr s = TmNew (TmApp (TmVar "Str") s)

newComp :: Tm -> Tm -> Tm
newComp x y = TmNew (TmApp (TmApp (TmVar "Comp") x) y)

recordLit :: SParser Tm -> SParser Tm
recordLit p = braces $ TmRcd <$> sepEndBySemi do
  o <- isJust <$> optional (reserved "override")
  recordField p o <|> methodPattern p o <|> defaultPattern p

recordField :: SParser Tm -> Boolean -> SParser RcdField
recordField p o = do
  l <- identifier
  params <- many tmParams
  symbol "="
  e <- p
  pure $ RcdField o l params (Left e)

methodPattern :: SParser Tm -> Boolean -> SParser RcdField
methodPattern p o = do
  symbol "("
  l <- identifier
  params <- many tmParams
  self <- optional selfAnno
  symbol ")"
  symbol "."
  l' <- identifier
  params' <- many tmParams
  symbol "="
  e <- p
  pure $ RcdField o l params (Right (MethodPattern self l' params' e))

defaultPattern :: SParser Tm -> SParser RcdField
defaultPattern p = do
  self <- Just <$> selfAnno <|> Nothing <$ underscore
  symbol "."
  l <- identifier
  params <- many tmParams
  symbol "="
  e <- p
  pure $ DefaultPattern (MethodPattern self l params e)

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
            , [ Infix (reservedOp "^" $> TmForward) AssocLeft ]
            , [ Infix (reservedOp "," $> TmMerge) AssocLeft ]
            ]

-- Types --

ty :: SParser Ty
ty = fix \t -> buildExprParser toperators $ bty t

bty :: SParser Ty -> SParser Ty
bty t = foldl TyApp <$> aty t <*> many (aty t <|> sortTy t) <|>
        forallTy <|> traitTy

aty :: SParser Ty -> SParser Ty
aty t = choice [ reserved "Int"    $> TyInt
               , reserved "Double" $> TyDouble
               , reserved "String" $> TyString
               , reserved "Bool"   $> TyBool
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
  to <- optional (symbol "%" *> t)
  pure $ TySort ti to

forallTy :: SParser Ty
forallTy = do
  reserved "forall"
  xs <- some (tyParams true)
  symbol "."
  t <- ty
  pure $ TyForall xs t

traitTy :: SParser Ty
traitTy = do
  reserved "Trait"
  angles do
    ti <- optional (try (ty <* symbol "%"))
    to <- ty
    pure $ TyTrait ti to

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

tyParams :: Boolean -> SParser TyParam
tyParams us = Tuple <$> id <*> pure Nothing <|>
           parens (Tuple <$> id <* symbol "*" <*> (Just <$> ty))
  where id = if us then underscore <|> upperIdentifier else upperIdentifier

tmParams :: SParser TmParam
tmParams = choice [ parensNameColonType
                  , TmParam <$> id <@> Nothing
                  , WildCard <$ braces (symbol "..")
                  ]
  where parensNameColonType = parens do
          x <- id
          symbol ":"
          t <- ty
          pure $ TmParam x (Just t)
        id = lowerIdentifier <|> underscore

selfAnno :: SParser (Tuple Name Ty)
selfAnno = brackets $ Tuple <$> lowerIdentifier <* symbol ":" <*> ty

-- Lexer --

zordDef :: LanguageDef
zordDef = LanguageDef (unGenLanguageDef haskellStyle) { reservedNames =
  [ "true", "false", "undefined", "if", "then", "else", "toString"
  , "trait", "implements", "inherits", "override", "new"
  , "let", "letrec", "open", "in", "type", "extends", "forall"
  , "Int", "Double", "String", "Bool", "Top", "Bot", "Trait"
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
lower = satisfy $ isLower <<< codePointFromChar

ident :: SParser Char -> SParser String
ident identStart = lexeme $ try do
  let languageDef = unGenLanguageDef zordDef
  c <- identStart
  cs <- Array.many languageDef.identLetter
  let word = SCU.singleton c <> SCU.fromCharArray cs
  if not (Array.elem word languageDef.reservedNames) then pure word
  else fail $ "Unexpected reserved word " <> show word

lowerIdentifier :: SParser String
lowerIdentifier = ident lower

upperIdentifier :: SParser String
upperIdentifier = ident upper

stringMatching :: Regex -> SParser String
stringMatching re = do
  input <- gets \(ParseState input _ _) -> input
  case match re input of
    Just arr -> case head arr of
      Just str -> do
        modify_ \(ParseState _ position _) ->
          ParseState (replace re "" input) (updatePosString position str) true
        pure str
      Nothing -> fail $ "Failed to match " <> show re
    Nothing -> fail $ "Failed to match " <> show re
