module Language.CP.CodeGen where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.RWS (RWST, asks, evalRWST, local, modify)
import Data.Array (all, concat, find, foldl, length, notElem, (!!))
import Data.Array as A
import Data.Bifunctor (bimap, lmap, rmap)
import Data.Either (Either)
import Data.Int (toNumber)
import Data.List (List(..), elem, (:))
import Data.Map (Map, empty, fromFoldable, insert, lookup)
import Data.Maybe (Maybe(..), isJust)
import Data.String (Pattern(..), Replacement(..), joinWith, replaceAll, stripPrefix, stripSuffix, toLower)
import Data.Traversable (traverse)
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Context (REPLState)
import Language.CP.Subtyping (isTopLike, split, (===))
import Language.CP.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), LogicOp(..), UnOp(..)) as Op
import Language.CP.Syntax.Common (Label, Name)
import Language.CP.Syntax.Core as C
import Language.CP.Typing (selectLabel)
import Language.CP.Util (unsafeFromJust, (<+>))
import Language.JS.AST (BinaryOperator(..), JS(..), UnaryOperator(..))
import Language.JS.Pretty (print1)
import Partial.Unsafe (unsafeCrashWith)

type CodeGen = RWST Ctx Unit Int (Except String)

type Ctx = { tmBindEnv :: Map Name C.Ty
           , tyBindEnv :: Map Name C.Ty
           , evalOrder :: EvalOrder
           , inTrait   :: Boolean
           }

data EvalOrder = CBV -- call by value
               | CBN -- call by need
derive instance Eq EvalOrder

emptyCtx :: Ctx
emptyCtx = { tmBindEnv: empty
           , tyBindEnv: empty
           , evalOrder: CBN
           , inTrait: false
           }

fromState :: REPLState -> Ctx
fromState st = emptyCtx { tmBindEnv = fromFoldable $ rmap fst <$> st.tmBindings }

runCodeGen :: C.Tm -> Ctx -> Either String (Array JS)
runCodeGen e ctx = do
  { ast } /\ _ <- runExcept $ evalRWST (infer e DstNil) ctx 0
  pure $ [ JSRawCode prelude ] <> ast

prelude :: String
prelude = """function copyObj(dst, src) {
    for (const prop in src) {
        var getter = src.__lookupGetter__(prop);
        if (getter) dst.__defineGetter__(prop, getter);
        else dst[prop] = src[prop];
    }
}
function primitive(tt) {
    var pt = ['int', 'double', 'string', 'bool'];
    if (tt.length === 1 && pt.includes(tt[0])) return tt[0];
    else return null;
}
function toIndex(tt) {
    var ts = tt.sort().filter((t, i) => t === 0 || t !== tt[i-1]);
    if (ts.length === 1) return ts[0];
    else return '(' + ts.join('&') + ')';
}"""

type AST = Array JS
type InferResult = { ast :: AST, typ :: C.Ty, var :: Name }
type CheckResult = { ast :: AST, var :: Name }

data Destination = DstNil | DstOpt Name | DstVar Name

dstOpt :: Name -> CodeGen CheckResult
dstOpt y = do
  var <- freshVarName
  let init = JSBinary Or (JSVar y) (JSObjectLiteral [])
  pure { ast: [ JSVariableIntroduction var $ Just init ], var }

dstNil :: CodeGen CheckResult
dstNil = do
  var <- freshVarName
  pure { ast: [ initialize var ], var }

infer :: C.Tm -> Destination -> CodeGen InferResult
infer C.TmUnit (DstVar z) = pure { ast: [], typ: C.TyUnit, var: z }
infer C.TmTop (DstVar z) = pure { ast: [], typ: C.TyTop, var: z }
infer C.TmUndefined (DstVar z) = pure { ast: [], typ: C.TyBot, var: z }
infer (C.TmInt i) dst = do
  var <- freshVarName
  let intro = JSVariableIntroduction var $ Just (JSNumericLiteral (toNumber i))
      assign z = addProp (JSVar z) (toIndex C.TyInt) (JSNumericLiteral (toNumber i))
      ast = case dst of DstVar z -> [ assign z ]
                        DstOpt z -> [ intro, JSIfElse (JSVar z) (assign z) Nothing ]
                        DstNil -> [ intro ]
  pure { ast, typ: C.TyInt, var }
infer (C.TmDouble d) dst = do
  var <- freshVarName
  let intro = JSVariableIntroduction var $ Just (JSNumericLiteral d)
      assign z = addProp (JSVar z) (toIndex C.TyDouble) (JSNumericLiteral d)
      ast = case dst of DstVar z -> [ assign z ]
                        DstOpt z -> [ intro, JSIfElse (JSVar z) (assign z) Nothing ]
                        DstNil -> [ intro ]
  pure { ast, typ: C.TyDouble, var }
infer (C.TmString s) dst = do
  var <- freshVarName
  let intro = JSVariableIntroduction var $ Just (JSStringLiteral s)
      assign z = addProp (JSVar z) (toIndex C.TyString) (JSStringLiteral s)
      ast = case dst of DstVar z -> [ assign z ]
                        DstOpt z -> [ intro, JSIfElse (JSVar z) (assign z) Nothing ]
                        DstNil -> [ intro ]
  pure { ast, typ: C.TyString, var }
infer (C.TmBool b) dst = do
  var <- freshVarName
  let intro = JSVariableIntroduction var $ Just (JSBooleanLiteral b)
      assign z = addProp (JSVar z) (toIndex C.TyBool) (JSBooleanLiteral b)
      ast = case dst of DstVar z -> [ assign z ]
                        DstOpt z -> [ intro, JSIfElse (JSVar z) (assign z) Nothing ]
                        DstNil -> [ intro ]
  pure { ast, typ: C.TyBool, var }
infer (C.TmArray t arr) (DstVar z) = do
  arr' <- traverse (flip infer DstNil) arr
  let js = arr' <#> (_.ast)
      vs = arr' <#> (_.var) >>> JSVar
      ast = concat js <> [ addProp (JSVar z) (toIndex (C.TyArray t)) (JSArrayLiteral vs) ]
  pure { ast, typ: C.TyArray t, var: z }
infer (C.TmUnary Op.Neg e) dst = do
  { ast: j0, typ: t, var: y } <- infer e DstNil
  var <- freshVarName
  let j1 = [ JSVariableIntroduction var $ Just $ JSUnary Negate (JSVar y) ]
      assign z typ = addProp (JSVar z) (toIndex typ) (JSVar var)
      j2 typ = case dst of DstVar z -> [ assign z typ ]
                           DstOpt z -> [ JSIfElse (JSVar z) (assign z typ) Nothing ]
                           DstNil -> []
  case t of C.TyInt    -> pure { ast: j0 <> j1 <> j2 C.TyInt,    typ: C.TyInt,    var }
            C.TyDouble -> pure { ast: j0 <> j1 <> j2 C.TyDouble, typ: C.TyDouble, var }
            _ -> throwError $ "Neg is not defined for" <+> show t
infer (C.TmUnary Op.Len e) dst = do
  { ast: j0, typ: t, var: y } <- infer e DstNil
  var <- freshVarName
  let j1 = [ JSVariableIntroduction var $ Just $ JSAccessor "length" (JSIndexer (toIndex t) (JSVar y)) ]
      assign z = addProp (JSVar z) (toIndex C.TyInt) (JSVar y)
      j2 = case dst of DstVar z -> [ assign z ]
                       DstOpt z -> [ JSIfElse (JSVar z) (assign z) Nothing ]
                       DstNil -> []
  pure { ast: j0 <> j1 <> j2, typ: C.TyInt, var }
infer (C.TmUnary Op.Sqrt e) dst = do
  { ast: j0, var: y } <- infer e DstNil
  var <- freshVarName
  let j1 = [ JSVariableIntroduction var $ Just $ JSApp (JSAccessor "sqrt" (JSVar "Math")) [JSVar y] ]
      assign z = addProp (JSVar z) (toIndex C.TyDouble) (JSVar var)
      j2 = case dst of DstVar z -> [ assign z ]
                       DstOpt z -> [ JSIfElse (JSVar z) (assign z) Nothing ]
                       DstNil -> []
  pure { ast: j0 <> j1 <> j2, typ: C.TyDouble, var }
infer (C.TmBinary (Op.Arith op) e1 e2) dst = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  { ast: j2, typ: t2, var: y } <- infer e2 DstNil
  var <- freshVarName
  let j3 flg = [ JSVariableIntroduction var $ Just $ (if flg then trunc else identity)
                                                     (JSBinary (map op) (JSVar x) (JSVar y)) ]
      assign z typ = addProp (JSVar z) (toIndex typ) (JSVar var)
      j4 typ = case dst of DstVar z -> [ assign z typ ]
                           DstOpt z -> [ JSIfElse (JSVar z) (assign z typ) Nothing ]
                           DstNil -> []
  case t1, t2 of C.TyInt,    C.TyInt    -> pure { ast: j1 <> j2 <> j3 (op == Op.Div) <> j4 C.TyInt
                                                , typ: C.TyInt, var }
                 C.TyDouble, C.TyDouble -> pure { ast: j1 <> j2 <> j3 false <> j4 C.TyDouble
                                                , typ: C.TyDouble, var }
                 _, _ -> throwError $
                   "ArithOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where map :: Op.ArithOp -> BinaryOperator
        map Op.Add = Add
        map Op.Sub = Subtract
        map Op.Mul = Multiply
        map Op.Div = Divide
        map Op.Mod = Modulus
        trunc :: JS -> JS
        trunc n = JSApp (JSAccessor "trunc" (JSVar "Math")) [n]
infer (C.TmBinary (Op.Comp op) e1 e2) dst = do
  { ast: j1, var: x } <- infer e1 DstNil
  { ast: j2, var: y } <- infer e2 DstNil
  var <- freshVarName
  let j3 = [ JSVariableIntroduction var $ Just $ JSBinary (map op) (JSVar x) (JSVar y) ]
      assign z = addProp (JSVar z) (toIndex C.TyBool) (JSVar z)
      j4 = case dst of DstVar z -> [ assign z ]
                       DstOpt z -> [ JSIfElse (JSVar z) (assign z) Nothing ]
                       DstNil -> []
  pure { ast: j1 <> j2 <> j3 <> j4, typ: C.TyBool, var }
  where map :: Op.CompOp -> BinaryOperator
        map Op.Eql = EqualTo
        map Op.Neq = NotEqualTo
        map Op.Lt  = LessThan
        map Op.Le  = LessThanOrEqualTo
        map Op.Gt  = GreaterThan
        map Op.Ge  = GreaterThanOrEqualTo
infer (C.TmBinary (Op.Logic op) e1 e2) dst = do
  { ast: j1, var: x } <- infer e1 DstNil
  { ast: j2, var: y } <- infer e2 DstNil
  var <- freshVarName
  let j3 = [ JSVariableIntroduction var $ Just $ JSBinary (map op) (JSVar x) (JSVar y) ]
      assign z = addProp (JSVar z) (toIndex C.TyBool) (JSVar var)
      j4 = case dst of DstVar z -> [ assign z ]
                       DstOpt z -> [ JSIfElse (JSVar z) (assign z) Nothing ]
                       DstNil -> []
  pure { ast: j1 <> j2 <> j3 <> j4, typ: C.TyBool, var }
  where map :: Op.LogicOp -> BinaryOperator
        map Op.And = And
        map Op.Or  = Or
infer (C.TmBinary Op.Append e1 e2) dst = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  { ast: j2, typ: t2, var: y } <- infer e2 DstNil
  case t1, t2 of
    C.TyString, C.TyString -> do
      var <- freshVarName
      let j3 = [ JSVariableIntroduction var $ Just $ JSBinary Add (JSVar x) (JSVar y) ]
          assign z = addProp (JSVar z) (toIndex C.TyString) (JSVar var)
          j4 = case dst of DstVar z -> [ assign z ]
                           DstOpt z -> [ JSIfElse (JSVar z) (assign z) Nothing ]
                           DstNil -> []
      pure { ast: j1 <> j2 <> j3 <> j4, typ: C.TyString, var }
    typ@(C.TyArray t), C.TyArray t' | t .=. t' -> do
      { ast: j3, var } <- case dst of DstVar z -> pure { ast: [], var: z }
                                      DstOpt z -> dstOpt z
                                      DstNil -> dstNil
      let ast = j1 <> j2 <> j3 <> [ addProp (JSVar var) (toIndex typ)
            (JSApp (JSAccessor "concat" (JSIndexer (toIndex typ) (JSVar x)))
                                        [JSIndexer (toIndex typ) (JSVar y)]) ]
      pure { ast, typ, var }
    _, _ -> throwError $
      "Append is not defined between" <+> show t1 <+> "and" <+> show t2
infer (C.TmBinary Op.Index e1 e2) dst = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  { ast: j2, typ: t2, var: y } <- infer e2 DstNil
  case t1, t2 of
    t@(C.TyArray typ), C.TyInt -> do
      var <- freshVarName
      let element = JSIndexer (JSVar y) (JSIndexer (toIndex t) (JSVar x))
          j3 = case dst of DstVar z -> [ copyObj z element typ ]
                           DstOpt z -> [ JSVariableIntroduction var $ Just element
                                       , JSIfElse (JSVar z) (copyObj z element typ) Nothing ]
                           DstNil -> [ JSVariableIntroduction var $ Just element ]
      pure { ast: j1 <> j2 <> j3, typ, var }
    _, _ -> throwError $
      "Index is not defined between" <+> show t1 <+> "and" <+> show t2
infer (C.TmIf e1 e2 e3) dst = do
  { ast: j1, typ: t1, var } <- infer e1 DstNil
  if t1 == C.TyBool then do
    { ast: j2, typ: t2, var: x } <- infer e2 dst
    { ast: j3, typ: t3, var: y } <- infer e3 dst
    if t2 .=. t3 then do
      let ifElse mz = let f2 = case mz of Nothing -> identity
                                          Just z -> (_ <> [ JSAssignment (JSVar z) (JSVar x) ])
                          f3 = case mz of Nothing -> identity
                                          Just z -> (_ <> [ JSAssignment (JSVar z) (JSVar y) ]) in
                      JSIfElse (JSVar var) (JSBlock (f2 j2)) (Just (JSBlock (f3 j3)))
      case dst of DstVar z -> pure { ast: j1 <> [ ifElse Nothing ], typ: t2, var: z }
                  _ -> do z <- freshVarName
                          pure { ast: j1 <> [ JSVariableIntroduction z Nothing, ifElse (Just z) ], typ: t2, var: z }
    else throwError $ "if-branches expected two equivalent types, but got"
                   <+> show t2 <+> "and" <+> show t3
  else throwError $ "if-condition expected Bool, but got" <+> show t1
infer (C.TmVar x) (DstVar z) = do
  typ <- lookupTmBind x
  pure { ast: [ copyObj z (JSVar (variable x)) typ ], typ, var: z }
infer (C.TmVar x) (DstOpt y) = do
  z <- freshVarName
  typ <- lookupTmBind x
  let ast = [ JSVariableIntroduction z $ Just $ JSVar $ variable x
            , JSIfElse (JSVar y) (copyObj y (JSVar z) typ) Nothing
            ]
  pure { ast, typ, var: variable x }
infer (C.TmVar x) DstNil = do
  typ <- lookupTmBind x
  pure { ast: [], typ, var: variable x }
infer (C.TmFix x e typ) (DstVar z) = do
  { ast: j } <- addTmBind x typ $ check e typ (DstVar z)
  -- TODO: `x` is always `$self` for `new` expressions; should generate fresh names to avoid name conflicts
  let ast = [ JSBlock $ [ JSConst (variable x) (JSVar z) ] <> j ]
  pure { ast, typ, var: z }
infer (C.TmAbs x e targ tret _ isTrait) (DstVar z)
  | isTopLike tret = infer C.TmTop (DstVar z)
  | otherwise = do
      y <- freshVarName
      { ast: j, var: y0 } <- addTmBind x targ $ setInTrait isTrait $ check e tret (DstOpt y)
      let typ = C.TyArrow targ tret isTrait
          fun = JSFunction Nothing [variable x, y] $ JSBlock $ j <> [JSReturn $ JSVar y0]
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure { ast, typ, var: z }
infer (C.TmApp e1 e2 _) dst = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  { ast: j2, typ: t2, var: y } <- infer e2 DstNil
  { ast: j3, typ: t3, var: z } <- distapp x t1 (TmArg y t2) dst
  pure { ast: j1 <> j2 <> j3, typ: t3, var: z }
infer (C.TmTAbs a td e t _) (DstVar z)
  | isTopLike t = infer C.TmTop (DstVar z)
  | otherwise = do
      y <- freshVarName
      { ast: j, var: y0 } <- addTyBind a td $ check e t (DstOpt y)
      let typ = C.TyForall a td t
          fun = JSFunction Nothing [variable a, y] $ JSBlock $ j <> [JSReturn $ JSVar y0]
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure { ast, typ, var: z }
infer (C.TmTApp e t) dst = do
  { ast: j1, typ: tf, var: y } <- infer e DstNil
  { ast: j2, typ: tbody, var: z } <- distapp y tf (TyArg t) dst
  pure { ast: j1 <> j2, typ: tbody, var: z }
infer (C.TmRcd l t e) (DstVar z)
  | isTopLike t = infer C.TmTop (DstVar z)
  | otherwise = do
      { ast: j, var: y } <- check e t DstNil
      order <- asks (_.evalOrder)
      inTrait <- asks (_.inTrait)
      let ast = if order == CBV || not inTrait
                then j <> [ addProp (JSVar z) (toIndex typ) (JSVar y) ]
                else [ addGetter (JSVar z) typ j y ]
          typ = C.TyRcd l t false
      pure { ast, typ, var: z }
infer (C.TmPrj e l) dst = do
  { ast: j1, typ: t1, var: y } <- infer e DstNil
  case selectLabel t1 l false of
    Just typ@(C.TyAnd _ _) -> do
      case dst of DstVar z -> do { ast: j2 } <- proj t1 y l (DstVar z) false
                                 pure { ast: j1 <> j2, typ, var: z }
                  DstOpt z' -> do { ast: j2, var: z } <- dstOpt z'
                                  { ast: j3 } <- proj t1 y l (DstVar z) false
                                  pure { ast: j1 <> j2 <> j3, typ, var: z }
                  DstNil -> do { ast: j2, var: z } <- dstNil
                               { ast: j3 } <- proj t1 y l (DstVar z) false
                               pure { ast: j1 <> j2 <> j3, typ, var: z }
    Just typ -> do
      { ast: j2, var } <- proj t1 y l dst false
      pure { ast: j1 <> j2, typ, var }
    _ -> throwError $ "label" <+> show l <+> "is absent in" <+> show t1
infer (C.TmOptPrj e1 l t e2) (DstVar z) = do
  { ast: j1, typ: t1, var: y } <- infer e1 DstNil
  { ast: j2 } <- infer e2 (DstVar z)
  { ast: j3 } <- proj t1 y l (DstVar z) true
  pure { ast: j1 <> j2 <> j3, typ: t, var: z }
infer e@(C.TmOptPrj _ _ _ _) (DstOpt y) = do
  { ast: j1, var } <- dstOpt y
  { ast: j2, typ } <- infer e (DstVar var)
  j3 <- convertPrimitive typ var
  pure { ast: j1 <> j2 <> j3, typ, var }
infer e@(C.TmOptPrj _ _ _ _) DstNil = do
  { ast: j1, var } <- dstNil
  { ast: j2, typ } <- infer e (DstVar var)
  j3 <- convertPrimitive typ var
  pure { ast: j1 <> j2 <> j3, typ, var }
infer (C.TmMerge e1 e2) (DstVar z) = do
  { ast: j1, typ: t1 } <- infer e1 (DstVar z)
  { ast: j2, typ: t2 } <- infer e2 (DstVar z)
  pure { ast: j1 <> j2, typ: C.TyAnd t1 t2, var: z }
infer (C.TmAnno e typ) dst = do
  { ast, var } <- check (skipAnno e) typ dst
  pure { ast, typ, var }
  where skipAnno :: C.Tm -> C.Tm
        skipAnno (C.TmAnno e' _) = e'
        skipAnno e' = e'
infer (C.TmFold t e) dst = do
  { ast, var } <- infer e dst
  pure { ast, typ: t, var }
infer (C.TmUnfold t e) dst = do
  { ast, var } <- infer e dst
  pure { ast, typ: C.unfold t, var }
infer (C.TmRef e) (DstVar z) = do
  { ast: j, typ: t, var: y } <- infer e DstNil
  let typ = C.TyRef t
      ast = j <> [ addProp (JSVar z) (toIndex typ) (JSVar y) ]
  pure { ast, typ, var: z }
infer (C.TmDeref e) dst = do
  { ast: j, typ: t, var: y } <- infer e DstNil
  case t of C.TyRef typ -> do
              var <- freshVarName
              let value = JSIndexer (toIndex t) (JSVar y)
                  j' = case dst of DstVar z -> [ copyObj z value typ ]
                                   DstOpt z -> [ JSVariableIntroduction var $ Just value
                                               , JSIfElse (JSVar z) (copyObj z value typ) Nothing ]
                                   DstNil -> [ JSVariableIntroduction var $ Just value ]
              pure { ast: j <> j', typ, var }
            _ -> throwError $ "cannot dereference" <+> show t
infer (C.TmAssign e1 e2) (DstVar z) = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  case t1 of C.TyRef t1' -> do
               { ast: j2, var: y } <- check e2 t1' DstNil
               let ast = j1 <> j2 <> [ JSAssignment (JSIndexer (toIndex t1) (JSVar x)) (JSVar y) ]
               pure { ast, typ: C.TyUnit, var: z }
             _ -> throwError $ "assignment expected a reference type, but got" <+> show t1
infer (C.TmToString e) dst = do
  { ast: j0, var: y } <- infer e DstNil
  var <- freshVarName
  let j1 = [ JSVariableIntroduction var $ Just $ JSApp (JSAccessor "toString" (JSVar y)) [] ]
      assign z = addProp (JSVar z) (toIndex C.TyString) (JSVar var)
      j2 = case dst of DstVar z -> [ assign z ]
                       DstOpt z -> [ JSIfElse (JSVar z) (assign z) Nothing ]
                       DstNil -> []
  pure { ast: j0 <> j1 <> j2, typ: C.TyString, var }
infer (C.TmDef x e1 e2) dst = do
  { ast: j1, typ: t1, var: y } <- infer e1 DstNil
  { ast: j2, typ: t2, var } <- addTmBind x t1 $ infer e2 dst
  let export = JSExport $ JSVariableIntroduction (variable x) $ Just $ JSVar y
  pure { ast: j1 <> [export] <> j2, typ: t2, var }
infer (C.TmMain e) DstNil = do
  { ast: j, typ, var } <- infer e DstNil
  let block = j <> [JSReturn $ JSVar var]
      ast = [ JSExport $ JSFunction (Just "main") [] $ JSBlock block ]
  pure { ast, typ, var }
infer e (DstOpt y) = do
  { ast: j1, var } <- dstOpt y
  { ast: j2, typ } <- infer e (DstVar var)
  pure { ast: j1 <> j2, typ, var }
infer e DstNil = do
  { ast: j1, var } <- dstNil
  { ast: j2, typ } <- infer e (DstVar var)
  pure { ast: j1 <> j2, typ, var }
infer e _ = unsafeCrashWith $ "FIXME: infer" <+> show e

check :: C.Tm -> C.Ty -> Destination -> CodeGen CheckResult
check e t dst = do
  x <- freshVarName
  { ast: j1, typ, var } <- infer e (DstOpt x)
  let j0 = [ JSVariableIntroduction x $ case dst of DstNil -> Nothing
                                                    DstOpt z -> Just $ JSVar z
                                                    DstVar z -> Just $ JSVar z ]
  if t .=. typ then pure { ast: j0 <> j1, var }
  else do
    y <- freshVarName
    let j2 = [ case dst of DstVar z -> JSVariableIntroduction y $ Just $ JSVar z
                           DstOpt z -> JSVariableIntroduction y $ Just $ JSBinary Or (JSVar z) (JSObjectLiteral [])
                           DstNil -> initialize y ]
    j3 <- subtype typ t var y true
    j4 <- convertPrimitive t y
    pure { ast: [ JSVariableIntroduction x Nothing ] <> j1 <> j2 <> j3 <> j4, var: y }

data Arg = TmArg Name C.Ty | TyArg C.Ty

distapp :: Name -> C.Ty -> Arg -> Destination -> CodeGen InferResult
distapp _ t _ (DstVar z) | isTopLike t = pure { ast: [], typ: C.TyTop, var: z }
distapp x t@(C.TyArrow targ tret _) (TmArg y t') dst | not (isTopLike tret) = do
  y' /\ j1 <- if targ .=. t' then pure $ y /\ []
              else do y' <- freshVarName
                      j <- subtype t' targ y y' true
                      pure $ y' /\ ([ initialize y' ] <> j)
  let app m1 m2 = let f1 = case m1 of Nothing -> identity
                                      Just z -> JSVariableIntroduction z <<< Just
                      f2 = case m2 of Nothing -> identity
                                      Just z -> (_ <> [JSVar z]) in
                  f1 (JSApp (JSIndexer (toIndex t) (JSVar x)) (f2 [JSVar y']))
  case dst of DstNil -> do z <- freshVarName
                           pure { ast: j1 <> [ app (Just z) Nothing ], typ: tret, var: z }
              DstOpt z' -> do z <- freshVarName
                              pure { ast: j1 <> [ app (Just z) (Just z') ], typ: tret, var: z }
              DstVar z -> pure { ast: j1 <> [ app Nothing (Just z) ], typ: tret, var: z }
distapp x t@(C.TyForall a _ tbody) (TyArg t') dst | not (isTopLike tbody) =
  let app m1 m2 = let f1 = case m1 of Nothing -> identity
                                      Just z -> JSVariableIntroduction z <<< Just
                      f2 = case m2 of Nothing -> identity
                                      Just z -> (_ <> [JSVar z]) in
                  f1 (JSApp (JSIndexer (toIndex t) (JSVar x)) (f2 [toIndices t']))
      typ = C.tySubst a t' tbody in
  case dst of DstNil -> do z <- freshVarName
                           pure { ast: [ app (Just z) Nothing ], typ, var: z }
              DstOpt z' -> do z <- freshVarName
                              pure { ast: [ app (Just z) (Just z') ], typ, var: z }
              DstVar z -> pure { ast: [ app Nothing (Just z) ], typ, var: z }
distapp x (C.TyAnd ta tb) arg (DstVar z) = do
  { ast: j1, typ: t1 } <- distapp x ta arg (DstVar z)
  { ast: j2, typ: t2 } <- distapp x tb arg (DstVar z)
  pure { ast: j1 <> j2, typ: C.TyAnd t1 t2, var: z }
distapp x t arg (DstOpt y) = do
  { ast: j1, var: z } <- dstOpt y
  { ast: j2, typ, var } <- distapp x t arg (DstVar z)
  pure { ast: j1 <> j2, typ, var }
distapp x t arg DstNil = do
  { ast: j1, var: z } <- dstNil
  { ast: j2, typ, var } <- distapp x t arg (DstVar z)
  pure { ast: j1 <> j2, typ, var }
distapp _ t _ _ = throwError $ "expected an applicable type, but got" <+> show t

proj :: C.Ty -> Name -> Label -> Destination -> Boolean -> CodeGen CheckResult
proj t0 x l dst opt = case dst of DstVar var -> pure { ast: go t0 var, var }
                                  _ -> freshVarName <#> \var -> { ast: go t0 var, var }
  where go :: C.Ty -> Name -> AST
        go t _ | isTopLike t = []
        go (C.TyAnd ta tb) z = go ta z <> go tb z
        go t@(C.TyRcd l' typ _) z | l == l' =
          let field = JSIndexer (toIndex t) (JSVar x)
              intro = JSVariableIntroduction z $ Just field
              copy y = (if opt then \j -> JSIfElse field j Nothing else identity)
                       (copyObj y field typ) in
          case dst of DstNil -> [ intro ]
                      DstOpt y -> [ intro, JSIfElse (JSVar y) (copy y) Nothing ]
                      DstVar y -> [ copy y ]
        go _ _ = []

subtype :: C.Ty -> C.Ty -> Name -> Name -> Boolean -> CodeGen AST
subtype _ t _ _ _ | isTopLike t = pure []
subtype C.TyTop (C.TyRcd _ _ true) _ _ _ = pure []
subtype C.TyBot t _ y _ = pure [ addProp (JSVar y) (toIndex t) JSNullLiteral ]
subtype ta tb x y true | ta .=. tb =
  case ta of C.TyAnd _ _ -> pure [ copyObj y (JSVar x) ta ]
             -- TODO: a record may contain a getter, but the fix below causes a significant slowdown
             -- C.TyRcd _ _ _ -> pure [ copyObj y (JSVar x) ta ]
             _ -> let f = if isPrimitive tb then identity else JSIndexer (toIndex ta) in
                  pure [ addProp (JSVar y) (toIndex tb) (f (JSVar x)) ]
subtype ta tb x z b | Just (tb1 /\ tb2) <- split tb =
  if isTopLike tb1 then subtype ta tb2 x z b
  else if isTopLike tb2 then subtype ta tb1 x z b
  else do { ast: j3, x: y1, y: y2 } <- unsplit { z, tx: tb1, ty: tb2, tz: tb }
          let j0 = (if y1 == z then [] else [initialize y1])
                <> (if y2 == z then [] else [initialize y2])
          j1 <- subtype ta tb1 x y1 b
          j2 <- subtype ta tb2 x y2 b
          pure $ j0 <> j1 <> j2 <> j3
subtype ta@(C.TyArrow ta1 ta2 _) tb@(C.TyArrow tb1 tb2 _) x y _ = do
  x1 <- freshVarName
  y1 <- freshVarName
  x2 <- freshVarName
  y2 <- freshVarName
  j1 <- subtype tb1 ta1 x1 y1 true
  j2 <- subtype ta2 tb2 x2 y2 true
  j1' <- convertPrimitive ta1 y1
  j2' <- convertPrimitive tb2 y2
  let block = [ initialize y1 ] <> j1 <> j1'
           <> [ JSVariableIntroduction x2 $ Just $ JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar y1] ]
           <> [ JSAssignment (JSVar y2) (JSBinary Or (JSVar y2) (JSObjectLiteral [])) ] <> j2 <> j2'
           <> [ JSReturn $ JSVar y2 ]
  pure [ addProp (JSVar y) (toIndex tb) (JSFunction Nothing [x1, y2] (JSBlock block)) ]
subtype ta@(C.TyForall a _ ta2) tb@(C.TyForall b _ tb2) x y _ = do
  x0 <- freshVarName
  y0 <- freshVarName
  let tb2' = C.tySubst b (C.TyVar a) tb2
  j <- subtype ta2 tb2' x0 y0 true
  j' <- convertPrimitive tb2' y0
  let block = [ JSVariableIntroduction x0 $ Just $ JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar (variable a)] ]
           <> [ JSAssignment (JSVar y0) (JSBinary Or (JSVar y0) (JSObjectLiteral [])) ] <> j <> j'
           <> [ JSReturn $ JSVar y0 ]
      func = JSFunction Nothing [variable a, y0] (JSBlock block) 
  pure [ addProp (JSVar y) (toIndex tb) func ]
subtype r1@(C.TyRcd l1 t1 _) r2@(C.TyRcd l2 t2 _) x y _ | l1 == l2 = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype t1 t2 x0 y0 true
  j' <- convertPrimitive t2 y0
  let block = [ JSVariableIntroduction x0 $ Just $ JSIndexer (toIndex r1) (JSVar x), initialize y0 ] <> j <> j'
  order <- asks (_.evalOrder)
  case order of
    CBV -> pure $ block <> [ addProp (JSVar y) (toIndex r2) (JSVar y0) ]
    CBN -> pure [ addGetter (JSVar y) r2 block y0 ]
subtype a1@(C.TyArray t1) a2@(C.TyArray t2) x y _ = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype t1 t2 x0 y0 true
  let arr = JSIndexer (toIndex a2) (JSVar y)
      block = [ initialize y0 ] <> j <> [ JSApp (JSAccessor "push" arr) [JSVar y0] ]
  pure [ JSAssignment arr (JSArrayLiteral [])
       , JSForOf x0 (JSIndexer (toIndex a1) (JSVar x)) $ JSBlock block
       ]
subtype (C.TyAnd ta tb) tc x y notSplit =
  (if notSplit then (_ <|> subtype C.TyTop tc x y false) else identity) -- match optional fields anyway
  (subtype ta tc x y false <|> subtype tb tc x y false)
subtype ta tb x y notSplit
  | ta == tb = let f = if notSplit && isPrimitive tb then identity else JSIndexer (toIndex ta) in
               pure [ addProp (JSVar y) (toIndex tb) (f (JSVar x)) ]
  | otherwise = throwError $ show ta <> " is not a subtype of " <> show tb <> ". "

unsplit :: { z :: Name, tx :: C.Ty, ty :: C.Ty, tz :: C.Ty } -> CodeGen { ast :: AST, x :: Name, y :: Name }
unsplit { z, tx: _, ty: _, tz: C.TyAnd _ _ } = pure { ast: [], x: z, y: z }
unsplit { z, tx: f1@(C.TyArrow _ t1 _), ty: f2@(C.TyArrow _ t2 _), tz: f@(C.TyArrow _ t _) } = do
  x1 <- freshVarName
  x2 <- freshVarName
  y <- freshVarName
  { ast: j, x: y1, y: y2 } <- unsplit { z: y, tx: t1, ty: t2, tz: t }
  let block = [ JSAssignment (JSVar y) (JSBinary Or (JSVar y) (JSObjectLiteral [])) ]
           <> (if y1 == y then [] else [initialize y1])
           <> (if y2 == y then [] else [initialize y2])
           <> [ JSApp (JSIndexer (toIndex f1) (JSVar x1)) [JSVar "p", JSVar y1]
              , JSApp (JSIndexer (toIndex f2) (JSVar x2)) [JSVar "p", JSVar y2] ]
           <> j <> [ JSReturn $ JSVar y]
      func = JSFunction Nothing ["p", y] (JSBlock block)
  pure { ast: [ addProp (JSVar z) (toIndex f) func ], x: x1, y: x2 }
unsplit { z, tx: f1@(C.TyForall _ _ t1), ty: f2@(C.TyForall _ _ t2), tz: f@(C.TyForall a _ t) } = do
  x1 <- freshVarName
  x2 <- freshVarName
  y <- freshVarName
  { ast: j, x: y1, y: y2 } <- unsplit { z: y, tx: t1, ty: t2, tz: t }
  let block = [ JSAssignment (JSVar y) (JSBinary Or (JSVar y) (JSObjectLiteral [])) ]
           <> (if y1 == y then [] else [initialize y1])
           <> (if y2 == y then [] else [initialize y2])
           <> [ JSApp (JSIndexer (toIndex f1) (JSVar x1)) [JSVar (variable a), JSVar y1]
              , JSApp (JSIndexer (toIndex f2) (JSVar x2)) [JSVar (variable a), JSVar y2] ]
           <> j <> [ JSReturn $ JSVar y]
      func = JSFunction Nothing [variable a, y] (JSBlock block)
  pure { ast: [ addProp (JSVar z) (toIndex f) func ], x: x1, y: x2 }
unsplit { z, tx: r1@(C.TyRcd _ t1 _), ty: r2@(C.TyRcd _ t2 _), tz: r@(C.TyRcd _ t _) } = do
  x1 <- freshVarName
  x2 <- freshVarName
  y <- freshVarName
  { ast: j, x: y1, y: y2 } <- unsplit { z: y, tx: t1, ty: t2, tz: t }
  order <- asks (_.evalOrder)
  let j' = [ initialize y ]
        <> (if y1 == y then [] else [initialize y1])
        <> (if y2 == y then [] else [initialize y2])
        <> [ copyObj y1 (JSIndexer (toIndex r1) (JSVar x1)) t1
           , copyObj y2 (JSIndexer (toIndex r2) (JSVar x2)) t2 ]
        <> j
      ast = case order of
        CBV -> j' <> [ addProp (JSVar z) (toIndex r) (JSVar y) ]
        CBN -> [ addGetter (JSVar z) r j' y ]
  pure { ast, x: x1, y: x2 }
unsplit s = unsafeCrashWith $ "cannot unsplit" <+> show s

toIndex :: C.Ty -> JS
toIndex = JSTemplateLiteral <<< fst <<< go Nil
  where
    go :: List Name -> C.Ty -> String /\ Boolean
    go _ t | isBaseType t    = toLower (show t) /\ false
    go as (C.TyArrow _ t _)  = lmap ("fun_" <> _) (go as t)
    go as (C.TyForall a _ t) = lmap ("forall_" <> _) (go (a:as) t)
    go as (C.TyRcd l t _)    = lmap (("rcd_" <> l <> ":") <> _) (go as t)
    go as (C.TyArray t)      = lmap ("array_" <> _) (go as t)
    go as (C.TyRef t)        = lmap ("ref_" <> _) (go as t)
    -- TODO: change variable names to De Bruijn indices
    go as (C.TyVar a) | a `elem` as = a /\ false
                      | otherwise = ("${toIndex(" <> variable a <> ")}") /\ true
    -- TODO: consider a safer way to handle recursive types
    go as (C.TyRec a t) = go (a:as) t
    go as t@(C.TyAnd _ _) = let ts /\ b = foldl (\(ts /\ b) t -> bimap (insertIfNotElem ts) (b || _) (go as t))
                                                ([] /\ false) (flatten t) in
      if b then ("${toIndex(" <> print1 (JSArrayLiteral (transformVar <$> ts)) <> ")}") /\ true
      else (if length ts == 1 then unsafeFromJust (ts !! 0) else "(" <> joinWith "&" ts <> ")") /\ false
    go _ t = unsafeCrashWith $ "cannot use as an index: " <> show t
    -- a dirty string manipulation:
    transformVar :: String -> JS
    transformVar s = case stripPrefix (Pattern "${toIndex(") s of
      Just s' -> JSUnary Spread $ JSVar $ unsafeFromJust $ stripSuffix (Pattern ")}") s'
      Nothing -> JSTemplateLiteral s
    isBaseType :: C.Ty -> Boolean
    isBaseType C.TyBool = true
    isBaseType C.TyInt = true
    isBaseType C.TyDouble = true
    isBaseType C.TyString = true
    isBaseType C.TyUnit = true
    isBaseType C.TyBot = true
    isBaseType _ = false
    -- this function does sorting and deduplication:
    insertIfNotElem :: Array String -> String -> Array String
    insertIfNotElem arr a = if notElem a arr then A.insert a arr else arr

toIndices :: C.Ty -> JS
toIndices (C.TyVar a) = JSVar $ variable a
toIndices t@(C.TyAnd _ _) = JSArrayLiteral $ map toIndex $ flatten t
toIndices t | isTopLike t = JSArrayLiteral []
            | otherwise   = JSArrayLiteral [toIndex t]

flatten :: C.Ty -> Array C.Ty
flatten (C.TyAnd t1 t2) = flatten t1 <> flatten t2
flatten t | isTopLike t = []
          | otherwise   = [t]

equiv :: C.Ty -> C.Ty -> Boolean
equiv t1 t2 | isTopLike t1 && isTopLike t2 = true
equiv t1@(C.TyAnd _ _) t2 = let ts1 = flatten t1
                                ts2 = flatten t2 in
                            all (\t -> isJust $ find (t .=. _) ts2) ts1 &&
                            all (\t -> isJust $ find (t .=. _) ts1) ts2
equiv t1 t2@(C.TyAnd _ _) = equiv t2 t1
equiv (C.TyArrow t1 t2 _) (C.TyArrow t3 t4 _) = t1 .=. t3 && t2 .=. t4
equiv (C.TyRcd l1 t1 opt1) (C.TyRcd l2 t2 opt2) = l1 == l2 && t1 .=. t2 && opt1 == opt2
equiv (C.TyForall a1 td1 t1) (C.TyForall a2 td2 t2) = td1 .=. td2 && t1 .=. C.tySubst a2 (C.TyVar a1) t2
equiv (C.TyRec a1 t1) (C.TyRec a2 t2) = t1 .=. C.tySubst a2 (C.TyVar a1) t2
equiv (C.TyArray t1) (C.TyArray t2) = t1 .=. t2
equiv (C.TyRef t1) (C.TyRef t2) = t1 .=. t2
equiv t1 t2 | t1 === t2 = true
            | otherwise = false

infix 4 equiv as .=.

freshVarName :: CodeGen Name
freshVarName = do
  count <- modify (_ + 1)
  pure $ variable $ show count

lookupTmBind :: Name -> CodeGen C.Ty
lookupTmBind x = do
  env <- asks (_.tmBindEnv)
  case lookup x env of
    Just typ -> pure typ
    Nothing  -> throwError $ "term variable" <+> show x <+> "is undefined"

addTmBind :: forall a. Name -> C.Ty -> CodeGen a -> CodeGen a
addTmBind x t = local (\ctx -> ctx { tmBindEnv = insert x t ctx.tmBindEnv })

addTyBind :: forall a. Name -> C.Ty -> CodeGen a -> CodeGen a
addTyBind a t = local (\ctx -> ctx { tyBindEnv = insert a t ctx.tyBindEnv })

setInTrait :: forall a. Boolean -> CodeGen a -> CodeGen a
setInTrait b = if b then local (\ctx -> ctx { inTrait = b }) else identity

variable :: Name -> Name
variable = ("$" <> _) <<< replaceAll (Pattern "'") (Replacement "$prime")

initialize :: Name -> JS
initialize x = JSVariableIntroduction x $ Just $ JSObjectLiteral []

thunk :: Array JS -> JS
thunk = JSFunction Nothing [] <<< JSBlock

-- TODO: replace `typeof o === 'object'` with `primitive(a)`; see `convertPrimitive` below
copyObj :: Name -> JS -> C.Ty -> JS
copyObj z arg typ =
  case typ of C.TyVar a -> let els = addPropForIndex (first (JSVar (variable a))) in
                           JSIfElse (isObject arg) (JSBlock [app]) (Just (JSBlock [els]))
              _ | isPrimitive typ -> addPropForIndex (toIndex typ)
                | otherwise -> app
  where app = JSApp (JSVar "copyObj") [JSVar z, arg]
        addPropForIndex t = addProp (JSVar z) t arg
        isObject o = JSBinary EqualTo (JSTypeOf o) (JSStringLiteral "object")
        first x = JSIndexer (JSNumericLiteral 0.0) x

addProp :: JS -> JS -> JS -> JS
addProp o x f = JSAssignment (JSIndexer x o) f

addGetter :: JS -> C.Ty -> Array JS -> Name -> JS
addGetter o t j y =  defineGetter o (toIndex t) block
  where block = j <> [ JSApp (JSVar "delete") [field], JSReturn (JSAssignment field (JSVar y)) ]
        field = JSIndexer (toIndex t) (JSVar "this")

addGettersForIndices :: Name -> C.Ty -> Array JS -> Array JS
addGettersForIndices z t j = [ initialize z, JSForOf index (toIndices t) $ defineGetter (JSVar z) (JSVar index) block ]
  where block = [ JSForOf index (toIndices t) $ JSApp (JSVar "delete") [field] ] <> j <> [ JSReturn field ]
        field = JSIndexer (JSVar index) (JSVar "this")
        index = "$$index"

defineGetter :: JS -> JS -> Array JS -> JS
defineGetter o n j = JSApp (JSAccessor "__defineGetter__" o) [n, JSFunction Nothing [] (JSBlock j)]

isPrimitive :: C.Ty -> Boolean
isPrimitive C.TyInt = true
isPrimitive C.TyDouble = true
isPrimitive C.TyString = true
isPrimitive C.TyBool = true
isPrimitive _ = false

convertPrimitive :: C.Ty -> Name -> CodeGen AST
convertPrimitive (C.TyVar a) z = do
  t <- freshVarName
  pure [ JSVariableIntroduction t $ Just $ JSApp (JSVar "primitive") [JSVar (variable a)]
       , JSIfElse (JSVar t) (JSBlock [ JSAssignment (JSVar z) (JSIndexer (JSVar t) (JSVar z)) ]) Nothing
       ]
convertPrimitive t z
  | isPrimitive t = pure [ JSAssignment (JSVar z) (JSIndexer (toIndex t) (JSVar z)) ]
  | otherwise = pure []
