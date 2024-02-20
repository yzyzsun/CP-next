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
infer C.TmUnit (DstVar z) = pure { ast: [], typ: C.TyTop, var: z }
infer C.TmUndefined (DstVar z) = pure { ast: [], typ: C.TyBot, var: z }
infer (C.TmInt i) (DstVar z) = pure
  { ast: [ addProp (JSVar z) (toIndex C.TyInt) (JSNumericLiteral (toNumber i)) ]
  , typ: C.TyInt
  , var: z
  }
infer (C.TmDouble d) (DstVar z) = pure
  { ast: [ addProp (JSVar z) (toIndex C.TyDouble) (JSNumericLiteral d) ]
  , typ: C.TyDouble
  , var: z
  }
infer (C.TmString s) (DstVar z) = pure
  { ast: [ addProp (JSVar z) (toIndex C.TyString) (JSStringLiteral s) ]
  , typ: C.TyString
  , var: z
  }
infer (C.TmBool b) (DstVar z) = pure
  { ast: [ addProp (JSVar z) (toIndex C.TyBool) (JSBooleanLiteral b) ]
  , typ: C.TyBool
  , var: z
  }
infer (C.TmArray t arr) (DstVar z) = do
  arr' <- traverse (flip infer DstNil) arr
  let js = arr' <#> (_.ast)
      vs = arr' <#> (_.var) >>> JSVar
      ast = concat js <> [ addProp (JSVar z) (toIndex (C.TyArray t)) (JSArrayLiteral vs) ]
  pure { ast, typ: C.TyArray t, var: z }
infer (C.TmUnary Op.Neg e) (DstVar z) = do
  { ast: j, typ: t, var: y } <- infer e DstNil
  let ast typ = j <> [ addProp (JSVar z) (toIndex typ)
                               (JSUnary Negate (JSIndexer (toIndex typ) (JSVar y))) ]
  case t of C.TyInt    -> pure { ast: ast C.TyInt,    typ: C.TyInt,    var: z }
            C.TyDouble -> pure { ast: ast C.TyDouble, typ: C.TyDouble, var: z }
            _ -> throwError $ "Neg is not defined for" <+> show t
infer (C.TmUnary Op.Not e) (DstVar z) = do
  { ast: j, typ: t, var: y } <- infer e DstNil
  let ast = j <> [ addProp (JSVar z) (toIndex C.TyBool)
                           (JSUnary Not (JSIndexer (toIndex C.TyBool) (JSVar y))) ]
  case t of C.TyBool -> pure { ast, typ: C.TyBool, var: z }
            _ -> throwError $ "Not is not defined for" <+> show t
infer (C.TmUnary Op.Len e) (DstVar z) = do
  { ast: j, typ: t, var: y } <- infer e DstNil
  let ast = j <> [ addProp (JSVar z) (toIndex C.TyInt)
                           (JSAccessor "length" (JSIndexer (toIndex t) (JSVar y))) ]
  pure { ast, typ: C.TyInt, var: z }
infer (C.TmUnary Op.Sqrt e) (DstVar z) = do
  { ast: j, typ: t, var: y } <- infer e DstNil
  let ast = j <> [ addProp (JSVar z) (toIndex C.TyDouble)
                           (JSApp (JSAccessor "sqrt" (JSVar "Math"))
                                  [JSIndexer (toIndex C.TyDouble) (JSVar y)]) ]
  case t of C.TyDouble -> pure { ast, typ: C.TyDouble, var: z }
            _ -> throwError $ "Sqrt is not defined for" <+> show t
infer (C.TmBinary (Op.Arith op) e1 e2) (DstVar z) = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  { ast: j2, typ: t2, var: y } <- infer e2 DstNil
  let ast typ flg = j1 <> j2 <> [ addProp (JSVar z) (toIndex typ)
        (fun (JSBinary (map op) (JSIndexer (toIndex typ) (JSVar x))
                                (JSIndexer (toIndex typ) (JSVar y)))) ]
        where fun = if flg then trunc else identity
  case t1, t2 of C.TyInt,    C.TyInt    -> pure { ast: ast C.TyInt (op == Op.Div), typ: C.TyInt,    var: z }
                 C.TyDouble, C.TyDouble -> pure { ast: ast C.TyDouble false,       typ: C.TyDouble, var: z }
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
infer (C.TmBinary (Op.Comp op) e1 e2) (DstVar z) = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  { ast: j2, typ: t2, var: y } <- infer e2 DstNil
  let ast typ = j1 <> j2 <> [ addProp (JSVar z) (toIndex C.TyBool)
    (JSBinary (map op) (JSIndexer (toIndex typ) (JSVar x))
                       (JSIndexer (toIndex typ) (JSVar y))) ]
  case t1, t2 of C.TyInt,    C.TyInt    -> pure { ast: ast C.TyInt,    typ: C.TyBool, var: z }
                 C.TyDouble, C.TyDouble -> pure { ast: ast C.TyDouble, typ: C.TyBool, var: z }
                 C.TyString, C.TyString -> pure { ast: ast C.TyString, typ: C.TyBool, var: z }
                 C.TyBool,   C.TyBool   -> pure { ast: ast C.TyBool,   typ: C.TyBool, var: z }
                 _, _ -> throwError $
                   "CompOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where map :: Op.CompOp -> BinaryOperator
        map Op.Eql = EqualTo
        map Op.Neq = NotEqualTo
        map Op.Lt  = LessThan
        map Op.Le  = LessThanOrEqualTo
        map Op.Gt  = GreaterThan
        map Op.Ge  = GreaterThanOrEqualTo
infer (C.TmBinary (Op.Logic op) e1 e2) (DstVar z) = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  { ast: j2, typ: t2, var: y } <- infer e2 DstNil
  let ast = j1 <> j2 <> [ addProp (JSVar z) (toIndex C.TyBool)
    (JSBinary (map op) (JSIndexer (toIndex C.TyBool) (JSVar x))
                       (JSIndexer (toIndex C.TyBool) (JSVar y))) ]
  case t1, t2 of C.TyBool, C.TyBool -> pure { ast, typ: C.TyBool, var: z }
                 _, _ -> throwError $
                   "LogicOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where map :: Op.LogicOp -> BinaryOperator
        map Op.And = And
        map Op.Or  = Or
infer (C.TmBinary Op.Append e1 e2) (DstVar z) = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  { ast: j2, typ: t2, var: y } <- infer e2 DstNil
  case t1, t2 of
    C.TyString, C.TyString ->
      let ast = j1 <> j2 <> [ addProp (JSVar z) (toIndex C.TyString)
            (JSBinary Add (JSIndexer (toIndex C.TyString) (JSVar x))
                          (JSIndexer (toIndex C.TyString) (JSVar y))) ] in
      pure { ast, typ: C.TyString, var: z }
    typ@(C.TyArray t), C.TyArray t' | t .=. t' ->
      let ast = j1 <> j2 <> [ addProp (JSVar z) (toIndex typ)
            (JSApp (JSAccessor "concat" (JSIndexer (toIndex typ) (JSVar x)))
                                        [JSIndexer (toIndex typ) (JSVar y)]) ] in
      pure { ast, typ, var: z }
    _, _ -> throwError $
      "Append is not defined between" <+> show t1 <+> "and" <+> show t2
infer (C.TmBinary Op.Index e1 e2) dst = do
  { ast: j1, typ: t1, var: x } <- infer e1 DstNil
  { ast: j2, typ: t2, var: y } <- infer e2 DstNil
  case t1, t2 of
    t@(C.TyArray typ), C.TyInt -> do
      let element = JSIndexer (JSIndexer (toIndex C.TyInt) (JSVar y))
                              (JSIndexer (toIndex t) (JSVar x))
      j3 /\ z <- case dst of DstVar z -> pure $ [ copyObj z element ] /\ z
                             DstOpt z' -> do z <- freshVarName
                                             pure $ [ JSVariableIntroduction z $ Just element
                                                    , JSIfElse (JSVar z') (copyObj z' element) Nothing ] /\ z
                             DstNil -> do z <- freshVarName
                                          pure $ [ JSVariableIntroduction z $ Just element ] /\ z
      pure { ast: j1 <> j2 <> j3, typ, var: z }
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
                      JSIfElse (JSIndexer (toIndex C.TyBool) (JSVar var))
                               (JSBlock (f2 j2)) (Just (JSBlock (f3 j3)))
      case dst of DstVar z -> pure { ast: j1 <> [ ifElse Nothing ], typ: t2, var: z }
                  _ -> do z <- freshVarName
                          pure { ast: j1 <> [ JSVariableIntroduction z Nothing, ifElse (Just z) ], typ: t2, var: z }
    else throwError $ "if-branches expected two equivalent types, but got"
                   <+> show t2 <+> "and" <+> show t3
  else throwError $ "if-condition expected Bool, but got" <+> show t1
infer (C.TmVar x) (DstVar z) = do
  typ <- lookupTmBind x
  pure { ast: [ copyObj z (JSVar (variable x)) ], typ, var: z }
infer (C.TmFix x e typ) (DstVar z) = do
  { ast: j } <- addTmBind x typ $ check e typ (DstVar z)
  let ast = [ JSVariableIntroduction (variable x) $ Just (JSVar z) ] <> j
  pure { ast, typ, var: z }
infer (C.TmAbs x e targ tret _ isTrait) (DstVar z)
  | isTopLike tret = infer C.TmUnit (DstVar z)
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
  { ast: j3, typ: t3, var: z } <- distapp t1 x (TmArg y t2) dst
  pure { ast: j1 <> j2 <> j3, typ: t3, var: z }
infer (C.TmTAbs a td e t _) (DstVar z)
  | isTopLike t = infer C.TmUnit (DstVar z)
  | otherwise = do
      y <- freshVarName
      { ast: j, var: y0 } <- addTyBind a td $ check e t (DstOpt y)
      let typ = C.TyForall a td t
          fun = JSFunction Nothing [variable a, y] $ JSBlock $ j <> [JSReturn $ JSVar y0]
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure { ast, typ, var: z }
infer (C.TmTApp e t) dst = do
  { ast: j1, typ: tf, var: y } <- infer e DstNil
  { ast: j2, typ: tbody, var: z } <- distapp tf y (TyArg t) dst
  pure { ast: j1 <> j2, typ: tbody, var: z }
infer (C.TmRcd l t e) (DstVar z)
  | isTopLike t = infer C.TmUnit (DstVar z)
  | otherwise = do
      { ast: j, var: y } <- check e t DstNil
      order <- asks (_.evalOrder)
      inTrait <- asks (_.inTrait)
      let ast = if order == CBV || not inTrait
                then j <> [ addProp (JSVar z) (toIndex typ) (JSVar y) ]
                else [ addGetter (JSVar z) (toIndex typ) j y ]
          typ = C.TyRcd l t false
      pure { ast, typ, var: z }
infer (C.TmPrj e l) dst = do
  { ast: j1, typ: t1, var: y } <- infer e DstNil
  case selectLabel t1 l false of
    Just typ@(C.TyAnd _ _) -> do
      case dst of DstVar z -> do { ast: j2 } <- proj t1 y l (DstVar z)
                                 pure { ast: j1 <> j2, typ, var: z }
                  DstOpt z' -> do { ast: j2, var: z } <- dstOpt z'
                                  { ast: j3 } <- proj t1 y l (DstVar z)
                                  pure { ast: j1 <> j2 <> j3, typ, var: z }
                  DstNil -> do { ast: j2, var: z } <- dstNil
                               { ast: j3 } <- proj t1 y l (DstVar z)
                               pure { ast: j1 <> j2 <> j3, typ, var: z }
    Just typ -> do
      { ast: j2, var } <- proj t1 y l dst
      pure { ast: j1 <> j2, typ, var }
    _ -> throwError $ "label" <+> show l <+> "is absent in" <+> show t1
infer (C.TmMerge e1 e2) (DstVar z) = do
  { ast: j1, typ: t1 } <- infer e1 (DstVar z)
  { ast: j2, typ: t2 } <- infer e2 (DstVar z)
  pure { ast: j1 <> j2, typ: C.TyAnd t1 t2, var: z }
infer (C.TmAnno e typ) (DstVar z) = do
  { ast } <- check (skipAnno e) typ (DstVar z)
  pure { ast, typ, var: z }
  where skipAnno :: C.Tm -> C.Tm
        skipAnno (C.TmAnno e' _) = e'
        skipAnno e' = e'
infer (C.TmToString e) (DstVar z) = do
  { ast: j, typ: t, var: y } <- infer e DstNil
  let ast = j <> [ addProp (JSVar z) (toIndex C.TyString)
    (JSApp (JSAccessor "toString" (JSIndexer (toIndex t) (JSVar y))) []) ]
  pure { ast, typ: C.TyString, var: z }
infer (C.TmDef x e1 e2 lazy) dst =
  if lazy then do  -- is originally `open` expressions
    { ast: j1, typ: t1 } <- infer e1 (DstVar "this")
    { ast: j2, typ: t2, var } <- addTmBind x t1 $ infer e2 dst
    let ast = [initialize varX] <> addGettersForIndices varX t1 j1 <> j2
    pure { ast, typ: t2, var }
  else do  -- is originally top-level definitions
    { ast: j1, typ: t1 } <- infer e1 (DstVar varX)
    { ast: j2, typ: t2, var } <- addTmBind x t1 $ infer e2 dst
    pure { ast: [JSExport $ initialize varX] <> j1 <> j2, typ: t2, var }
  where varX = variable x
infer (C.TmMain e) DstNil = do
  { ast: j, typ, var } <- infer e DstNil
  let block = j <> [JSReturn $ JSVar var]
      ast = [ JSExport $ JSFunction (Just "main") [] $ JSBlock block ]
  pure { ast, typ, var }
infer (C.TmVar x) (DstOpt y) = do
  z <- freshVarName
  typ <- lookupTmBind x
  let ast = [ JSVariableIntroduction z $ Just $ JSVar $ variable x
            , JSIfElse (JSVar y) (copyObj y (JSVar z)) Nothing
            ]
  pure { ast, typ, var: variable x }
infer (C.TmVar x) DstNil = do
  typ <- lookupTmBind x
  pure { ast: [], typ, var: variable x }
infer (C.TmAnno e typ) DstNil = do
  { ast, var } <- check e typ DstNil
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
    pure { ast: j0 <> j1 <> j2 <> j3, var: y }

data Arg = TmArg Name C.Ty | TyArg C.Ty

distapp :: C.Ty -> Name -> Arg -> Destination -> CodeGen InferResult
distapp t _ _ (DstVar z) | isTopLike t = pure { ast: [], typ: C.TyTop, var: z }
distapp t@(C.TyArrow targ tret _) x (TmArg y t') dst = do
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
distapp t@(C.TyForall a _ tbody) x (TyArg t') dst =
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
distapp (C.TyAnd ta tb) x arg (DstVar z) = do
  { ast: j1, typ: t1 } <- distapp ta x arg (DstVar z)
  { ast: j2, typ: t2 } <- distapp tb x arg (DstVar z)
  pure { ast: j1 <> j2, typ: C.TyAnd t1 t2, var: z }
distapp t x arg (DstOpt y) = do
  { ast: j1, var: z } <- dstOpt y
  { ast: j2, typ, var } <- distapp t x arg (DstVar z)
  pure { ast: j1 <> j2, typ, var }
distapp t x arg DstNil = do
  { ast: j1, var: z } <- dstNil
  { ast: j2, typ, var } <- distapp t x arg (DstVar z)
  pure { ast: j1 <> j2, typ, var }
distapp t _ _ _ = throwError $ "expected an applicable type, but got" <+> show t

proj :: C.Ty -> Name -> Label -> Destination -> CodeGen CheckResult
proj t0 x l dst = case dst of DstVar var -> pure { ast: go t0 var, var }
                              _ -> freshVarName <#> \var -> { ast: go t0 var, var }
  where go :: C.Ty -> Name -> AST
        go t _ | isTopLike t = []
        go (C.TyAnd ta tb) z = go ta z <> go tb z
        go t@(C.TyRcd l' _ _) z | l == l' =
          let field = JSIndexer (toIndex t) (JSVar x)
              intro = JSVariableIntroduction z $ Just field in
          case dst of DstNil -> [ intro ]
                      DstOpt y -> [ intro, JSIfElse (JSVar y) (copyObj y field) Nothing ]
                      DstVar y -> [ copyObj y field ]
        go _ _ = []

subtype :: C.Ty -> C.Ty -> Name -> Name -> Boolean -> CodeGen AST
subtype _ t _ _ _ | isTopLike t = pure []
subtype C.TyBot t _ y _ = pure [ JSAssignment (JSIndexer (toIndex t) (JSVar y)) JSNullLiteral ]
subtype ta tb x y true | ta .=. tb =
  case ta of C.TyAnd _ _ -> pure [ copyObj y (JSVar x) ]
             _ -> pure [ JSAssignment (JSIndexer (toIndex tb) (JSVar y))
                                      (JSIndexer (toIndex ta) (JSVar x)) ]
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
  let block = [ initialize y1 ] <> j1
           <> [ JSVariableIntroduction x2 $ Just $ JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar y1] ]
           <> [ JSAssignment (JSVar y2) (JSBinary Or (JSVar y2) (JSObjectLiteral [])) ] <> j2 <> [ JSReturn $ JSVar y2 ]
  pure [ addProp (JSVar y) (toIndex tb) (JSFunction Nothing [x1, y2] (JSBlock block)) ]
subtype ta@(C.TyForall a _ ta2) tb@(C.TyForall b _ tb2) x y _ = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype ta2 (C.tySubst b (C.TyVar a) tb2) x0 y0 true
  let block = [ JSVariableIntroduction x0 $ Just $ JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar (variable a)] ]
           <> [ JSAssignment (JSVar y0) (JSBinary Or (JSVar y0) (JSObjectLiteral [])) ] <> j <> [ JSReturn $ JSVar y0 ]
      func = JSFunction Nothing [variable a, y0] (JSBlock block) 
  pure [ addProp (JSVar y) (toIndex tb) func ]
subtype r1@(C.TyRcd l1 t1 _) r2@(C.TyRcd l2 t2 _) x y _ | l1 == l2 = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype t1 t2 x0 y0 true
  let j' = [ JSVariableIntroduction x0 $ Just $ JSIndexer (toIndex r1) (JSVar x), initialize y0 ] <> j
  order <- asks (_.evalOrder)
  case order of
    CBV -> pure $ j' <> [ addProp (JSVar y) (toIndex r2) (JSVar y0) ]
    CBN -> pure [ addGetter (JSVar y) (toIndex r2) j' y0 ]
subtype a1@(C.TyArray t1) a2@(C.TyArray t2) x y _ = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype t1 t2 x0 y0 true
  let arr = JSIndexer (toIndex a2) (JSVar y)
      block = [ initialize y0 ] <> j <> [ JSApp (JSAccessor "push" arr) [JSVar y0] ]
  pure [ JSAssignment arr (JSArrayLiteral [])
       , JSForOf x0 (JSIndexer (toIndex a1) (JSVar x)) $ JSBlock block
       ]
subtype (C.TyAnd ta tb) tc x y _ = subtype ta tc x y false <|> subtype tb tc x y false
subtype ta tb x y _
  | ta == tb = pure [ JSAssignment (JSIndexer (toIndex tb) (JSVar y))
                                   (JSIndexer (toIndex ta) (JSVar x)) ]
  | otherwise = throwError $ show ta <> " is not a subtype of " <> show tb

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
        <> [ copyObj y1 (JSIndexer (toIndex r1) (JSVar x1))
           , copyObj y2 (JSIndexer (toIndex r2) (JSVar x2))]
        <> j
      ast = case order of
        CBV -> j' <> [ addProp (JSVar z) (toIndex r) (JSVar y) ]
        CBN -> [ addGetter (JSVar z) (toIndex r) j' y ]
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
    -- TODO: change variable names to De Bruijn indices
    go as (C.TyVar a) | a `elem` as = a /\ false
                      | otherwise = ("${toIndex(" <> variable a <> ")}") /\ true
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

copyObj :: Name -> JS -> JS
copyObj z arg = JSApp (JSVar "copyObj") [JSVar z, arg]

addProp :: JS -> JS -> JS -> JS
addProp o x f = JSAssignment (JSIndexer x o) f

addGetter :: JS -> JS -> Array JS -> Name -> JS
addGetter o t j y =  defineGetter o t block
  where block = j <> [ JSApp (JSVar "delete") [field], JSReturn (JSAssignment field (JSVar y)) ]
        field = JSIndexer t (JSVar "this")

addGettersForIndices :: Name -> C.Ty -> Array JS -> Array JS
addGettersForIndices z t j = [ initialize z, JSForOf index (toIndices t) $ defineGetter (JSVar z) (JSVar index) block ]
  where block = [ JSForOf index (toIndices t) $ JSApp (JSVar "delete") [field] ] <> j <> [ JSReturn field ]
        field = JSIndexer (JSVar index) (JSVar "this")
        index = "$$index"

defineGetter :: JS -> JS -> Array JS -> JS
defineGetter o t j = JSApp (JSAccessor "__defineGetter__" o) [t, JSFunction Nothing [] (JSBlock j)]

