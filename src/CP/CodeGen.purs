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
import Language.JS.AST (BinaryOperator(..), JS(..), ObjectProperty(..), UnaryOperator(..))
import Language.JS.Pretty (print1)
import Partial.Unsafe (unsafeCrashWith)

type CodeGen = RWST Ctx Unit Int (Except String)

type Ctx = { tmBindEnv :: Map Name C.Ty
           , tyBindEnv :: Map Name C.Ty
           , evalOrder :: EvalOrder
           }

data EvalOrder = CBV -- call by value
               | CBN -- call by need

emptyCtx :: Ctx
emptyCtx = { tmBindEnv: empty
           , tyBindEnv: empty
           , evalOrder: CBN
           }

fromState :: REPLState -> Ctx
fromState st = emptyCtx { tmBindEnv = fromFoldable $ rmap fst <$> st.tmBindings }

runCodeGen :: C.Tm -> Ctx -> Either String (Array JS)
runCodeGen e ctx = do
  { ast } /\ _ <- runExcept $ evalRWST (infer e "$0") ctx 0
  pure $ [ JSRawCode prelude ] <> ast

prelude :: String
prelude = """function toIndex(tt) {
    var ts = tt.sort().filter((t, i) => t === 0 || t !== tt[i-1]);
    if (ts.length === 1) return ts[0];
    else return '(' + ts.join('&') + ')';
}"""

type AST = Array JS

infer :: C.Tm -> Name -> CodeGen { ast :: AST, typ :: C.Ty }
infer C.TmUnit _ = pure { ast: [], typ: C.TyTop }
infer C.TmUndefined _ = pure { ast: [], typ: C.TyBot }
infer (C.TmInt i) z = pure
  { ast: [ addProp (JSVar z) (toIndex C.TyInt) (JSNumericLiteral (toNumber i)) ]
  , typ: C.TyInt
  }
infer (C.TmDouble d) z = pure
  { ast: [ addProp (JSVar z) (toIndex C.TyDouble) (JSNumericLiteral d) ]
  , typ: C.TyDouble
  }
infer (C.TmString s) z = pure
  { ast: [ addProp (JSVar z) (toIndex C.TyString) (JSStringLiteral s) ]
  , typ: C.TyString
  }
infer (C.TmBool b) z = pure
  { ast: [ addProp (JSVar z) (toIndex C.TyBool) (JSBooleanLiteral b) ]
  , typ: C.TyBool
  }
infer (C.TmArray t arr) z = do
  arr' <- traverse infer' arr
  let js = arr' <#> (_.ast)
      vs = arr' <#> (_.var) >>> JSVar
      ast = concat js <> [ addProp (JSVar z) (toIndex (C.TyArray t)) (JSArrayLiteral vs) ]
  pure { ast, typ: C.TyArray t }
infer (C.TmUnary Op.Neg e) z = do
  { ast: j, typ: t, var: y } <- infer' e
  let ast typ = j <> [ addProp (JSVar z) (toIndex typ)
                               (JSUnary Negate (JSIndexer (toIndex typ) (JSVar y))) ]
  case t of C.TyInt    -> pure { ast: ast C.TyInt,    typ: C.TyInt    }
            C.TyDouble -> pure { ast: ast C.TyDouble, typ: C.TyDouble }
            _ -> throwError $ "Neg is not defined for" <+> show t
infer (C.TmUnary Op.Not e) z = do
  { ast: j, typ: t, var: y } <- infer' e
  let ast = j <> [ addProp (JSVar z) (toIndex C.TyBool)
                           (JSUnary Not (JSIndexer (toIndex C.TyBool) (JSVar y))) ]
  case t of C.TyBool -> pure { ast, typ: C.TyBool }
            _ -> throwError $ "Not is not defined for" <+> show t
infer (C.TmUnary Op.Len e) z = do
  { ast: j, typ: t, var: y } <- infer' e
  let ast = j <> [ addProp (JSVar z) (toIndex C.TyInt)
                           (JSAccessor "length" (JSIndexer (toIndex t) (JSVar y))) ]
  pure { ast, typ: C.TyInt }
infer (C.TmUnary Op.Sqrt e) z = do
  { ast: j, typ: t, var: y } <- infer' e
  let ast = j <> [ addProp (JSVar z) (toIndex C.TyDouble)
                           (JSApp (JSAccessor "sqrt" (JSVar "Math"))
                                  [JSIndexer (toIndex C.TyDouble) (JSVar y)]) ]
  case t of C.TyDouble -> pure { ast, typ: C.TyDouble }
            _ -> throwError $ "Sqrt is not defined for" <+> show t
infer (C.TmBinary (Op.Arith op) e1 e2) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  { ast: j2, typ: t2, var: y } <- infer' e2
  let ast typ flg = j1 <> j2 <> [ addProp (JSVar z) (toIndex typ)
        (fun (JSBinary (map op) (JSIndexer (toIndex typ) (JSVar x))
                                (JSIndexer (toIndex typ) (JSVar y)))) ]
        where fun = if flg then trunc else identity
  case t1, t2 of C.TyInt,    C.TyInt    -> pure { ast: ast C.TyInt (op == Op.Div), typ: C.TyInt    }
                 C.TyDouble, C.TyDouble -> pure { ast: ast C.TyDouble false,       typ: C.TyDouble }
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
infer (C.TmBinary (Op.Comp op) e1 e2) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  { ast: j2, typ: t2, var: y } <- infer' e2
  let ast typ = j1 <> j2 <> [ addProp (JSVar z) (toIndex C.TyBool)
    (JSBinary (map op) (JSIndexer (toIndex typ) (JSVar x))
                       (JSIndexer (toIndex typ) (JSVar y))) ]
  case t1, t2 of C.TyInt,    C.TyInt    -> pure { ast: ast C.TyInt,    typ: C.TyBool }
                 C.TyDouble, C.TyDouble -> pure { ast: ast C.TyDouble, typ: C.TyBool }
                 C.TyString, C.TyString -> pure { ast: ast C.TyString, typ: C.TyBool }
                 C.TyBool,   C.TyBool   -> pure { ast: ast C.TyBool,   typ: C.TyBool }
                 _, _ -> throwError $
                   "CompOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where map :: Op.CompOp -> BinaryOperator
        map Op.Eql = EqualTo
        map Op.Neq = NotEqualTo
        map Op.Lt  = LessThan
        map Op.Le  = LessThanOrEqualTo
        map Op.Gt  = GreaterThan
        map Op.Ge  = GreaterThanOrEqualTo
infer (C.TmBinary (Op.Logic op) e1 e2) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  { ast: j2, typ: t2, var: y } <- infer' e2
  let ast = j1 <> j2 <> [ addProp (JSVar z) (toIndex C.TyBool)
    (JSBinary (map op) (JSIndexer (toIndex C.TyBool) (JSVar x))
                       (JSIndexer (toIndex C.TyBool) (JSVar y))) ]
  case t1, t2 of C.TyBool, C.TyBool -> pure { ast, typ: C.TyBool }
                 _, _ -> throwError $
                   "LogicOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where map :: Op.LogicOp -> BinaryOperator
        map Op.And = And
        map Op.Or  = Or
infer (C.TmBinary Op.Append e1 e2) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  { ast: j2, typ: t2, var: y } <- infer' e2
  case t1, t2 of
    C.TyString, C.TyString ->
      let ast = j1 <> j2 <> [ addProp (JSVar z) (toIndex C.TyString)
            (JSBinary Add (JSIndexer (toIndex C.TyString) (JSVar x))
                          (JSIndexer (toIndex C.TyString) (JSVar y))) ] in
      pure { ast, typ: C.TyString }
    typ@(C.TyArray t), C.TyArray t' | t .=. t' ->
      let ast = j1 <> j2 <> [ addProp (JSVar z) (toIndex typ)
            (JSApp (JSAccessor "concat" (JSIndexer (toIndex typ) (JSVar x)))
                                        [JSIndexer (toIndex typ) (JSVar y)]) ] in
      pure { ast, typ }
    _, _ -> throwError $
      "Append is not defined between" <+> show t1 <+> "and" <+> show t2
infer (C.TmBinary Op.Index e1 e2) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  { ast: j2, typ: t2, var: y } <- infer' e2
  case t1, t2 of
    t@(C.TyArray typ), C.TyInt ->
      let ast = j1 <> j2 <> [ assignObj z
            [JSIndexer (JSIndexer (toIndex C.TyInt) (JSVar y))
                       (JSIndexer (toIndex t) (JSVar x))] ] in
      pure { ast, typ }
    _, _ -> throwError $
      "Index is not defined between" <+> show t1 <+> "and" <+> show t2
infer (C.TmIf e1 e2 e3) z = do
  { ast: j1, typ: t1, var } <- infer' e1
  if t1 == C.TyBool then do
    { ast: j2, typ: t2 } <- infer e2 z
    { ast: j3, typ: t3 } <- infer e3 z
    if t2 .=. t3 then do
      let ast = j1 <> [ JSIfElse (JSIndexer (toIndex C.TyBool) (JSVar var))
                                 (JSBlock j2) (Just (JSBlock j3)) ]
      pure { ast, typ: t2 }
    else throwError $ "if-branches expected two equivalent types, but got"
                   <+> show t2 <+> "and" <+> show t3
  else throwError $ "if-condition expected Bool, but got" <+> show t1
infer (C.TmVar x) z = do
  order <- asks (_.evalOrder)
  let access = case order of CBV -> identity
                             CBN -> JSAccessor "get"
  typ <- lookupTmBind x
  pure { ast: [ assignObj z [access (JSVar (variable x))] ], typ }
infer (C.TmFix x e typ) z = do
  j <- addTmBind x typ $ check e typ z
  order <- asks (_.evalOrder)
  let rvalue = case order of
        CBV -> JSVar z
        CBN -> JSObjectLiteral [LiteralName "get" (JSVar z)]
      ast = [ JSVariableIntroduction (variable x) $ Just rvalue ] <> j
  pure { ast, typ }
infer (C.TmAbs x e targ tret _) z
  | isTopLike tret = infer C.TmUnit z
  | otherwise = do
      y <- freshVarName
      j <- addTmBind x targ $ check e tret y
      let typ = C.TyArrow targ tret false
          fun = JSFunction Nothing [variable x, y] $ JSBlock j
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure { ast, typ }
infer (C.TmApp e1 e2 _) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  { ast: j2, typ: t2, var: y } <- infer' e2
  order <- asks (_.evalOrder)
  case order of
    CBV -> do { ast: j3, typ: t3 } <- distapp t1 x (TmArg y t2) z
              pure { ast: j1 <> j2 <> j3, typ: t3 }
    CBN -> do y' <- freshVarName
              { ast: j3, typ: t3 } <- distapp t1 x (TmArg y' t2) z
              let j2' = [ JSVariableIntroduction y' $ Just $ lazyObj y j2 ]
              pure { ast: j1 <> j2' <> j3, typ: t3 }
infer (C.TmTAbs a td e t _) z
  | isTopLike t = infer C.TmUnit z
  | otherwise = do
      y <- freshVarName
      j <- addTyBind a td $ check e t y
      let typ = C.TyForall a td t
          fun = JSFunction Nothing [variable a, y] $ JSBlock j
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure { ast, typ }
infer (C.TmTApp e t) z = do
  { ast: j1, typ: tf, var: y } <- infer' e
  { ast: j2, typ: tbody } <- distapp tf y (TyArg t) z
  pure { ast: j1 <> j2, typ: tbody }
infer (C.TmRcd l t e) z
  | isTopLike t = infer C.TmUnit z
  | otherwise = do
      { ast: j, var: y } <- check' e t
      order <- asks (_.evalOrder)
      let ast = case order of
            CBV -> j <> [ addProp (JSVar z) (toIndex typ) (JSVar y) ]
            CBN -> [ addProp (JSVar z) (toIndex typ) (lazyObj y j) ]
          typ = C.TyRcd l t false
      pure { ast, typ }
infer (C.TmPrj e l) z = do
  { ast: j1, typ: t1, var: y } <- infer' e
  case selectLabel t1 l false of
    Just typ -> do
      order <- asks (_.evalOrder)
      let j2 = proj t1 y l z order
      pure $ { ast: j1 <> j2, typ }
    _ -> throwError $ "label" <+> show l <+> "is absent in" <+> show t1
infer (C.TmMerge e1 e2) z = do
  { ast: j1, typ: t1 } <- infer e1 z
  { ast: j2, typ: t2 } <- infer e2 z
  pure { ast: j1 <> j2, typ: C.TyAnd t1 t2 }
infer (C.TmAnno e typ) z = do
  ast <- check (skipAnno e) typ z
  pure { ast, typ }
  where skipAnno :: C.Tm -> C.Tm
        skipAnno (C.TmAnno e' _) = e'
        skipAnno e' = e'
infer (C.TmToString e) z = do
  { ast: j, typ: t, var: y } <- infer' e
  let ast = j <> [ addProp (JSVar z) (toIndex C.TyString)
    (JSApp (JSAccessor "toString" (JSIndexer (toIndex t) (JSVar y))) []) ]
  pure { ast, typ: C.TyString }
infer (C.TmLet x e1 e2 global) z = do
  order <- asks (_.evalOrder)
  case order of
    CBV -> do { ast: j1, typ: t1 } <- infer e1 (variable x)
              { ast: j2, typ: t2 } <- addTmBind x t1 $ infer e2 z
              pure { ast: [export $ initialize $ variable x] <> j1 <> j2, typ: t2 }
    CBN -> do { ast: j1, typ: t1, var: y } <- infer' e1
              { ast: j2, typ: t2 } <- addTmBind x t1 $ infer e2 z
              let def = JSVariableIntroduction (variable x) $ Just $ lazyObj y j1
              pure { ast: [export def] <> j2, typ: t2 }
  where export = if global then JSExport else identity
infer (C.TmMain e) _ = do
  z <- freshVarName
  { ast: j , typ } <- infer e z
  let block = [initialize z] <> j <> [JSReturn $ JSVar z]
      ast = [ JSExport $ JSFunction (Just "main") [] $ JSBlock block ]
  pure { ast, typ }
infer e _ = unsafeCrashWith $ "FIXME: infer" <+> show e

infer' :: C.Tm -> CodeGen { ast :: AST, typ :: C.Ty, var :: Name }
infer' (C.TmVar x) = do
  typ <- lookupTmBind x
  order <- asks (_.evalOrder)
  case order of
    CBV -> pure { ast: [], typ, var: variable x }
    CBN -> do var <- freshVarName
              pure { ast: [ JSVariableIntroduction var $ Just $ JSAccessor "get" (JSVar (variable x)) ], typ, var }
infer' (C.TmAnno e typ) = do
  { ast, var } <- check' e typ
  pure { ast, typ, var }
infer' e = do
  var <- freshVarName
  { ast, typ } <- infer e var
  pure { ast: [ initialize var ] <> ast, typ, var }

-- TODO: change (infer' e) to (infer e y) if t .=. typ
check :: C.Tm -> C.Ty -> Name -> CodeGen AST
check e t y = do
  { ast, typ, var: x } <- infer' e
  (ast <> _) <$> subtype typ t x y true

check' :: C.Tm -> C.Ty -> CodeGen { ast :: AST, var :: Name }
check' e t = do
  { ast: j1, typ, var: x } <- infer' e
  if t .=. typ then pure { ast: j1, var: x }
  else do
    y <- freshVarName
    j2 <- subtype typ t x y true
    pure { ast: j1 <> [ initialize y ] <> j2, var: y }

data Arg = TmArg Name C.Ty | TyArg C.Ty

distapp :: C.Ty -> Name -> Arg -> Name -> CodeGen { ast :: AST, typ :: C.Ty }
distapp t _ _ _ | isTopLike t = pure { ast: [], typ: C.TyTop }
distapp (C.TyAnd ta tb) x arg z = do
  { ast: j1, typ: t1 } <- distapp ta x arg z
  { ast: j2, typ: t2 } <- distapp tb x arg z
  pure { ast: j1 <> j2, typ: C.TyAnd t1 t2 }
distapp t@(C.TyArrow targ tret _) x (TmArg y t') z =
  let app var = JSApp (JSIndexer (toIndex t) (JSVar x)) [JSVar var, JSVar z] in
  if targ .=. t' then pure { ast: [ app y ], typ: tret }
  else do
    order <- asks (_.evalOrder)
    ast <- case order of
      CBV -> do y0 <- freshVarName
                j <- subtype t' targ y y0 true
                pure $ [ initialize y0 ] <> j <> [ app y0 ]
      CBN -> do y1 <- freshVarName
                y2 <- freshVarName
                j <- subtype t' targ y1 y2 true
                let block = [ JSVariableIntroduction y1 $ Just $ JSAccessor "get" (JSVar y), initialize y2 ] <> j
                y' <- freshVarName
                pure [ JSVariableIntroduction y' $ Just $ lazyObj y2 block, app y' ]
    pure { ast, typ: tret }
distapp t@(C.TyForall a _ tbody) x (TyArg t') z =
  pure { ast: [ JSApp (JSIndexer (toIndex t) (JSVar x)) [toIndices t', JSVar z] ]
       , typ: C.tySubst a t' tbody
       }
distapp t _ _ _ = throwError $ "expected an applicable type, but got" <+> show t

proj :: C.Ty -> Name -> Label -> Name -> EvalOrder -> AST
proj t x l z o = unsafeFromJust $ go t
  where go :: C.Ty -> Maybe AST
        go t' | isTopLike t' = Nothing
        go (C.TyAnd ta tb) =
          case go ta, go tb of Nothing, Nothing -> Nothing
                               Nothing, Just j2 -> Just j2
                               Just j1, Nothing -> Just j1
                               Just j1, Just j2 -> Just $ j1 <> j2
        go t'@(C.TyRcd l' _ _) | l == l' =
          Just [ assignObj z [access (JSIndexer (toIndex t') (JSVar x))] ]
        go _  = Nothing
        access :: JS -> JS
        access = case o of CBV -> identity
                           CBN -> JSAccessor "get"

subtype :: C.Ty -> C.Ty -> Name -> Name -> Boolean -> CodeGen AST
subtype _ t _ _ _ | isTopLike t = pure []
subtype C.TyBot t _ y _ = pure [ JSAssignment (JSIndexer (toIndex t) (JSVar y)) JSNullLiteral ]
subtype ta tb x y true | ta .=. tb = pure [ assignObj y [JSVar x] ]
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
  j1 <- subtype tb1 ta1 x1 y1 true
  x2 <- freshVarName
  y2 <- freshVarName
  j2 <- subtype ta2 tb2 x2 y2 true
  order <- asks (_.evalOrder)
  let func = case order of
        CBV -> let block = [ initialize y1 ] <> j1
                        <> [ initialize x2, JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar y1, JSVar x2] ] <> j2 in
               JSFunction Nothing [x1, y2] (JSBlock block)
        CBN -> let arg = lazyObj y1 ([ JSVariableIntroduction x1 $ Just $ JSAccessor "get" (JSVar "p")
                                     , initialize y1 ] <> j1)
                   block = [ initialize x2, JSApp (JSIndexer (toIndex ta) (JSVar x)) [arg, JSVar x2] ] <> j2 in
               JSFunction Nothing ["p", y2] (JSBlock block)
  pure [ addProp (JSVar y) (toIndex tb) func ]
subtype ta@(C.TyForall a _ ta2) tb@(C.TyForall b _ tb2) x y _ = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype ta2 (C.tySubst b (C.TyVar a) tb2) x0 y0 true
  let block = [ initialize x0, JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar (variable a), JSVar x0] ] <> j
      func = JSFunction Nothing [variable a, y0] (JSBlock block) 
  pure [ addProp (JSVar y) (toIndex tb) func ]
subtype r1@(C.TyRcd l1 t1 _) r2@(C.TyRcd l2 t2 _) x y _ | l1 == l2 = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype t1 t2 x0 y0 true
  order <- asks (_.evalOrder)
  case order of
    CBV -> pure $ [ JSVariableIntroduction x0 $ Just $ JSIndexer (toIndex r1) (JSVar x)
                  , initialize y0 ] <> j <> [ addProp (JSVar y) (toIndex r2) (JSVar y0) ]
    CBN -> let rvalue = lazyObj y0 ([ JSVariableIntroduction x0 $ Just $
                                        JSAccessor "get" (JSIndexer (toIndex r1) (JSVar x))
                                    , initialize y0 ] <> j) in
           pure [ addProp (JSVar y) (toIndex r2) rvalue ]
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
subtype (C.TyVar a) (C.TyVar a') x y _ | a == a' = let index = "$$index" in
  pure [ JSForOf index (JSVar (variable a)) $ JSAssignment (JSIndexer (JSVar index) (JSVar y))
                                                           (JSIndexer (JSVar index) (JSVar x)) ]
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
  let block = (if y1 == y then [] else [initialize y1])
           <> (if y2 == y then [] else [initialize y2])
           <> [ JSApp (JSIndexer (toIndex f1) (JSVar x1)) [JSVar "p", JSVar y1]
              , JSApp (JSIndexer (toIndex f2) (JSVar x2)) [JSVar "p", JSVar y2] ]
           <> j
      func = JSFunction Nothing ["p", y] (JSBlock block)
  pure { ast: [ addProp (JSVar z) (toIndex f) func ], x: x1, y: x2 }
unsplit { z, tx: f1@(C.TyForall _ _ t1), ty: f2@(C.TyForall _ _ t2), tz: f@(C.TyForall a _ t) } = do
  x1 <- freshVarName
  x2 <- freshVarName
  y <- freshVarName
  { ast: j, x: y1, y: y2 } <- unsplit { z: y, tx: t1, ty: t2, tz: t }
  let block = (if y1 == y then [] else [initialize y1])
           <> (if y2 == y then [] else [initialize y2])
           <> [ JSApp (JSIndexer (toIndex f1) (JSVar x1)) [JSVar (variable a), JSVar y1]
              , JSApp (JSIndexer (toIndex f2) (JSVar x2)) [JSVar (variable a), JSVar y2] ]
           <> j
      func = JSFunction Nothing [variable a, y] (JSBlock block)
  pure { ast: [ addProp (JSVar z) (toIndex f) func ], x: x1, y: x2 }
unsplit { z, tx: r1@(C.TyRcd _ t1 _), ty: r2@(C.TyRcd _ t2 _), tz: r@(C.TyRcd _ t _) } = do
  x1 <- freshVarName
  x2 <- freshVarName
  y <- freshVarName
  { ast: j, x: y1, y: y2 } <- unsplit { z: y, tx: t1, ty: t2, tz: t }
  order <- asks (_.evalOrder)
  let init = [ initialize y ]
          <> (if y1 == y then [] else [initialize y1])
          <> (if y2 == y then [] else [initialize y2])
      ast = case order of
        CBV -> init <> [ assignObj y1 [JSIndexer (toIndex r1) (JSVar x1)]
                       , assignObj y2 [JSIndexer (toIndex r2) (JSVar x2)]]
                    <> j <> [ addProp (JSVar z) (toIndex r) (JSVar y) ]
        CBN -> let block = init <> [ assignObj y1 [JSAccessor "get" (JSIndexer (toIndex r1) (JSVar x1))]
                                   , assignObj y2 [JSAccessor "get" (JSIndexer (toIndex r2) (JSVar x2))]]
                                <> j in
               [ addProp (JSVar z) (toIndex r) (lazyObj y block) ]
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

initialize :: Name -> JS
initialize x = JSVariableIntroduction x $ Just $ JSObjectLiteral []

thunk :: Array JS -> JS
thunk = JSFunction Nothing [] <<< JSBlock

lazyObj :: Name -> Array JS -> JS
lazyObj x j = JSObjectLiteral [Getter "get" getter]
  where getter = j <>
          [ JSApp (JSVar "delete") [ thisGet ]
          , JSReturn (JSAssignment thisGet (JSVar x))
          ]
        thisGet = JSAccessor "get" (JSVar "this")

assignObj :: Name -> Array JS -> JS
assignObj z args = JSApp (JSAccessor "assign" (JSVar "Object")) ([JSVar z] <> args)

addProp :: JS -> JS -> JS -> JS
addProp o x f = JSAssignment (JSIndexer x o) f

variable :: Name -> Name
variable = ("$" <> _) <<< replaceAll (Pattern "'") (Replacement "$prime")
