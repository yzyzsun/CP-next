module Language.CP.CodeGen where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.RWS (RWST, asks, evalRWST, local, modify)
import Data.Array (concat, foldl, length, (!!))
import Data.Array as A
import Data.Bifunctor (bimap, lmap, rmap)
import Data.Either (Either)
import Data.Int (toNumber)
import Data.List (List(..), elem, (:))
import Data.Map (Map, empty, fromFoldable, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), Replacement(..), joinWith, replaceAll)
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
import Record (delete)
import Type.Proxy (Proxy(..))

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
  pure $ [ JSFunction (Just "toIndex") ["t"] $ JSBlock
            [JSIfElse (JSBinary EqualTo (JSAccessor "length" (JSVar "t")) (JSNumericLiteral 1.0))
                      (JSBlock [JSReturn $ JSIndexer (JSNumericLiteral 0.0) (JSVar "t")])
                      (Just $ JSBlock [JSReturn $ JSBinary Add
                        (JSBinary Add
                          (JSStringLiteral "(&")
                          (JSApp (JSAccessor "join" (JSApp (JSAccessor "sort" (JSVar "t")) [])) [JSStringLiteral "&"]))
                        (JSStringLiteral "&)")])]
         ] <> ast

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
    typ@(C.TyArray t), C.TyArray t' | t === t' ->
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
    if t2 === t3 then do
      let ast = j1 <> [ JSIfElse (JSIndexer (toIndex C.TyBool) (JSVar var))
                                 (JSBlock j2) (Just (JSBlock j3)) ]
      pure { ast, typ: t2 }
    else throwError $ "if-branches expected two equivalent types, but got"
                   <+> show t2 <+> "and" <+> show t3
  else throwError $ "if-condition expected Bool, but got" <+> show t1
infer (C.TmVar x) z = do
  typ <- lookupTmBind x
  pure { ast: [ assignObj z [getVar x] ], typ }
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
infer (C.TmApp e1 e2 coercive) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  case app t1 of
    Just { targ: t2, tret: t3 } -> do
      { ast: j2, var: y } <- if coercive then check' e2 t2
                             else delete (Proxy :: Proxy "typ") <$> infer' e2
      order <- asks (_.evalOrder)
      case order of
        CBV -> let j3 = dist t1 x (TmArg (JSVar y)) z in
               pure { ast: j1 <> j2 <> j3, typ: t3 }
        CBN -> do y' <- freshVarName
                  let j3 = dist t1 x (TmArg (JSVar y')) z
                      j2' = [ JSVariableIntroduction y' $ Just $ lazyObj y j2 ]
                  pure { ast: j1 <> j2' <> j3, typ: t3 }
    Nothing -> throwError $ "expected an applicable type, but got" <+> show t1
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
  case tapp tf of
    Just { param, tbody } -> do
      let j2 = dist tf y (TyArg (toIndices t)) z
      pure { ast: j1 <> j2, typ: C.tySubst param t tbody }
    Nothing -> throwError $ "expected an type-applicable type, but got" <+> show tf
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
              let def = JSVariableIntroduction (variable x) $ Just $
                          JSObjectLiteral [LiteralName "get" (JSVar y)]
              pure { ast: j1 <> [export def] <> j2, typ: t2 }
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
              pure { ast: [ JSVariableIntroduction var $ Just $ getVar x ], typ, var }
infer' (C.TmAnno e typ) = do
  { ast, var } <- check' e typ
  pure { ast, typ, var }
infer' e = do
  var <- freshVarName
  { ast, typ } <- infer e var
  pure { ast: [ initialize var ] <> ast, typ, var }

-- TODO: change (infer' e) to (infer e y) if t === typ
check :: C.Tm -> C.Ty -> Name -> CodeGen AST
check e t y = do
  { ast, typ, var: x } <- infer' e
  (ast <> _) <$> subtype typ t x y

check' :: C.Tm -> C.Ty -> CodeGen { ast :: AST, var :: Name }
check' e t = do
  { ast: j1, typ, var: x } <- infer' e
  if t === typ then pure { ast: j1, var: x }
  else do
    y <- freshVarName
    j2 <- subtype typ t x y
    pure { ast: j1 <> [ initialize y ] <> j2, var: y }

app :: C.Ty -> Maybe { targ :: C.Ty, tret :: C.Ty }
app (C.TyArrow targ tret _) = Just { targ, tret }
app C.TyTop = Just { targ: C.TyTop, tret: C.TyTop }
app (C.TyAnd t1 t2) | Just { targ: targ1, tret: tret1 } <- app t1
                    , Just { targ: targ2, tret: tret2 } <- app t2
                    = Just { targ: C.TyAnd targ1 targ2, tret: C.TyAnd tret1 tret2 }
app _ = Nothing

tapp :: C.Ty -> Maybe { param :: Name, tdis :: C.Ty, tbody :: C.Ty }
tapp (C.TyForall param tdis tbody) = Just { param, tdis, tbody }
tapp C.TyTop = Just { param: "$top", tdis: C.TyTop, tbody: C.TyTop }
tapp (C.TyAnd t1 t2) | Just { param: param1, tdis: tdis1, tbody: tbody1 } <- tapp t1
                     , Just { param: param2, tdis: tdis2, tbody: tbody2 } <- tapp t2
                     = let tbody2' = C.tySubst param2 (C.TyVar param1) tbody2 in
                       Just { param: param1, tdis: C.TyAnd tdis1 tdis2, tbody: C.TyAnd tbody1 tbody2' }
tapp _ = Nothing

data Arg = TmArg JS | TyArg JS

dist :: C.Ty -> Name -> Arg -> Name -> AST
dist t _ _ _ | isTopLike t = []
dist (C.TyAnd ta tb) x arg z = dist ta x arg z <> dist tb x arg z
dist t x (TmArg y) z = [ JSApp (JSIndexer (toIndex t) (JSVar x)) [y, JSVar z] ]
dist t x (TyArg y) z = [ JSApp (JSIndexer (toIndex t) (JSVar x)) [y, JSVar z] ]

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

subtype :: C.Ty -> C.Ty -> Name -> Name -> CodeGen AST
subtype _ t _ _ | isTopLike t = pure []
subtype C.TyBot t _ y = pure [ JSAssignment (JSIndexer (toIndex t) (JSVar y)) JSNullLiteral ]
subtype ta tb x y | ta === tb = pure [ assignObj y [JSVar x] ]
subtype ta tb x z | Just (tb1 /\ tb2) <- split tb =
  if isTopLike tb1 then subtype ta tb2 x z
  else if isTopLike tb2 then subtype ta tb1 x z
  else do { ast: j3, x: y1, y: y2 } <- unsplit { z, tx: tb1, ty: tb2, tz: tb }
          let j0 = (if y1 == z then [] else [initialize y1])
                <> (if y2 == z then [] else [initialize y2])
          j1 <- subtype ta tb1 x y1
          j2 <- subtype ta tb2 x y2
          pure $ j0 <> j1 <> j2 <> j3
subtype ta@(C.TyArrow ta1 ta2 _) tb@(C.TyArrow tb1 tb2 _) x y = do
  x1 <- freshVarName
  y1 <- freshVarName
  j1 <- subtype tb1 ta1 x1 y1
  x2 <- freshVarName
  y2 <- freshVarName
  j2 <- subtype ta2 tb2 x2 y2
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
subtype ta@(C.TyForall a _ ta2) tb@(C.TyForall b _ tb2) x y = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype ta2 (C.tySubst b (C.TyVar a) tb2) x0 y0
  let block = [ initialize x0, JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar (variable a), JSVar x0] ] <> j
      func = JSFunction Nothing [variable a, y0] (JSBlock block) 
  pure [ addProp (JSVar y) (toIndex tb) func ]
subtype r1@(C.TyRcd l1 t1 _) r2@(C.TyRcd l2 t2 _) x y | l1 == l2 = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype t1 t2 x0 y0
  order <- asks (_.evalOrder)
  case order of
    CBV -> pure $ [ JSVariableIntroduction x0 $ Just $ JSIndexer (toIndex r1) (JSVar x)
                  , initialize y0 ] <> j <> [ addProp (JSVar y) (toIndex r2) (JSVar y0) ]
    CBN -> let rvalue = lazyObj y0 ([ JSVariableIntroduction x0 $ Just $
                                        JSAccessor "get" (JSIndexer (toIndex r1) (JSVar x))
                                    , initialize y0 ] <> j) in
           pure [ addProp (JSVar y) (toIndex r2) rvalue ]
subtype (C.TyAnd ta tb) tc x y = subtype ta tc x y <|> subtype tb tc x y
subtype (C.TyVar a) (C.TyVar a') x y | a == a' = let index = "$$index" in
  pure [ JSForOf index (JSVar (variable a)) $ JSAssignment (JSIndexer (JSVar index) (JSVar y))
                                                           (JSIndexer (JSVar index) (JSVar x)) ]
subtype ta tb x y
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

toIndices :: C.Ty -> JS
toIndices (C.TyVar a) = JSVar $ variable a
toIndices t@(C.TyAnd _ _) = JSArrayLiteral $ map toIndex $ flatten t
toIndices C.TyTop = JSArrayLiteral []
toIndices t = JSArrayLiteral [toIndex t]

toIndex :: C.Ty -> JS
toIndex = JSTemplateLiteral <<< fst <<< go Nil
  where
    go :: List Name -> C.Ty -> String /\ Boolean
    go _ t | isBaseType t    = show t /\ false
    go as (C.TyArrow _ t _)  = lmap ("fun_" <> _) (go as t)
    go as (C.TyForall a _ t) = lmap ("forall_" <> _) (go (a:as) t)
    go as (C.TyRcd l t _)    = lmap (("rcd_" <> l <> ":") <> _) (go as t)
    go as (C.TyArray t)      = lmap ("array_" <> _) (go as t)
    go as (C.TyVar a)        = if a `elem` as then a /\ false
                               else ("${toIndex(" <> variable a <> ")}") /\ true
    go as t@(C.TyAnd _ _)    = let flattened = flatten t in
      if length flattened == 1 then go as (unsafeFromJust (flattened !! 0))
      else let ts /\ b = foldl (\(ts /\ b) t -> bimap (flip A.insert ts) (b || _) (go as t))
                               ([] /\ false) flattened in
           if not b then ("(&" <> joinWith "&" ts <> "&)") /\ false
           else ("${toIndex(" <> print1 (JSArrayLiteral (go' as <$> flattened)) <> ")}") /\ true
    go _ t = unsafeCrashWith $ "cannot use as an index: " <> show t
    go' :: List Name -> C.Ty -> JS
    go' as (C.TyVar a) | not (a `elem` as) = JSUnary Spread (JSVar (variable a))
    go' as t = JSTemplateLiteral $ fst $ go as t
    isBaseType :: C.Ty -> Boolean
    isBaseType C.TyBool = true
    isBaseType C.TyInt = true
    isBaseType C.TyDouble = true
    isBaseType C.TyString = true
    isBaseType _ = false

flatten :: C.Ty -> Array C.Ty
flatten (C.TyAnd t1 t2) = flatten t1 <> flatten t2
flatten t | isTopLike t = []
          | otherwise   = [t]

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
          [ JSApp (JSAccessor "defineProperty" (JSVar "Object"))
              [ JSVar "this", JSStringLiteral "get", JSObjectLiteral [LiteralName "value" (JSVar x)] ]
          , JSReturn (JSVar x)
          ]

assignObj :: Name -> Array JS -> JS
assignObj z args = JSApp (JSAccessor "assign" (JSVar "Object")) ([JSVar z] <> args)

addProp :: JS -> JS -> JS -> JS
addProp o x f = JSAssignment (JSIndexer x o) f

variable :: Name -> Name
variable = ("$" <> _) <<< replaceAll (Pattern "'") (Replacement "$prime")

getVar :: Name -> JS
getVar x = JSAccessor "get" (JSVar (variable x))
