module Language.CP.CodeGen where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.RWS (RWST, asks, evalRWST, local, modify)
import Data.Array (elem, sortBy, (:))
import Data.Either (Either)
import Data.Int (toNumber)
import Data.Map (Map, empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Subtyping (isTopLike, split, (===))
import Language.CP.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), LogicOp(..), UnOp(..)) as Op
import Language.CP.Syntax.Common (Label, Name)
import Language.CP.Syntax.Core as C
import Language.CP.Util ((<+>))
import Language.JS.AST (BinaryOperator(..), JS(..), UnaryOperator(..))
import Partial.Unsafe (unsafeCrashWith)

type CodeGen = RWST Ctx Unit Int (Except String)

type Ctx = { tmBindEnv :: Map Name C.Ty
           , tyBindEnv :: Map Name C.Ty
           }

runCodeGen :: C.Tm -> Either String JS
runCodeGen e = do
  (ast /\ _) /\ _ <- runExcept $
    evalRWST (infer e initialVarName) { tmBindEnv: empty, tyBindEnv: empty } 0
  pure $ JSFunction (Just "main") [] $ JSBlock $
      [ initialize initialVarName ] <> ast <> [ JSReturn $ JSVar initialVarName ]

type AST = Array JS

infer :: C.Tm -> Name -> CodeGen (AST /\ C.Ty)
infer C.TmUnit _ = do
  pure $ [] /\ C.TyTop
infer (C.TmInt i) z = do
  let ast = [ addProp (JSVar z) (toIndex C.TyInt) (JSNumericLiteral (toNumber i)) ]
  pure $ ast /\ C.TyInt
infer (C.TmDouble d) z = do
  let ast = [ addProp (JSVar z) (toIndex C.TyDouble) (JSNumericLiteral d) ]
  pure $ ast /\ C.TyDouble
infer (C.TmString s) z = do
  let ast = [ addProp (JSVar z) (toIndex C.TyString) (JSStringLiteral s) ]
  pure $ ast /\ C.TyString
infer (C.TmBool b) z = do
  let ast = [ addProp (JSVar z) (toIndex C.TyBool) (JSBooleanLiteral b) ]
  pure $ ast /\ C.TyBool
infer (C.TmUnary Op.Neg e) z = do
  y <- freshVarName
  j /\ t <- infer e y
  let ast typ = [ initialize y ] <> j
             <> [ addProp (JSVar z) (toIndex typ)
                          (JSUnary Negate (JSIndexer (toIndex typ) (JSVar y))) ]
  case t of C.TyInt -> pure $ ast C.TyInt /\ C.TyInt
            C.TyDouble -> pure $ ast C.TyDouble /\ C.TyDouble
            _ -> throwError $ "Neg is not defined for" <+> show t
infer (C.TmUnary Op.Not e) z = do
  y <- freshVarName
  j /\ t <- infer e y
  let ast = [ initialize y ] <> j
         <> [ addProp (JSVar z) (toIndex C.TyBool)
                      (JSUnary Not (JSIndexer (toIndex C.TyBool) (JSVar y))) ]
  case t of C.TyBool -> pure $ ast /\ C.TyBool
            _ -> throwError $ "Not is not defined for" <+> show t
infer (C.TmBinary (Op.Arith op) e1 e2) z = do
  x <- freshVarName
  y <- freshVarName
  j1 /\ t1 <- infer e1 x
  j2 /\ t2 <- infer e2 y
  let ast typ = [ initialize x, initialize y ] <> j1 <> j2
             <> [ addProp (JSVar z) (toIndex typ)
                          (JSBinary (map op) (JSIndexer (toIndex typ) (JSVar x))
                                             (JSIndexer (toIndex typ) (JSVar y))) ]
  case t1, t2 of C.TyInt, C.TyInt -> pure $ ast C.TyInt /\ C.TyInt
                 C.TyDouble, C.TyDouble -> pure $ ast C.TyDouble /\ C.TyDouble
                 _, _ -> throwError $
                   "ArithOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where map :: Op.ArithOp -> BinaryOperator
        map Op.Add = Add
        map Op.Sub = Subtract
        map Op.Mul = Multiply
        map Op.Div = Divide
        map Op.Mod = Modulus
infer (C.TmBinary (Op.Comp op) e1 e2) z = do
  x <- freshVarName
  y <- freshVarName
  j1 /\ t1 <- infer e1 x
  j2 /\ t2 <- infer e2 y
  let ast typ = [ initialize x, initialize y ] <> j1 <> j2
             <> [ addProp (JSVar z) (toIndex C.TyBool)
                          (JSBinary (map op) (JSIndexer (toIndex typ) (JSVar x))
                                             (JSIndexer (toIndex typ) (JSVar y))) ]
  case t1, t2 of C.TyInt, C.TyInt -> pure $ ast C.TyInt /\ C.TyBool
                 C.TyDouble, C.TyDouble -> pure $ ast C.TyDouble /\ C.TyBool
                 C.TyString, C.TyString -> pure $ ast C.TyString /\ C.TyBool
                 C.TyBool, C.TyBool -> pure $ ast C.TyBool /\ C.TyBool
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
  x <- freshVarName
  y <- freshVarName
  j1 /\ t1 <- infer e1 x
  j2 /\ t2 <- infer e2 y
  let ast = [ initialize x, initialize y ] <> j1 <> j2
         <> [ addProp (JSVar z) (toIndex C.TyBool)
                      (JSBinary (map op) (JSIndexer (toIndex C.TyBool) (JSVar x))
                                         (JSIndexer (toIndex C.TyBool) (JSVar y))) ]
  case t1, t2 of C.TyBool, C.TyBool -> pure $ ast /\ C.TyBool
                 _, _ -> throwError $
                   "LogicOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where map :: Op.LogicOp -> BinaryOperator
        map Op.And = And
        map Op.Or  = Or
infer (C.TmBinary (Op.Append) e1 e2) z = do
  x <- freshVarName
  y <- freshVarName
  j1 /\ t1 <- infer e1 x
  j2 /\ t2 <- infer e2 y
  let ast = [ initialize x, initialize y ] <> j1 <> j2
         <> [ addProp (JSVar z) (toIndex C.TyString)
                      (JSBinary Add (JSIndexer (toIndex C.TyString) (JSVar x))
                                    (JSIndexer (toIndex C.TyString) (JSVar y))) ]
  case t1, t2 of C.TyString, C.TyString -> pure $ ast /\ C.TyString
                 _, _ -> throwError $
                   "Append is not defined between" <+> show t1 <+> "and" <+> show t2
infer (C.TmIf e1 e2 e3) z = do
  x1 <- freshVarName
  j1 /\ t1 <- infer e1 x1
  if t1 == C.TyBool then do
    x2 <- freshVarName
    x3 <- freshVarName
    j2 /\ t2 <- infer e2 x2
    j3 /\ t3 <- infer e3 x3
    if t2 === t3 then do
      y2 <- freshVarName
      y3 <- freshVarName
      let ast = [ initialize x1, initialize x2, initialize x3 ] <> j1
             <> [ JSVariableIntroduction y2 $ Just $ thunk $ j2 <> [JSReturn (JSVar x2)]
                , JSVariableIntroduction y3 $ Just $ thunk $ j3 <> [JSReturn (JSVar x3)]
                , assignObj z [JSConditional (JSIndexer (toIndex C.TyBool) (JSVar x1))
                                             (JSApp (JSVar y2) []) (JSApp (JSVar y3) [])]
                ]
      pure $ ast /\ t2
    else throwError $ "if-branches expected two equivalent types, but got"
                   <+> show t2 <+> "and" <+> show t3
  else throwError $ "if-condition expected Bool, but got" <+> show t1
infer (C.TmVar x) z = do
  env <- asks (_.tmBindEnv)
  case lookup x env of
    Just t  -> pure $ [ assignObj z [JSVar x] ] /\ t
    Nothing -> throwError $ "term variable" <+> show x <+> "is undefined"
infer (C.TmFix x e t) z = do
  j <- addTmBind x t $ check e t x
  f <- freshVarName
  let ast = [ JSVariableIntroduction f $ Just $ JSFunction Nothing [x] $ JSBlock j
            , assignObj z [JSApp (JSVar "new") [thunk [JSApp (JSVar f) [JSVar "this"]]]]
            ]
  pure $ ast /\ t
infer (C.TmAbs x e targ tret _) z
  | isTopLike tret = infer C.TmUnit z
  | otherwise = do
      y <- freshVarName
      j <- addTmBind x targ $ check e tret y
      let typ = C.TyArrow targ tret false
          fun = JSFunction Nothing [x] $ JSBlock $ [initialize y] <> j <> [JSReturn $ JSVar y]
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure $ ast /\ typ
infer (C.TmApp e1 e2 _) z = do
  x <- freshVarName
  j1 /\ t1 <- infer e1 x
  case app t1 of
    Just { targ: t2, tret: t3 } -> do
      y <- freshVarName
      j2 <- check e2 t2 y
      j3 <- dist t1 x (TmArg (JSVar y)) z
      pure $ ([ initialize x, initialize y ] <> j1 <> j2 <> j3) /\ t3
    Nothing -> throwError $ "expected an applicable type, but got" <+> show t1
infer (C.TmTAbs a td e t _) z
  | isTopLike t = infer C.TmUnit z
  | otherwise = do
      y <- freshVarName
      j <- addTyBind a td $ check e t y
      let typ = C.TyForall a td t
          fun = JSFunction Nothing [a] $ JSBlock $ [initialize y] <> j <> [JSReturn $ JSVar y]
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure $ ast /\ typ
infer (C.TmTApp e t) z = do
  y <- freshVarName
  j1 /\ tf <- infer e y
  case tapp tf of
    Just { param, tdis, tbody } -> do
      disjoint t tdis
      j2 <- dist tf y (TyArg (toIndex t)) z
      pure $ ([ initialize y ] <> j1 <> j2) /\ C.tySubst param t tbody
    Nothing -> throwError $ "expected an type-applicable type, but got" <+> show tf
infer (C.TmRcd l t e) z
  | isTopLike t = infer C.TmUnit z
  | otherwise = do
      y <- freshVarName
      j <- check e t y
      let typ = C.TyRcd l t false
          fun = thunk $ [initialize y] <> j <> [JSReturn $ JSVar y]
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure $ ast /\ typ
infer (C.TmPrj e l) z = do
  y <- freshVarName
  j1 /\ t1 <- infer e y
  case prj t1 of
    Just { label, typ: t2 } | label == l -> do
      j2 <- dist t1 y Label z
      pure $ ([ initialize y ] <> j1 <> j2) /\ t2
    _ -> throwError $ "label" <+> show l <+> "is absent in" <+> show t1
infer (C.TmMerge e1 e2) z = do
  j1 /\ t1 <- infer e1 z
  j2 /\ t2 <- infer e2 z
  disjoint t1 t2
  pure $ (j1 <> j2) /\ C.TyAnd t1 t2
infer (C.TmAnno e t) z = do
  j <- check e t z
  pure $ j /\ t
infer (C.TmToString e) z = do
  y <- freshVarName
  j /\ t <- infer e y
  let ast = [ initialize y ] <> j
         <> [ addProp (JSVar z) (toIndex C.TyString)
                      (JSApp (JSAccessor "toString" (JSIndexer (toIndex t) (JSVar y))) []) ]
  pure $ ast /\ C.TyString
infer e _ = unsafeCrashWith $ "FIXME: infer" <+> show e

check :: C.Tm -> C.Ty -> Name -> CodeGen AST
check e t y = do
  x <- freshVarName
  j1 /\ t' <- infer e x
  j2 <- if t === t' then pure [ assignObj y [JSVar x] ]
        else subtype t' t x y
  pure $ [ initialize x ] <> j1 <> j2

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

prj :: C.Ty -> Maybe { label :: Label, typ :: C.Ty }
prj (C.TyRcd label typ _) = Just { label, typ }
prj C.TyTop = Just { label: "$top", typ: C.TyTop }
prj (C.TyAnd t1 t2) | Just { label: l1, typ: t1' } <- prj t1
                    , Just { label: l2, typ: t2' } <- prj t2
                    , l1 == l2 = Just { label: l1, typ: C.TyAnd t1' t2' }
prj _ = Nothing

data Arg = TmArg JS | TyArg JS | Label

dist :: C.Ty -> Name -> Arg -> Name -> CodeGen AST
dist t _ _ _ | isTopLike t = pure []
dist (C.TyAnd ta tb) x arg z = do
  j1 <- dist ta x arg z
  j2 <- dist tb x arg z
  pure $ j1 <> j2
dist t x (TmArg y) z = do
  pure [ assignObj z [JSApp (JSIndexer (toIndex t) (JSVar x)) [y]] ]
dist t x (TyArg y) z = do
  pure [ assignObj z [JSApp (JSIndexer (toIndex t) (JSVar x)) [y]] ]
dist t x Label z = do
  pure [ assignObj z [JSApp (JSIndexer (toIndex t) (JSVar x)) []] ]

disjoint :: C.Ty -> C.Ty -> CodeGen Unit
disjoint _ _ = pure unit -- FIXME!

subtype :: C.Ty -> C.Ty -> Name -> Name -> CodeGen AST
subtype _ tb _ _ | isTopLike tb = pure []
subtype ta tb x z | Just (tb1 /\ tb2) <- split tb = do
  y1 <- freshVarName
  y2 <- freshVarName
  j1 <- subtype ta tb1 x y1
  j2 <- subtype ta tb2 x y2
  j3 <- unsplit { x: y1, y: y2, z, tx: tb1, ty: tb2, tz: tb }
  pure $ [ initialize y1, initialize y2 ] <> j1 <> j2 <> j3
subtype ta@(C.TyArrow _ ta2 _) tb@(C.TyArrow _ tb2 _) x y = do
  x2 <- freshVarName
  y2 <- freshVarName
  j2 <- subtype ta2 tb2 x2 y2
  let block = [ JSVariableIntroduction x2 $ Just $
                  JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar "p"]
              , initialize y2 ]
           <> j2 <> [ JSReturn $ JSVar y2 ]
      func = JSFunction Nothing ["p"] (JSBlock block) 
  pure [ addProp (JSVar y) (toIndex tb) func ]
subtype ta@(C.TyForall a _ ta2) tb@(C.TyForall b _ tb2) x y = do
  x2 <- freshVarName
  y2 <- freshVarName
  j2 <- subtype ta2 (C.tySubst b (C.TyVar a) tb2) x2 y2
  let block = [ JSVariableIntroduction x2 $ Just $
                  JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar a]
              , initialize y2 ]
           <> j2 <> [ JSReturn $ JSVar y2 ]
      func = JSFunction Nothing [a] (JSBlock block) 
  pure [ addProp (JSVar y) (toIndex tb) func ]
subtype r1@(C.TyRcd l1 t1 _) r2@(C.TyRcd l2 t2 _) x y | l1 == l2 = do
  x0 <- freshVarName
  y0 <- freshVarName
  j <- subtype t1 t2 x0 y0
  let block = [ JSVariableIntroduction x0 $ Just $
                  JSApp (JSIndexer (toIndex r1) (JSVar x)) []
              , initialize y0 ]
           <> j <> [ JSReturn $ JSVar y0 ]
  pure [ addProp (JSVar y) (toIndex r2) (thunk block) ]
subtype (C.TyAnd ta tb) tc x y = subtype ta tc x y <|> subtype tb tc x y
subtype ta tb x y
  | ta == tb = pure [ JSAssignment (JSIndexer (toIndex tb) (JSVar y))
                                   (JSIndexer (toIndex ta) (JSVar x)) ]
  | otherwise = throwError $ show ta <> " is not a subtype of " <> show tb

type Splittee = {  x :: Name,  y :: Name,  z :: Name
                , tx :: C.Ty, ty :: C.Ty, tz :: C.Ty
                }

unsplit :: Splittee -> CodeGen AST
unsplit { x, y, z, tx: _, ty: _, tz: C.TyAnd _ _ } =
  pure [ assignObj z [JSVar x, JSVar y] ]
unsplit { x: x1, y: x2, z, tx: f1@(C.TyArrow _ t1 _), ty: f2@(C.TyArrow _ t2 _), tz: f@(C.TyArrow _ t _) } = do
  y1 <- freshVarName
  y2 <- freshVarName
  y <- freshVarName
  j <- unsplit { x: y1, y: y2, z: y, tx: t1, ty: t2, tz: t }
  let block = [ JSVariableIntroduction y1 $ Just $ JSApp (JSIndexer (toIndex f1) (JSVar x1)) [JSVar "p"]
              , JSVariableIntroduction y2 $ Just $ JSApp (JSIndexer (toIndex f2) (JSVar x2)) [JSVar "p"]
              , initialize y ] <> j <> [ JSReturn $ JSVar y ]
      func = JSFunction Nothing ["p"] (JSBlock block)
  pure [ addProp (JSVar z) (toIndex f) func ]
unsplit { x: x1, y: x2, z, tx: f1@(C.TyForall _ _ t1), ty: f2@(C.TyForall _ _ t2), tz: f@(C.TyForall a _ t) } = do
  y1 <- freshVarName
  y2 <- freshVarName
  y <- freshVarName
  j <- unsplit { x: y1, y: y2, z: y, tx: t1, ty: t2, tz: t }
  let block = [ JSVariableIntroduction y1 $ Just $ JSApp (JSIndexer (toIndex f1) (JSVar x1)) [JSVar a]
              , JSVariableIntroduction y2 $ Just $ JSApp (JSIndexer (toIndex f2) (JSVar x2)) [JSVar a]
              , initialize y ] <> j <> [ JSReturn $ JSVar y ]
      func = JSFunction Nothing [a] (JSBlock block)
  pure [ addProp (JSVar z) (toIndex f) func ]
unsplit { x: x1, y: x2, z, tx: r1@(C.TyRcd _ t1 _), ty: r2@(C.TyRcd _ t2 _), tz: r@(C.TyRcd _ t _) } = do
  y1 <- freshVarName
  y2 <- freshVarName
  y <- freshVarName
  j <- unsplit { x: y1, y: y2, z: y, tx: t1, ty: t2, tz: t }
  let ast = [ JSVariableIntroduction y1 $ Just $ JSApp (JSIndexer (toIndex r1) (JSVar x1)) []
            , JSVariableIntroduction y2 $ Just $ JSApp (JSIndexer (toIndex r2) (JSVar x2)) []
            , initialize y ] <> j <> [ addProp (JSVar z) (toIndex r) (JSVar y) ]
  pure ast
unsplit s = unsafeCrashWith $ "cannot unsplit" <+> show s

toIndex :: C.Ty -> JS
toIndex = JSTemplateLiteral <<< go []
  where
    go :: Array Name -> C.Ty -> String
    go _ t | isBaseType t = show t
    go as (C.TyArrow _ t _) = "fun_" <> go as t
    go as (C.TyForall a _ t) = "forall_" <> go (a:as) t
    go as (C.TyRcd l t _) = "rcd_" <> l <> "_" <> go as t
    go as (C.TyAnd t1 t2) =
      "andBegin_" <> joinWith "_" (map (go as) (sortBy typeOrdering (flattenAnd (C.TyAnd t1 t2)))) <> "_andEnd"
    go as (C.TyVar a) = if a `elem` as then a else "${" <> a <> "}"
    go t _ = unsafeCrashWith $ "cannot use as an index: " <> show t
    typeOrdering :: C.Ty -> C.Ty -> Ordering
    typeOrdering ta tb | isBaseType ta && isBaseType tb = compare (show ta) (show tb)
    typeOrdering ta _  | isBaseType ta = LT
    typeOrdering _ tb  | isBaseType tb = GT
    typeOrdering (C.TyArrow _ ta _)  (C.TyArrow _ tb _) = typeOrdering ta tb
    typeOrdering (C.TyArrow _ _ _) _ = GT
    typeOrdering _ (C.TyArrow _ _ _ ) = LT
    typeOrdering _ _ = EQ
    flattenAnd :: C.Ty -> Array C.Ty
    flattenAnd (C.TyAnd ta tb) = flattenAnd ta <> flattenAnd tb
    flattenAnd t = [t]
    isBaseType :: C.Ty -> Boolean
    isBaseType C.TyBool = true
    isBaseType C.TyInt = true
    isBaseType C.TyDouble = true
    isBaseType C.TyString = true
    isBaseType _ = false

initialVarName :: Name
initialVarName = "$0"

freshVarName :: CodeGen Name
freshVarName = do
  count <- modify (_ + 1)
  pure $ "$" <> show count

addTmBind :: forall a. Name -> C.Ty -> CodeGen a -> CodeGen a
addTmBind x t = local (\ctx -> ctx { tmBindEnv = insert x t ctx.tmBindEnv })

addTyBind :: forall a. Name -> C.Ty -> CodeGen a -> CodeGen a
addTyBind a t = local (\ctx -> ctx { tyBindEnv = insert a t ctx.tyBindEnv })

initialize :: Name -> JS
initialize x = JSVariableIntroduction x $ Just $ JSObjectLiteral []

thunk :: Array JS -> JS
thunk = JSFunction Nothing [] <<< JSBlock

assignObj :: Name -> Array JS -> JS
assignObj z args = JSApp (JSAccessor "assign" (JSVar "Object")) ([JSVar z] <> args)

addProp :: JS -> JS -> JS -> JS
addProp o x f = JSAssignment (JSIndexer x o) f
