module Language.CP.CodeGen where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.RWS (RWST, asks, evalRWST, local, modify)
import Data.Array (elem, sortBy, (:))
import Data.Either (Either(..))
import Data.Int (toNumber)
import Data.Map (Map, empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Tuple.Nested ((/\))
import Language.CP.Subtyping (isTopLike, split, (===))
import Language.CP.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), LogicOp(..), UnOp(..)) as Op
import Language.CP.Syntax.Common (Label, Name)
import Language.CP.Syntax.Core as C
import Language.JS.AST (BinaryOperator(..), JS(..), UnaryOperator(..))
import Partial.Unsafe (unsafeCrashWith)

type CodeGen = RWST Ctx Unit Int (Except String)

type Ctx = { tmBindEnv :: Map Name C.Ty
           , tyBindEnv :: Map Name C.Ty
           }

runCodeGen :: C.Tm -> JS
runCodeGen e =
  case runExcept $ evalRWST (infer e) { tmBindEnv: empty, tyBindEnv: empty } 0 of
    Right ({ ast, var } /\ _) -> JSFunction (Just "main") [] $ JSBlock $ ast <> [ JSReturn $ JSVar var ]
    Left err -> unsafeCrashWith err

type AST = Array JS
type ASTVar = { ast :: AST, var :: Name }
type ASTVarTyp = { ast :: AST, var :: Name, typ :: C.Ty }

infer :: C.Tm -> CodeGen ASTVarTyp
infer C.TmUnit = do
  z <- freshVarName
  let ast = [ initialize z ]
  pure { ast, var: z, typ: C.TyTop }
infer (C.TmInt i) = do
  z <- freshVarName
  let ast = [ initialize z, addProp (JSVar z) (toIndex C.TyInt) (JSNumericLiteral (toNumber i)) ]
  pure { ast, var: z, typ: C.TyInt }
infer (C.TmDouble d) = do
  z <- freshVarName
  let ast = [ initialize z, addProp (JSVar z) (toIndex C.TyDouble) (JSNumericLiteral d) ]
  pure { ast, var: z, typ: C.TyDouble }
infer (C.TmString s) = do
  z <- freshVarName
  let ast = [ initialize z, addProp (JSVar z) (toIndex C.TyString) (JSStringLiteral s) ]
  pure { ast, var: z, typ: C.TyString }
infer (C.TmBool b) = do
  z <- freshVarName
  let ast = [ initialize z, addProp (JSVar z) (toIndex C.TyBool) (JSBooleanLiteral b) ]
  pure { ast, var: z, typ: C.TyBool }
infer (C.TmUnary Op.Neg e) = do
  { ast, var, typ } <- infer e
  z <- freshVarName
  let js t = { ast: ast <> [ initialize z, addProp (JSVar z) (toIndex t)
                                                   (JSUnary Negate (JSIndexer (toIndex t) (JSVar var))) ]
             , var: z, typ: t }
  case typ of C.TyInt -> pure $ js C.TyInt
              C.TyDouble -> pure $ js C.TyDouble
              _ -> throwError "TmUnary Neg: Type Error"
infer (C.TmUnary Op.Not e) = do
  { ast, var, typ } <- infer e
  z <- freshVarName
  let js = { ast: ast <> [ initialize z, addProp (JSVar z) (toIndex C.TyBool)
                                                 (JSUnary Not (JSIndexer (toIndex C.TyBool) (JSVar var))) ]
           , var: z, typ: C.TyBool }
  case typ of C.TyBool -> pure js
              _ -> throwError "TmUnary Not: Type Error"
infer (C.TmBinary (Op.Arith op) e1 e2) = do
  { ast: j1, var: x, typ: ta } <- infer e1
  { ast: j2, var: y, typ: tb } <- infer e2
  z <- freshVarName
  let js t = { ast: j1 <> j2 <> [ initialize z, addProp (JSVar z) (toIndex t)
                                                        (JSBinary (map op) (JSIndexer (toIndex t) (JSVar x))
                                                                           (JSIndexer (toIndex t) (JSVar y))) ]
             , var: z, typ: t }
  case ta, tb of C.TyInt, C.TyInt -> pure $ js C.TyInt
                 C.TyDouble, C.TyDouble -> pure $ js C.TyDouble
                 _, _ -> throwError "TmBinary Arith: Type Error"
  where map :: Op.ArithOp -> BinaryOperator
        map Op.Add = Add
        map Op.Sub = Subtract
        map Op.Mul = Multiply
        map Op.Div = Divide
        map Op.Mod = Modulus
infer (C.TmBinary (Op.Comp op) e1 e2) = do
  { ast: j1, var: x, typ: ta } <- infer e1
  { ast: j2, var: y, typ: tb } <- infer e2
  z <- freshVarName
  let js t = { ast: j1 <> j2 <> [ initialize z, addProp (JSVar z) (toIndex C.TyBool)
                                                        (JSBinary (map op) (JSIndexer (toIndex t) (JSVar x))
                                                                           (JSIndexer (toIndex t) (JSVar y))) ]
             , var: z, typ: C.TyBool }
  case ta, tb of C.TyInt, C.TyInt -> pure $ js C.TyInt
                 C.TyDouble, C.TyDouble -> pure $ js C.TyDouble
                 C.TyString, C.TyString -> pure $ js C.TyString
                 C.TyBool, C.TyBool -> pure $ js C.TyBool
                 _, _ -> throwError "TmBinary Comp: Type Error"
  where map :: Op.CompOp -> BinaryOperator
        map Op.Eql = EqualTo
        map Op.Neq = NotEqualTo
        map Op.Lt  = LessThan
        map Op.Le  = LessThanOrEqualTo
        map Op.Gt  = GreaterThan
        map Op.Ge  = GreaterThanOrEqualTo
infer (C.TmBinary (Op.Logic op) e1 e2) = do
  { ast: j1, var: x, typ: ta } <- infer e1
  { ast: j2, var: y, typ: tb } <- infer e2
  z <- freshVarName
  let js = { ast: j1 <> j2 <> [ initialize z, addProp (JSVar z) (toIndex C.TyBool)
                                                      (JSBinary (map op) (JSIndexer (toIndex C.TyBool) (JSVar x))
                                                                         (JSIndexer (toIndex C.TyBool) (JSVar y))) ]
           , var: z, typ: C.TyBool }
  case ta, tb of C.TyBool, C.TyBool -> pure js
                 _, _ -> throwError "TmBinary Logic: Type Error"
  where map :: Op.LogicOp -> BinaryOperator
        map Op.And = And
        map Op.Or  = Or
infer (C.TmBinary (Op.Append) e1 e2) = do
  { ast: j1, var: x, typ: ta } <- infer e1
  { ast: j2, var: y, typ: tb } <- infer e2
  z <- freshVarName
  let js = { ast: j1 <> j2 <> [ initialize z, addProp (JSVar z) (toIndex C.TyString)
                                                      (JSBinary Add (JSIndexer (toIndex C.TyString) (JSVar x))
                                                                    (JSIndexer (toIndex C.TyString) (JSVar y))) ]
           , var: z, typ: C.TyString }
  case ta, tb of C.TyString, C.TyString -> pure js
                 _, _ -> throwError "TmBinary Append: Type Error"
infer (C.TmIf e1 e2 e3) = do
  { ast: j1, var: x1, typ: t1 } <- infer e1
  if t1 == C.TyBool then do
    { ast: j2, var: x2, typ: t2 } <- infer e2
    { ast: j3, var: x3, typ: t3 } <- infer e3
    if t2 === t3 then do
      y2 <- freshVarName
      y3 <- freshVarName
      z <- freshVarName
      let ast = j1 <> [ JSVariableIntroduction y2 $ Just $ JSFunction Nothing [] $ JSBlock $ j2 <> [JSReturn (JSVar x2)]
                      , JSVariableIntroduction y3 $ Just $ JSFunction Nothing [] $ JSBlock $ j3 <> [JSReturn (JSVar x3)]
                      , JSVariableIntroduction z $ Just $ JSConditional (JSIndexer (toIndex C.TyBool) (JSVar x1))
                                                                        (JSApp (JSVar y2) []) (JSApp (JSVar y3) [])
                      ]
      pure { ast, var: z, typ: t2 }
    else throwError "TmIfThenElse: Type Error"
  else throwError "TmIfCond: Type Error"
infer (C.TmVar x) = do
  env <- asks (_.tmBindEnv)
  case lookup x env of
    Just t  -> pure { ast: [], var: x, typ: t }
    Nothing -> throwError "TmVar: variable not found in tmBindEnv"
infer (C.TmFix x e t) = do
  { ast: j, var: y } <- addTmBind x t $ check e t
  let func = JSFunction Nothing [] $ JSBlock $ j <> [JSReturn $ JSVar y]
      ast = [ JSVariableIntroduction x $ Just $ JSApp func [] ]
  pure { ast, var: x, typ: t }
infer (C.TmAbs x e targ tret _)  
  | isTopLike tret = infer C.TmUnit
  | otherwise = do
      { ast: j, var: y } <- addTmBind x targ $ check e tret
      z <- freshVarName
      let typ = C.TyArrow targ tret false
          func = JSFunction Nothing [x] $ JSBlock $ j <> [JSReturn $ JSVar y]
          ast = [ initialize z, addProp (JSVar z) (toIndex typ) func ]
      pure { ast, var: z, typ }
infer (C.TmApp e1 e2 _) = do
  { ast: j1, var: x, typ: ta } <- infer e1
  case app ta of
    Just { targ: tb, tret: tc } -> do
      { ast: j2, var: y } <- check e2 tb
      { ast: j3, var: z } <- dist ta x (TmArg (JSVar y))
      pure { ast: j1 <> j2 <> j3, var: z, typ: tc }
    Nothing -> throwError "TmAppL: Type Error"
infer (C.TmTAbs a td e t _) = do
  { ast: j, var: y } <- addTyBind a td $ check e t
  z <- freshVarName
  let typ = C.TyForall a td t
      func = JSFunction Nothing [a] $ JSBlock $ j <> [JSReturn $ JSVar y]
      ast = [ initialize z, addProp (JSVar z) (toIndex typ) func ]
  pure { ast, var: z, typ }
infer (C.TmTApp e t) = do
  { ast: j1, var: y, typ: tf } <- infer e
  case tapp tf of
    Just { param, tdis, tbody } -> do
      disjoint t tdis
      { ast: j2, var: z } <- dist tf y (TyArg (toIndex t))
      pure { ast: j1 <> j2, var: z, typ: C.tySubst param t tbody }
    Nothing -> throwError "TmTAppL: Type Error"
infer (C.TmRcd l t e) = do
  { ast: j, var: x } <- check e t
  z <- freshVarName
  let typ = C.TyRcd l t false
      ast = j <> [ initialize z, addProp (JSVar z) (toIndex typ) (JSVar x) ]
  pure { ast, var: z, typ }
infer (C.TmPrj e l) = do
  { ast: j1, var: x, typ: ta } <- infer e
  case prj ta of
    Just { label, typ: tb } | label == l -> do
      { ast: j2, var: z } <- dist ta x Label
      pure { ast: j1 <> j2, var: z, typ: tb }
    _ -> throwError "TmPrj: Type Error"
infer (C.TmMerge e1 e2) = do
  { ast: j1, var: x, typ: ta } <- infer e1
  { ast: j2, var: y, typ: tb } <- infer e2
  disjoint ta tb
  z <- freshVarName
  let ast = j1 <> j2 <> [ JSVariableIntroduction z $ Just $ merge x y ]
  pure { ast, var: z, typ: C.TyAnd ta tb }
infer (C.TmAnno e t) = do
  { ast: j, var: x } <- check e t
  pure { ast: j, var: x, typ: t }
infer (C.TmToString e) = do
  { ast: j, var: x, typ: t } <- infer e
  z <- freshVarName
  let ast = j <> [ initialize z, addProp (JSVar z) (toIndex C.TyString)
                                         (JSApp (JSAccessor "toString" (JSIndexer (toIndex t) (JSVar x))) []) ]
  pure { ast, var: z, typ: C.TyString }
infer _ = unsafeCrashWith "FIXME: not implemented"

check :: C.Tm -> C.Ty -> CodeGen ASTVar
check tm chkTy = do
  { ast: j1, var: x, typ: infTy } <- infer tm
  if chkTy == infTy then pure { ast: j1, var: x }
  else do { ast: j2, var: y } <- subtype x infTy chkTy
          pure { ast: j1 <> j2, var: y }

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

dist :: C.Ty -> Name -> Arg -> CodeGen ASTVar
dist t _ _ | isTopLike t = do
  z <- freshVarName
  pure { ast: [ JSVariableIntroduction z $ Just $ JSObjectLiteral [] ], var: z }
dist (C.TyAnd ta tb) x arg = do
  z <- freshVarName
  { ast: j1, var: z1 } <- dist ta x arg
  { ast: j2, var: z2 } <- dist tb x arg
  let ast = j1 <> j2 <> [ JSVariableIntroduction z $ Just $ merge z1 z2 ]
  pure { ast, var: z }
dist t x (TmArg y) = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSApp (JSIndexer (toIndex t) (JSVar x)) [y] ]
  pure { ast, var: z }
dist t x (TyArg y) = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSApp (JSIndexer (toIndex t) (JSVar x)) [y] ]
  pure { ast, var: z }
dist t x Label = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSIndexer (toIndex t) (JSVar x) ]
  pure { ast, var: z }

disjoint :: C.Ty -> C.Ty -> CodeGen Unit
disjoint _ _ = pure unit -- FIXME!

subtype :: Name -> C.Ty -> C.Ty -> CodeGen ASTVar
subtype _ _ tb  | isTopLike tb = do
  y <- freshVarName
  let ast = [ JSVariableIntroduction y $ Just $ JSObjectLiteral [] ]
  pure { ast, var: y }
subtype x ta tb | Just (tb1 /\ tb2) <- split tb = do
  { ast: j1, var: y1 } <- subtype x ta tb1
  { ast: j2, var: y2 } <- subtype x ta tb2
  { ast: j3, var: z }  <- unsplit { x: y1, y: y2, tx: tb1, ty: tb2, tz: tb }
  pure { ast: j1 <> j2 <> j3, var: z }
subtype x ta@(C.TyArrow _ ta2 _) tb@(C.TyArrow _ tb2 _) = do
  x2 <- freshVarName
  y <- freshVarName
  { ast: j2, var: y2 } <- subtype x2 ta2 tb2
  let block = [ JSVariableIntroduction x2 $ Just $ JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar "p"] ]
           <> j2 <> [ JSReturn $ JSVar y2 ]
      func = JSFunction Nothing ["p"] (JSBlock block) 
      ast = [ initialize y, addProp (JSVar y) (toIndex tb) func ]
  pure { ast, var: y }
subtype x ta@(C.TyForall a _ ta2) tb@(C.TyForall b _ tb2) = do
  x2 <- freshVarName
  y <- freshVarName
  { ast: j2, var: y2 } <- subtype x2 ta2 (C.tySubst b (C.TyVar a) tb2)
  let block = [ JSVariableIntroduction x2 $ Just $ JSApp (JSIndexer (toIndex ta) (JSVar x)) [JSVar a] ]
           <> j2 <> [ JSReturn $ JSVar y2 ]
      func = JSFunction Nothing [a] (JSBlock block) 
      ast = [ initialize y, addProp (JSVar y) (toIndex tb) func ]
  pure { ast, var: y }
subtype x r1@(C.TyRcd l1 t1 _) r2@(C.TyRcd l2 t2 _) | l1 == l2 = do
  x0 <- freshVarName
  { ast: j, var: y0 } <- subtype x0 t1 t2
  y <- freshVarName
  let ast = [ JSVariableIntroduction x0 $ Just $ JSIndexer (toIndex r1) (JSVar x) ]
         <> j <> [ initialize y, addProp (JSVar y) (toIndex r2) (JSVar y0) ]
  pure { ast, var: y }
subtype x (C.TyAnd ta tb) tc = subtype x ta tc <|> subtype x tb tc
subtype x ta tb
  | ta == tb = do
      y <- freshVarName
      let ast = [ JSVariableIntroduction y $ Just $ JSVar x ]
      pure { ast, var: y }
  | otherwise = throwError $ show ta <> " is not a subtype of " <> show tb

type Splittee = { x :: String, y :: String
                , tx :: C.Ty, ty :: C.Ty, tz :: C.Ty
                }

unsplit :: Splittee -> CodeGen ASTVar
unsplit { x, y, tx: _, ty: _, tz: C.TyAnd _ _ } = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ merge x y ]
  pure { ast, var: z }
unsplit { x: x1, y: x2, tx: f1@(C.TyArrow _ t1 _), ty: f2@(C.TyArrow _ t2 _), tz: f@(C.TyArrow _ t _) } = do
  z <- freshVarName
  y1 <- freshVarName
  y2 <- freshVarName
  { ast: j, var: y } <- unsplit { x: y1, y: y2, tx: t1, ty: t2, tz: t }
  let block = [ JSVariableIntroduction y1 $ Just $ JSApp (JSIndexer (toIndex f1) (JSVar x1)) [JSVar "p"]
              , JSVariableIntroduction y2 $ Just $ JSApp (JSIndexer (toIndex f2) (JSVar x2)) [JSVar "p"]
              ] <> j <> [ JSReturn $ JSVar y ]
      func = JSFunction Nothing ["p"] (JSBlock block)
      ast = [ initialize z, addProp (JSVar z) (toIndex f) func ]
  pure { ast, var: z }
unsplit { x: x1, y: x2, tx: f1@(C.TyForall _ _ t1), ty: f2@(C.TyForall _ _ t2), tz: f@(C.TyForall a _ t) } = do
  z <- freshVarName
  y1 <- freshVarName
  y2 <- freshVarName
  { ast: j, var: y } <- unsplit { x: y1, y: y2, tx: t1, ty: t2, tz: t }
  let block = [ JSVariableIntroduction y1 $ Just $ JSApp (JSIndexer (toIndex f1) (JSVar x1)) [JSVar a]
              , JSVariableIntroduction y2 $ Just $ JSApp (JSIndexer (toIndex f2) (JSVar x2)) [JSVar a]
              ] <> j <> [ JSReturn $ JSVar y ]
      func = JSFunction Nothing [a] (JSBlock block)
      ast = [ initialize z, addProp (JSVar z) (toIndex f) func ]
  pure { ast, var: z }
unsplit { x: x1, y: x2, tx: r1@(C.TyRcd _ t1 _), ty: r2@(C.TyRcd _ t2 _), tz: r@(C.TyRcd _ t _) } = do
  z <- freshVarName
  y1 <- freshVarName
  y2 <- freshVarName
  { ast: j, var: y } <- unsplit { x: y1, y: y2, tx: t1, ty: t2, tz: t }
  let ast = [ JSVariableIntroduction y1 $ Just $ JSIndexer (toIndex r1) (JSVar x1)
            , JSVariableIntroduction y2 $ Just $ JSIndexer (toIndex r2) (JSVar x2)
            ] <> j <> [ initialize z, addProp (JSVar z) (toIndex r) (JSVar y) ]
  pure { ast, var: z }
unsplit s = unsafeCrashWith $ "cannot unsplit " <> show s

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

freshVarName :: CodeGen Name
freshVarName = do
  count <- modify (_ + 1)
  pure $ "v_" <> show count

addTmBind :: forall a. Name -> C.Ty -> CodeGen a -> CodeGen a
addTmBind x t = local (\ctx -> ctx { tmBindEnv = insert x t ctx.tmBindEnv })

addTyBind :: forall a. Name -> C.Ty -> CodeGen a -> CodeGen a
addTyBind a t = local (\ctx -> ctx { tyBindEnv = insert a t ctx.tyBindEnv })

initialize :: Name -> JS
initialize x = JSVariableIntroduction x $ Just $ JSObjectLiteral []

-- TODO: use {...x, ...y} in ES6+
merge :: Name -> Name -> JS
merge x y = JSApp (JSAccessor "assign" (JSVar "Object")) [JSObjectLiteral [], JSVar x, JSVar y]

-- TODO: use object literals with computed property names in ES6+
addProp :: JS -> JS -> JS -> JS
addProp o x f = JSAssignment (JSIndexer x o) f
