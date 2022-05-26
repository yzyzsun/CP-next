module Language.CP.CodeGen where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.State (State, evalState, get, put)
import Data.Array (sortBy)
import Data.Int (toNumber)
import Data.Map (Map, empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Tuple.Nested ((/\))
import Language.CP.Subtyping (isTopLike, split)
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Core as C
import Language.JS.AST (JS(..))
import Partial.Unsafe (unsafeCrashWith)

type CodeGen = State CodeGenCtx

type CodeGenCtx = { varCount  :: Int
                  , tmBindEnv :: Map Name C.Ty
                  , tyBindEnv :: Map Name C.Ty
                  }

runCodeGen :: C.Tm -> JS
runCodeGen e =
  let { ast, var } = evalState (infer e) { varCount: 0, tmBindEnv: empty, tyBindEnv: empty } in
  JSFunction (Just "main") [] $ JSBlock $ ast <> [ JSReturn $ JSVar var ]

type AST = Array JS
type ASTVar = { ast :: AST, var :: Name }
type ASTVarTyp = { ast :: AST, var :: Name, typ :: C.Ty }

infer :: C.Tm -> CodeGen ASTVarTyp
infer C.TmUnit = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSObjectLiteral [] ]
  pure { ast, var: z, typ: C.TyTop }
infer (C.TmInt i) = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSObjectLiteral [toIndex C.TyInt /\ JSNumericLiteral (toNumber i)] ]
  pure { ast, var: z, typ: C.TyInt }
infer (C.TmDouble d) = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSObjectLiteral [toIndex C.TyDouble /\ JSNumericLiteral d] ]
  pure { ast, var: z, typ: C.TyDouble }
infer (C.TmBool b) = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSObjectLiteral [toIndex C.TyBool /\ JSBooleanLiteral b] ]
  pure { ast, var: z, typ: C.TyBool }
infer (C.TmVar x) = do 
  ctx <- get
  case lookup x ctx.tmBindEnv of
    Just t  -> pure { ast: [], var: x, typ: t }
    Nothing -> unsafeCrashWith "TmVar: variable not found in tmBindEnv"
infer (C.TmFix x e t) = do
  ctx <- get
  put $ ctx { tmBindEnv = insert x t ctx.tmBindEnv }
  { ast: j, var: y } <- check e t
  ctx' <- get
  put ctx' { tmBindEnv = ctx.tmBindEnv }
  let func = JSFunction Nothing [] $ JSBlock $ j <> [JSReturn $ JSVar y]
      ast = [ JSVariableIntroduction x $ Just $ JSApp func [] ]
  pure { ast, var: x, typ: t }
infer (C.TmAbs x e targ tret _)  
  | isTopLike tret = infer C.TmUnit
  | otherwise = do
      ctx <- get
      put $ ctx { tmBindEnv = insert x targ ctx.tmBindEnv }
      { ast: j, var: y } <- check e tret
      ctx' <- get
      put $ ctx' { tmBindEnv = ctx.tmBindEnv }
      z <- freshVarName
      let typ = C.TyArrow targ tret false
          func = JSFunction Nothing [x] $ JSBlock $ j <> [JSReturn $ JSVar y]
          ast = [ JSVariableIntroduction z $ Just $ JSObjectLiteral [toIndex typ /\ func] ]
      pure { ast, var: z, typ }
infer (C.TmApp e1 e2 _) = do
  { ast: j1, var: x, typ: ta } <- infer e1
  case app ta of
    Just { targ: tb, tret: tc } -> do
      { ast: j2, var: y } <- check e2 tb
      { ast: j3, var: z } <- dist ta x y TmArg
      pure { ast: j1 <> j2 <> j3, var: z, typ: tc }
    Nothing -> unsafeCrashWith "TmAppL: Type Error"
infer (C.TmTAbs a td e t _) = do
  ctx <- get
  put $ ctx { tyBindEnv = insert a td ctx.tyBindEnv }
  { ast: j, var: y } <- check e t
  ctx' <- get
  put $ ctx' { tyBindEnv = ctx.tyBindEnv }
  z <- freshVarName
  let typ = C.TyForall a td t
      func = JSFunction Nothing [a] $ JSBlock $ j <> [JSReturn $ JSVar y]
      ast = [ JSVariableIntroduction z $ Just $ JSObjectLiteral [toIndex typ /\ func] ]
  pure { ast, var: z, typ }
infer (C.TmTApp e t) = do
  { ast: j1, var: y, typ: tf } <- infer e
  case tapp tf of
    Just { param, tdis, tbody } -> do
      disjoint t tdis
      { ast: j2, var: z } <- dist tf y (toIndex t) TyArg
      pure { ast: j1 <> j2, var: z, typ: C.tySubst param t tbody }
    Nothing -> unsafeCrashWith "TmTAppL: Type Error"
infer (C.TmRcd l t e) = do
  { ast: j, var: x } <- check e t
  z <- freshVarName
  let typ = C.TyRcd l t false
      ast = j <> [ JSVariableIntroduction z $ Just $ JSObjectLiteral [toIndex typ /\ JSVar x] ]
  pure { ast, var: z, typ }
infer (C.TmPrj e l) = do
  { ast: j1, var: x, typ: ta } <- infer e
  case prj ta of
    Just tb -> do
      { ast: j2, var: z } <- dist ta x l Label
      pure { ast: j1 <> j2, var: z, typ: tb }
    Nothing -> unsafeCrashWith "TmPrj: Type Error"
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
infer _ = infer C.TmUnit

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

prj :: C.Ty -> Maybe C.Ty
prj (C.TyRcd _ t _) = Just t
prj C.TyTop = Just C.TyTop
prj (C.TyAnd t1 t2) | Just t1' <- prj t1, Just t2' <- prj t2 = Just (C.TyAnd t1' t2')
prj _ = Nothing

data Arg = TmArg | TyArg | Label

dist :: C.Ty -> Name -> Name -> Arg -> CodeGen ASTVar
dist t _ _ _ | isTopLike t = do
  z <- freshVarName
  pure { ast: [ JSVariableIntroduction z $ Just $ JSObjectLiteral [] ], var: z }
dist (C.TyAnd ta tb) x y arg = do
  z <- freshVarName
  { ast: j1, var: z1 } <- dist ta x y arg
  { ast: j2, var: z2 } <- dist tb x y arg
  let ast = j1 <> j2 <> [ JSVariableIntroduction z $ Just $ merge z1 z2 ]
  pure { ast, var: z }
dist t x y TmArg = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSApp (JSAccessor (toIndex t) (JSVar x)) [JSVar y] ]
  pure { ast, var: z }
dist t x s TyArg = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSApp (JSAccessor (toIndex t) (JSVar x)) [JSStringLiteral s] ]
  pure { ast, var: z }
dist t x _ Label = do
  z <- freshVarName
  let ast = [ JSVariableIntroduction z $ Just $ JSAccessor (toIndex t) (JSVar x) ]
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
  let block = [ JSVariableIntroduction x2 $ Just $ JSApp (JSAccessor (toIndex ta) (JSVar x)) [JSVar "p"] ]
           <> j2 <> [ JSReturn $ JSVar y2 ]
      func = JSFunction Nothing ["p"] (JSBlock block) 
      ast = [ JSVariableIntroduction y $ Just $ JSObjectLiteral [ toIndex tb /\ func ] ]
  pure { ast, var: y }
subtype x ta@(C.TyForall a _ ta2) tb@(C.TyForall b _ tb2) = do
  x2 <- freshVarName
  y <- freshVarName
  { ast: j2, var: y2 } <- subtype x2 ta2 (C.tySubst b (C.TyVar a) tb2)
  let block = [ JSVariableIntroduction x2 $ Just $ JSApp (JSAccessor (toIndex ta) (JSVar x)) [JSVar a] ]
           <> j2 <> [ JSReturn $ JSVar y2 ]
      func = JSFunction Nothing [a] (JSBlock block) 
      ast = [ JSVariableIntroduction y $ Just $ JSObjectLiteral [ toIndex tb /\ func ] ]
  pure { ast, var: y }
subtype x r1@(C.TyRcd l1 t1 _) r2@(C.TyRcd l2 t2 _) | l1 == l2 = do
  x0 <- freshVarName
  { ast: j, var: y0 } <- subtype x0 t1 t2
  y <- freshVarName
  let ast = [ JSVariableIntroduction x0 $ Just $ JSAccessor (toIndex r1) (JSVar x) ]
         <> j <> [ JSVariableIntroduction y $ Just $ JSObjectLiteral [ toIndex r2 /\ JSVar y0 ] ]
  pure { ast, var: y }
subtype x (C.TyAnd ta tb) tc = subtype x ta tc <|> subtype x tb tc
subtype x ta tb
  | ta == tb = do
      y <- freshVarName
      let ast = [ JSVariableIntroduction y $ Just $ JSObjectLiteral [toIndex tb /\ JSAccessor (toIndex tb) (JSVar x)] ]
      pure { ast, var: y }
  | otherwise = unsafeCrashWith $ show ta <> " is not a subtype of " <> show tb

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
  let block = [ JSVariableIntroduction y1 $ Just $ JSApp (JSAccessor (toIndex f1) (JSVar x1)) [JSVar "p"]
              , JSVariableIntroduction y2 $ Just $ JSApp (JSAccessor (toIndex f2) (JSVar x2)) [JSVar "p"]
              ] <> j <> [ JSReturn $ JSVar y ]
      func = JSFunction Nothing ["p"] (JSBlock block)
      ast = [ JSVariableIntroduction z $ Just $ JSObjectLiteral [ toIndex f /\ func ] ]
  pure { ast, var: z }
unsplit { x: x1, y: x2, tx: f1@(C.TyForall _ _ t1), ty: f2@(C.TyForall _ _ t2), tz: f@(C.TyForall a _ t) } = do
  z <- freshVarName
  y1 <- freshVarName
  y2 <- freshVarName
  { ast: j, var: y } <- unsplit { x: y1, y: y2, tx: t1, ty: t2, tz: t }
  let block = [ JSVariableIntroduction y1 $ Just $ JSApp (JSAccessor (toIndex f1) (JSVar x1)) [JSVar a]
              , JSVariableIntroduction y2 $ Just $ JSApp (JSAccessor (toIndex f2) (JSVar x2)) [JSVar a]
              ] <> j <> [ JSReturn $ JSVar y ]
      func = JSFunction Nothing [a] (JSBlock block)
      ast = [ JSVariableIntroduction z $ Just $ JSObjectLiteral [ toIndex f /\ func ] ]
  pure { ast, var: z }
unsplit { x: x1, y: x2, tx: r1@(C.TyRcd _ t1 _), ty: r2@(C.TyRcd _ t2 _), tz: r@(C.TyRcd _ t _) } = do
  z <- freshVarName
  y1 <- freshVarName
  y2 <- freshVarName
  { ast: j, var: y } <- unsplit { x: y1, y: y2, tx: t1, ty: t2, tz: t }
  let ast = [ JSVariableIntroduction y1 $ Just $ JSAccessor (toIndex r1) (JSVar x1)
            , JSVariableIntroduction y2 $ Just $ JSAccessor (toIndex r2) (JSVar x2)
            ] <> j <> [ JSVariableIntroduction z $ Just $ JSObjectLiteral [ toIndex r /\ JSVar y ] ]
  pure { ast, var: z }
unsplit s = unsafeCrashWith $ "cannot unsplit " <> show s

toIndex :: C.Ty -> String
toIndex C.TyInt = "Int"
toIndex C.TyDouble = "Double"
toIndex C.TyString = "String"
toIndex C.TyBool = "Bool"
toIndex (C.TyArrow _ t _) = "fun_" <> toIndex t
toIndex (C.TyForall _ _ t) = "forall_" <> toIndex t
toIndex (C.TyRcd l t _) = "rcd_" <> l <> "_" <> toIndex t
toIndex (C.TyAnd t1 t2) =
  "andBegin_" <> joinWith "_" (map toIndex (sortBy typeOrdering (flattenAnd (C.TyAnd t1 t2)))) <> "_andEnd"
toIndex _ = "" -- FIXME: TyVar

typeOrdering :: C.Ty -> C.Ty -> Ordering
typeOrdering ta tb | isBaseType ta && isBaseType tb = compare (toIndex ta) (toIndex tb)
typeOrdering ta _  | isBaseType ta = LT
typeOrdering _ tb  | isBaseType tb = GT
typeOrdering (C.TyArrow _ ta _)  (C.TyArrow _ tb _) = typeOrdering ta tb
typeOrdering (C.TyArrow _ _ _) _ = GT
typeOrdering _ (C.TyArrow _ _ _ ) = LT
typeOrdering _ _ = EQ

isBaseType :: C.Ty -> Boolean
isBaseType C.TyBool = true
isBaseType C.TyInt = true
isBaseType C.TyDouble = true
isBaseType C.TyString = true
isBaseType _ = false

flattenAnd :: C.Ty -> Array C.Ty
flattenAnd (C.TyAnd ta tb) = flattenAnd ta <> flattenAnd tb
flattenAnd t = [t]

freshVarName :: CodeGen Name
freshVarName = do
  ctx <- get
  put $ ctx { varCount = ctx.varCount + 1 }
  pure $ "var_" <> show ctx.varCount

initialize :: Name -> JS
initialize x = JSVariableIntroduction x $ Just $ JSObjectLiteral []

-- TODO: use {...x, ...y} in ES6+
merge :: Name -> Name -> JS
merge x y = JSApp (JSAccessor "assign" (JSVar "Object")) [JSObjectLiteral [], JSVar x, JSVar y]
