module Language.CP.Compiler where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Maybe.Trans (MaybeT, lift, runMaybeT)
import Control.Monad.State (State, get, put)
import Control.Plus as Plus
import Data.Array (sortBy)
import Data.Map (Map, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.Number (fromString)
import Data.String (joinWith)
import Data.Tuple.Nested ((/\))
import Language.CP.Subtyping (isTopLike, split)
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Core as C
import Language.CP.Util (unsafeFromJust)
import Language.JS.AST (JS(..))
import Partial.Unsafe (unsafeCrashWith)

type CtxCodeGen = { varCount   :: Int
                  , tmBindEnv  :: Map Name C.Ty
                  }

type JsAst =  { ast :: Array JS
              , var :: String
              , typ :: C.Ty
}

typeToString :: C.Ty -> String
typeToString C.TyInt = "Int"
typeToString C.TyDouble = "Double"
typeToString C.TyString = "String"
typeToString C.TyBool = "Bool"
typeToString (C.TyArrow _ to _) = arrowToString to
typeToString (C.TyAnd t1 t2) = andToString t1 t2
-- typeToString C.TyRcd label ty _ = "Rcd_" <> label <> "_" <> typeToString ty
typeToString _ = ""

andToString :: C.Ty -> C.Ty -> String
andToString ta tb = "andBegin_" <> joinWith "_" (map typeToString (sortBy typeOrdering (flattenAnd (C.TyAnd ta tb)))) <> "_andEnd"

typeOrdering :: C.Ty -> C.Ty -> Ordering
typeOrdering ta tb | isBaseType ta && isBaseType tb = compare (typeToString ta) (typeToString tb)
typeOrdering ta _  | isBaseType ta = LT
typeOrdering _ tb  | isBaseType tb = GT
typeOrdering (C.TyArrow _ ta _)  (C.TyArrow _ tb _) = typeOrdering ta tb
typeOrdering (C.TyArrow _ _ _) _ = GT
typeOrdering _ (C.TyArrow _ _ _ ) = LT
typeOrdering _ _ = EQ

flattenAnd :: C.Ty -> Array C.Ty
flattenAnd (C.TyAnd ta tb) = flattenAnd ta <> flattenAnd tb
flattenAnd t = [t]

arrowToString :: C.Ty -> String
arrowToString t = "fun_" <> typeToString t

getNewVarName :: State CtxCodeGen String
getNewVarName = do
  ctx <- get
  put $ ctx {varCount = ctx.varCount + 1}
  pure $ "var_" <> show ctx.varCount

infer :: C.Tm -> State CtxCodeGen JsAst
infer C.TmUnit = do
  z <- getNewVarName
  let ast = [ JSVariableIntroduction z (Just $ JSObjectLiteral []) ]
  pure {ast: ast, var: z, typ: C.TyTop}
infer (C.TmInt i) = do
  z <- getNewVarName
  let ast = [ JSVariableIntroduction z (Just $ JSObjectLiteral [typeToString (C.TyInt) /\ (JSNumericLiteral <<< unsafeFromJust <<< fromString <<< show $ i)]) ]
  pure {ast: ast, var: z, typ: C.TyInt}
infer (C.TmDouble d) = do
  z <- getNewVarName
  let ast = [ JSVariableIntroduction z (Just $ JSObjectLiteral [typeToString (C.TyDouble) /\ JSNumericLiteral d]) ]
  pure {ast: ast, var: z, typ: C.TyDouble}
infer (C.TmBool b) = do
  z <- getNewVarName
  let ast = [ JSVariableIntroduction z (Just $ JSObjectLiteral [typeToString (C.TyBool) /\ JSBooleanLiteral b]) ]
  pure {ast: ast, var: z, typ: C.TyBool}
infer (C.TmVar x) = do 
  ctx <- get
  case lookup x ctx.tmBindEnv of
    Just t  -> pure $ {ast: [], var: x, typ: t}
    Nothing -> unsafeCrashWith "TmVar: variable not found in tmBindEnv"
infer (C.TmAbs x tm targ tret _)  
  | isTopLike tret    = infer C.TmUnit
  | otherwise         = do
      ctx <- get
      put $ ctx {tmBindEnv = insert x targ ctx.tmBindEnv}
      m   <- runMaybeT $ check tm tret
      case m of
        Just {ast: j, var: y} -> do
          ctx' <- get
          put $ ctx' {tmBindEnv = ctx.tmBindEnv}
          z <- getNewVarName
          let ty = C.TyArrow targ tret false
          let func = JSFunction Nothing [x] (JSBlock (j <> [JSReturn $ JSVar y]))
          let ast = [ JSVariableIntroduction z $ Just (JSObjectLiteral [typeToString ty /\ func]) ]
          pure {ast: ast, var: z, typ: ty}
        Nothing               -> unsafeCrashWith "TmAbs: Type Error"
infer (C.TmFix x tm ty) = do
  ctx <- get
  put $ ctx {tmBindEnv = insert x ty ctx.tmBindEnv}
  m   <- runMaybeT $ check tm ty
  case m of
    Just {ast: j, var: y} -> do
      ctx' <- get
      put ctx' {tmBindEnv = ctx.tmBindEnv}
      let func = JSFunction Nothing [] (JSBlock (j <> [JSReturn $ JSVar y]))
      let ast = [ JSVariableIntroduction x (Just $ JSApp func []) ]
      pure {ast: ast, var: x, typ: ty }
    Nothing -> unsafeCrashWith "TmFix: Type Error"
infer (C.TmApp e1 e2 _) = do
  {ast: j1, var: x, typ: ta} <- infer e1
  case app ta of
    Just {targ : tb, tret : tc} -> do
      m <- runMaybeT $ check e2 tb
      case m of
        Just {ast: j2, var: y} -> do
          {ast: j3, var: z} <- dist ta x y
          pure $ {ast: j1 <> j2 <> j3, var: z, typ: tc}
        Nothing -> unsafeCrashWith "TmAppR: Type Error"
    Nothing -> unsafeCrashWith "TmAppL: Type Error"
infer (C.TmMerge e1 e2) = do
  {ast: j1, var: x, typ: ta} <- infer e1
  {ast: j2, var: y, typ: tb} <- infer e2
  d <- disjoint ta tb
  if d 
    then do
      z <- getNewVarName
      let ast = j1 <> j2 <> [JSVariableIntroduction z (Just $ JSApp (JSAccessor "assign" (JSVar "Object")) [JSObjectLiteral [], JSVar x, JSVar y])]
      pure {ast: ast, var: z, typ: C.TyAnd ta tb}
    else unsafeCrashWith "TmMerge: Only disjoint types can be merged"
infer (C.TmAnno tm ty) = do
  m <- runMaybeT $ check tm ty
  case m of
    Just {ast: j, var: x} -> pure {ast: j, var: x, typ: ty}
    Nothing -> unsafeCrashWith "TmAnno: TypeError"  
infer _ = infer C.TmUnit


check :: C.Tm -> C.Ty -> MaybeT (State CtxCodeGen) {ast:: Array JS, var:: String}
check tm chkTy = do
  {ast: j1, var: x, typ: infTy} <- lift $ infer tm
  if chkTy == infTy
    then pure {ast: j1, var: x}
    else do
      {ast: j2, var: y} <- subtype x infTy chkTy
      pure {ast: j1 <> j2, var: y}

app :: C.Ty -> Maybe {targ:: C.Ty, tret:: C.Ty}
app t | isTopLike t = Just {targ: C.TyTop, tret: C.TyTop}
app (C.TyAnd t1 t2) | Just {targ: targ1, tret: tret1} <- app t1
                    , Just {targ: targ2, tret: tret2} <- app t2
                    = Just {targ: C.TyAnd targ1 targ2, tret: C.TyAnd tret1 tret2}
app (C.TyArrow targ tret _) = Just {targ, tret}
app _ = Nothing

dist :: C.Ty -> String -> String -> State CtxCodeGen {ast :: Array JS, var :: String}
dist t _ _ | isTopLike t = do
  z <- getNewVarName
  pure {ast : [JSVariableIntroduction z (Just $ JSObjectLiteral [])], var: z }
dist (C.TyAnd ta tb) x y = do
  z <- getNewVarName
  {ast: j1, var: z1} <- dist ta x y
  {ast: j2, var: z2} <- dist tb x y
  let ast = j1 <> j2 <> [JSVariableIntroduction z (Just $ JSApp (JSAccessor "assign" (JSVar "Object")) [JSObjectLiteral [], JSVar z1, JSVar z2])]
  pure {ast: ast, var: z}
dist (C.TyArrow _ t _) x y = do
  z <- getNewVarName
  let ast = [JSVariableIntroduction z (Just $ JSApp (JSAccessor (arrowToString t) (JSVar x)) [JSVar y] )]
  pure {ast : ast, var: z}
dist _ _ _ = unsafeCrashWith "cannot dist"

disjoint :: C.Ty -> C.Ty -> State CtxCodeGen Boolean
disjoint _ _ = pure $ true

subtype :: String -> C.Ty -> C.Ty -> MaybeT (State CtxCodeGen) {ast:: Array JS, var:: String}
subtype x ta tb | isBaseType tb && ta == tb   = do
  y <- lift getNewVarName
  let ast = [ JSVariableIntroduction y (Just $ JSObjectLiteral [typeToString tb /\ JSAccessor (typeToString tb) (JSVar x)]) ]
  pure {ast: ast, var: y}
subtype _ _ tb  | isTopLike tb = do
  y <- lift getNewVarName
  pure {ast : [JSVariableIntroduction y (Just $ JSObjectLiteral [])], var: y}
subtype x ta tb | Just (tb1 /\ tb2) <- split tb = do
  {ast: j1, var: y1} <- subtype x ta tb1
  {ast: j2, var: y2} <- subtype x ta tb2
  {ast: j3, var: z}  <- lift $ merge y1 y2 tb1 tb2 tb
  pure {ast: j1 <> j2 <> j3, var: z}
subtype x (C.TyArrow ta1 ta2 _) (C.TyArrow tb1 tb2 _) = do
  {ast : _j1, var : _y1} <- subtype "x1" tb1 ta1
  x2 <- lift getNewVarName
  {ast : j2, var : y2} <- subtype x2 ta2 tb2
  y <- lift getNewVarName
  let t1 = arrowToString ta2
  let t2 = arrowToString tb2
  let block  = [JSVariableIntroduction x2 (Just $ JSApp (JSAccessor t1 $ JSVar x) [JSVar "p"])]
            <> j2
            <> [JSReturn $ JSVar y2]
  let func = JSFunction Nothing ["p"] (JSBlock block) 
  let ast = [JSVariableIntroduction y (Just $ JSObjectLiteral [ t2 /\ func ])]
  pure $ {ast: ast, var: y}
subtype x (C.TyAnd ta tb) tc = subtype x ta tc <|> subtype x tb tc
subtype _ _ _ = Plus.empty

-- split :: C.Ty -> Maybe (C.Ty /\ C.Ty)
-- split (C.TyAnd t1 t2) = Just (t1 /\ t2)
-- split (C.TyArrow targ tret _) | Just (t1 /\ t2) <- split tret = Just ((C.TyArrow targ t1 false) /\ (C.TyArrow targ t2 false))
-- split _ = Nothing

merge :: String -> String -> C.Ty -> C.Ty -> C.Ty -> State CtxCodeGen {ast:: Array JS, var:: String}
merge x y _ _ (C.TyAnd _ _) = do
  z <- getNewVarName
  let ast = [JSVariableIntroduction z (Just $ JSApp (JSAccessor "assign" (JSVar "Object")) [JSObjectLiteral [], JSVar x, JSVar y])]
  pure {ast: ast, var: z}
merge x1 x2 (C.TyArrow _ t1 _) (C.TyArrow _ t2 _) (C.TyArrow _ t _) = do
  z <- getNewVarName
  y1 <- getNewVarName
  y2 <- getNewVarName
  {ast: j, var: y} <- merge y1 y2 t1 t2 t
  let block =  [ JSVariableIntroduction y1 (Just $ JSApp (JSAccessor (arrowToString t1) $ JSVar x1) [JSVar "p"])
               , JSVariableIntroduction y2 (Just $ JSApp (JSAccessor (arrowToString t2) $ JSVar x2) [JSVar "p"])]
            <> j
            <> [JSReturn $ JSVar y]
  let func = JSFunction Nothing ["p"] (JSBlock block) 
  let ast = [JSVariableIntroduction z (Just $ JSObjectLiteral [ (arrowToString t) /\ func ])]
  pure $ {ast: ast, var: z}
merge _ _ _ _ _ = unsafeCrashWith "Cannot merge"

isBaseType :: C.Ty -> Boolean
isBaseType C.TyBool = true
isBaseType C.TyInt = true
isBaseType C.TyDouble = true
isBaseType C.TyString = true
isBaseType _ = false