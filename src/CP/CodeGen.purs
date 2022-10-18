module Language.CP.CodeGen where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.RWS (RWST, asks, evalRWST, local, modify)
import Data.Array (elem, sort, (:))
import Data.Either (Either)
import Data.Int (toNumber)
import Data.Map (Map, empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), Replacement(..), joinWith, replaceAll)
import Data.Tuple.Nested ((/\))
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

runCodeGen :: C.Tm -> Either String (Array JS)
runCodeGen e = do
  { ast, var } /\ _ <- runExcept $
    evalRWST (infer' e) { tmBindEnv: empty, tyBindEnv: empty } 0
  pure [ JSFunction (Just "toIndex") ["t"] $ JSBlock
          [JSIfElse (JSBinary EqualTo (JSAccessor "length" (JSVar "t")) (JSNumericLiteral 1.0))
                    (JSBlock [JSReturn $ JSIndexer (JSNumericLiteral 0.0) (JSVar "t")])
                    (Just $ JSBlock [JSReturn $ JSBinary Add
                      (JSBinary Add
                        (JSStringLiteral "(&")
                        (JSApp (JSAccessor "join" (JSApp (JSAccessor "sort" (JSVar "t")) [])) [JSStringLiteral "&"]))
                      (JSStringLiteral "&)")])]
       , JSFunction (Just "main") [] $ JSBlock $ ast <> [ JSReturn $ JSVar var ]
       ]

type AST = Array JS

infer :: C.Tm -> Name -> CodeGen { ast :: AST, typ :: C.Ty }
infer C.TmUnit _ = pure { ast: [], typ: C.TyTop }
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
infer (C.TmBinary (Op.Arith op) e1 e2) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  { ast: j2, typ: t2, var: y } <- infer' e2
  let ast typ = j1 <> j2 <> [ addProp (JSVar z) (toIndex typ)
    (JSBinary (map op) (JSIndexer (toIndex typ) (JSVar x))
                       (JSIndexer (toIndex typ) (JSVar y))) ]
  case t1, t2 of C.TyInt,    C.TyInt    -> pure { ast: ast C.TyInt,    typ: C.TyInt    }
                 C.TyDouble, C.TyDouble -> pure { ast: ast C.TyDouble, typ: C.TyDouble }
                 _, _ -> throwError $
                   "ArithOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where map :: Op.ArithOp -> BinaryOperator
        map Op.Add = Add
        map Op.Sub = Subtract
        map Op.Mul = Multiply
        map Op.Div = Divide
        map Op.Mod = Modulus
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
infer (C.TmBinary (Op.Append) e1 e2) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  { ast: j2, typ: t2, var: y } <- infer' e2
  let ast = j1 <> j2 <> [ addProp (JSVar z) (toIndex C.TyString)
    (JSBinary Add (JSIndexer (toIndex C.TyString) (JSVar x))
                  (JSIndexer (toIndex C.TyString) (JSVar y))) ]
  case t1, t2 of C.TyString, C.TyString -> pure { ast, typ: C.TyString }
                 _, _ -> throwError $
                   "Append is not defined between" <+> show t1 <+> "and" <+> show t2
infer (C.TmIf e1 e2 e3) z = do
  { ast: j1, typ: t1, var: x1 } <- infer' e1
  if t1 == C.TyBool then do
    { ast: j2, typ: t2, var: x2 } <- infer' e2
    { ast: j3, typ: t3, var: x3 } <- infer' e3
    if t2 === t3 then do
      y2 <- freshVarName
      y3 <- freshVarName
      let ast = j1 <> [ JSVariableIntroduction y2 $ Just $ thunk $ j2 <> [JSReturn (JSVar x2)]
                      , JSVariableIntroduction y3 $ Just $ thunk $ j3 <> [JSReturn (JSVar x3)]
                      , assignObj z [JSConditional (JSIndexer (toIndex C.TyBool) (JSVar x1))
                                                   (JSApp (JSVar y2) []) (JSApp (JSVar y3) [])]
                      ]
      pure { ast, typ: t2 }
    else throwError $ "if-branches expected two equivalent types, but got"
                   <+> show t2 <+> "and" <+> show t3
  else throwError $ "if-condition expected Bool, but got" <+> show t1
infer (C.TmVar x) z = do
  typ <- lookupTmBind x
  pure { ast: [ assignObj z [JSApp (JSVar (variable x)) []] ], typ }
infer (C.TmFix x e typ) z = do
  j <- addTmBind x typ $ check e typ z
  let ast = [ JSVariableIntroduction (variable x) $ Just $ thunk [JSReturn (JSVar z)] ] <> j
  pure { ast, typ }
infer (C.TmAbs x e targ tret _) z
  | isTopLike tret = infer C.TmUnit z
  | otherwise = do
      { ast: j, var: y } <- addTmBind x targ $ check' e tret
      let typ = C.TyArrow targ tret false
          fun = JSFunction Nothing [variable x] $ JSBlock $ j <> [JSReturn $ JSVar y]
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure { ast, typ }
infer (C.TmApp e1 e2 _) z = do
  { ast: j1, typ: t1, var: x } <- infer' e1
  case app t1 of
    Just { targ: t2, tret: t3 } -> do
      { ast: j2, var: y } <- check' e2 t2
      y' <- freshVarName
      j3 <- dist t1 x (TmArg (JSVar y')) z
      let j2' = [ JSVariableIntroduction y' $ Just $ thunk $ j2 <> [JSReturn $ JSVar y] ]
      pure { ast: j1 <> j2' <> j3, typ: t3 }
    Nothing -> throwError $ "expected an applicable type, but got" <+> show t1
infer (C.TmTAbs a td e t _) z
  | isTopLike t = infer C.TmUnit z
  | otherwise = do
      { ast: j, var: y } <- addTyBind a td $ check' e t
      let typ = C.TyForall a td t
          fun = JSFunction Nothing [variable a] $ JSBlock $ j <> [JSReturn $ JSVar y]
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure { ast, typ }
infer (C.TmTApp e t) z = do
  { ast: j1, typ: tf, var: y } <- infer' e
  case tapp tf of
    Just { param, tbody } -> do
      j2 <- dist tf y (TyArg (toIndices t)) z
      pure { ast: j1 <> j2, typ: C.tySubst param t tbody }
    Nothing -> throwError $ "expected an type-applicable type, but got" <+> show tf
infer (C.TmRcd l t e) z
  | isTopLike t = infer C.TmUnit z
  | otherwise = do
      { ast: j, var: y } <- check' e t
      let typ = C.TyRcd l t false
          fun = thunk $ j <> [JSReturn $ JSVar y]
          ast = [ addProp (JSVar z) (toIndex typ) fun ]
      pure { ast, typ }
infer (C.TmPrj e l) z = do
  { ast: j1, typ: t1, var: y } <- infer' e
  case prj t1 of
    Just { label, typ } | label == l -> do
      j2 <- dist t1 y Label z
      pure $ { ast: j1 <> j2, typ }
    _ -> throwError $ "label" <+> show l <+> "is absent in" <+> show t1
infer (C.TmMerge e1 e2) z = do
  { ast: j1, typ: t1 } <- infer e1 z
  { ast: j2, typ: t2 } <- infer e2 z
  pure { ast: j1 <> j2, typ: C.TyAnd t1 t2 }
infer (C.TmAnno e typ) z = do
  ast <- check e typ z
  pure { ast, typ }
infer (C.TmToString e) z = do
  { ast: j, typ: t, var: y } <- infer' e
  let ast = j <> [ addProp (JSVar z) (toIndex C.TyString)
    (JSApp (JSAccessor "toString" (JSIndexer (toIndex t) (JSVar y))) []) ]
  pure { ast, typ: C.TyString }
infer e _ = unsafeCrashWith $ "FIXME: infer" <+> show e

infer' :: C.Tm -> CodeGen { ast :: AST, typ :: C.Ty, var :: Name }
infer' (C.TmVar x) = do
  typ <- lookupTmBind x
  var <- freshVarName
  pure { ast: [ JSVariableIntroduction var $ Just $ JSApp (JSVar (variable x)) [] ], typ, var }
infer' (C.TmAnno e typ) = do
  { ast, var } <- check' e typ
  pure { ast, typ, var }
infer' e = do
  var <- freshVarName
  { ast, typ } <- infer e var
  pure { ast: [ initialize var ] <> ast, typ, var }

-- TODO: eliminate infer' if t === typ
check :: C.Tm -> C.Ty -> Name -> CodeGen AST
check e t y = do
  { ast, typ, var: x } <- infer' e
  if t === typ then (_.ast) <$> infer e y
  else (ast <> _) <$> subtype typ t x y

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
subtype (C.TyVar a) (C.TyVar a') x y | a == a' = let index = "$$index" in
  pure [ JSForOf index (JSVar (variable a)) $ JSAssignment (JSIndexer (JSVar index) (JSVar y))
                                                           (JSIndexer (JSVar index) (JSVar x)) ]
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
  let block = [ JSVariableIntroduction y1 $ Just $ JSApp (JSIndexer (toIndex r1) (JSVar x1)) []
              , JSVariableIntroduction y2 $ Just $ JSApp (JSIndexer (toIndex r2) (JSVar x2)) []
              , initialize y ] <> j <> [ JSReturn $ JSVar y ]
      func = JSFunction Nothing [] (JSBlock block)
  pure [ addProp (JSVar z) (toIndex r) func ]
unsplit s = unsafeCrashWith $ "cannot unsplit" <+> show s

toIndices :: C.Ty -> JS
toIndices (C.TyVar a) = JSVar $ variable a
toIndices t@(C.TyAnd _ _) = JSArrayLiteral $ map toIndex $ flatten t
toIndices t = JSArrayLiteral [toIndex t]

toIndex :: C.Ty -> JS
toIndex = JSTemplateLiteral <<< go []
  where
    go :: Array Name -> C.Ty -> String
    go _ t | isBaseType t = show t
    go as (C.TyArrow _ t _) = "fun_" <> go as t
    go as (C.TyForall a _ t) = "forall_" <> go (a:as) t
    go as (C.TyRcd l t _) = "rcd_" <> l <> ":" <> go as t
    go as t@(C.TyAnd _ _) = "(&" <> joinWith "&" (sort (map (go as) (flatten t))) <> "&)"
    go as (C.TyVar a) = if a `elem` as then a else "${toIndex(" <> variable a <> ")}"
    go _ t = unsafeCrashWith $ "cannot use as an index: " <> show t
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

assignObj :: Name -> Array JS -> JS
assignObj z args = JSApp (JSAccessor "assign" (JSVar "Object")) ([JSVar z] <> args)

addProp :: JS -> JS -> JS -> JS
addProp o x f = JSAssignment (JSIndexer x o) f

variable :: Name -> Name
variable = ("$" <> _) <<< replaceAll (Pattern "'") (Replacement "$prime")
