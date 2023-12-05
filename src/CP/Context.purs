module Language.CP.Context where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Control.Monad.State (StateT, runStateT)
import Data.Bifunctor (rmap)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.List (List(..), null, singleton)
import Data.Map (Map, empty, fromFoldable, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source as S
import Parsing (Position(..))

type Typing = ReaderT Ctx (Except TypeError)

type Ctx = { tmBindEnv  :: Map Name C.Ty -- typing
           , tyBindEnv  :: Map Name C.Ty -- disjointness
           , tyAliasEnv :: Map Name S.Ty -- synonym
           , sortEnv    :: Map Name Name -- distinguishing
           , pos :: Pos
           }

data Pos = UnknownPos
         | Pos Position S.Tm Boolean

emptyCtx :: Ctx
emptyCtx =  { tmBindEnv  : empty
            , tyBindEnv  : empty
            , tyAliasEnv : empty
            , sortEnv    : empty
            , pos        : UnknownPos
            }

runTyping :: forall a. Typing a -> Ctx -> Either TypeError a
runTyping m ctx = runExcept $ runReaderT m ctx

lookupTmBind :: Name -> Typing C.Ty
lookupTmBind name = do
  env <- asks (_.tmBindEnv)
  case lookup name env of
    Just t -> pure t
    Nothing -> throwTypeError $ "term variable " <> show name <> " is undefined"

lookupTyBind :: Name -> Typing (Maybe C.Ty)
lookupTyBind name = lookup name <$> asks (_.tyBindEnv)

lookupTyAlias :: Name -> Typing (Maybe S.Ty)
lookupTyAlias name = lookup name <$> asks (_.tyAliasEnv)

lookupSort :: Name -> Typing (Maybe Name)
lookupSort name = lookup name <$> asks (_.sortEnv)

addToEnv :: forall a b. ((Map Name b -> Map Name b) -> Ctx -> Ctx) ->
                        Name -> b -> Typing a -> Typing a
addToEnv map name ty = if name == "_" then identity
                       else local (map (insert name ty))

addTmBind :: forall a. Name -> C.Ty -> Typing a -> Typing a
addTmBind = addToEnv \f r -> r { tmBindEnv = f r.tmBindEnv }

addTyBind :: forall a. Name -> C.Ty -> Typing a -> Typing a
addTyBind = addToEnv \f r -> r { tyBindEnv = f r.tyBindEnv }

addTyAlias :: forall a. Name -> S.Ty -> Typing a -> Typing a
addTyAlias = addToEnv \f r -> r { tyAliasEnv = f r.tyAliasEnv }

addSort :: forall a. Name -> Name -> Typing a -> Typing a
addSort = addToEnv \f r -> r { sortEnv = f r.sortEnv }

localPos :: forall a. (Pos -> Pos) -> Typing a -> Typing a
localPos f = local \r -> r { pos = f r.pos }

askPos :: Typing Pos
askPos = asks (_.pos)

data TypeError = TypeError String Pos

instance Show TypeError where
  show (TypeError msg UnknownPos) = msg
  show (TypeError msg (Pos pos expr inDoc)) =
    showPosition pos <> ": " <> msg <> "\nin the expression: " <>
    (if inDoc then S.showDoc else show) expr
    where
      showPosition :: Position -> String
      showPosition (Position { line: line, column: column }) =
        show line <> ":" <> show column

-- TODO: combine two type errors
instance Semigroup TypeError where
  append = const

throwTypeError :: forall a. String -> Typing a
throwTypeError msg = TypeError msg <$> askPos >>= throwError

type Checking = StateT REPLState (Except TypeError)

data Mode = SmallStep | StepTrace | BigStep | HOAS | Closure

derive instance Generic Mode _
instance Show Mode where show = genericShow

type TmBindings = List (Name /\ C.Ty /\ (C.Tm -> C.Tm))
type TyAliases = List (Name /\ S.Ty)

type REPLState =  { mode       :: Mode
                  , timing     :: Boolean
                  , tmBindings :: TmBindings
                  , tyAliases  :: TyAliases
                  , forbidDup  :: Boolean
                  }

initState :: REPLState
initState = { mode       : HOAS
            , timing     : false
            , tmBindings : Nil
            , tyAliases  : Nil
            , forbidDup  : true
            }

mergeStates :: REPLState -> REPLState -> Either (List Name) REPLState
mergeStates st1 st2 =
  let dupTms = st1.tmBindings >>= \(x /\ _ /\ _) ->
                 st2.tmBindings >>= \(y /\ _ /\ _) ->
                   if x == y then singleton x else Nil
      dupTys = st1.tyAliases >>= \(x /\ _) ->
                 st2.tyAliases >>= \(y /\ _) ->
                   if x == y then singleton x else Nil in
  if null dupTms && null dupTys
  then Right $ initState { tmBindings = st1.tmBindings <> st2.tmBindings
                         , tyAliases = st1.tyAliases <> st2.tyAliases
                         }
  else Left $ dupTms <> dupTys

runChecking :: forall a. Checking a -> REPLState -> Either TypeError (a /\ REPLState)
runChecking m st = runExcept $ runStateT m st

clearEnv :: REPLState -> REPLState
clearEnv st = st { tmBindings = Nil, tyAliases = Nil }

fromState :: REPLState -> Ctx
fromState b = { tmBindEnv  : fromFoldable $ rmap fst <$> b.tmBindings
              , tyAliasEnv : fromFoldable b.tyAliases
              , tyBindEnv  : empty
              , sortEnv    : empty
              , pos        : UnknownPos
              }

throwCheckError :: forall a. String -> Checking a
throwCheckError msg = throwError $ TypeError msg UnknownPos
