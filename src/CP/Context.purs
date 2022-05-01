module Language.CP.Context where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Data.Either (Either)
import Data.Map (Map, empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source as S
import Parsing (Position)

type Typing = ReaderT Ctx (Except TypeError)

type Ctx = { tmBindEnv  :: Map Name C.Ty -- typing
           , tyBindEnv  :: Map Name C.Ty -- disjointness
           , tyAliasEnv :: Map Name S.Ty -- synonym
           , sortEnv    :: Map Name Name -- distinguishing
           , pos :: Pos
           }

data Pos = UnknownPos
         | Pos Position S.Tm Boolean

runTyping :: forall a. Typing a -> Either TypeError a
runTyping m = runExcept $ runReaderT m { tmBindEnv : empty
                                       , tyBindEnv : empty
                                       , tyAliasEnv : empty
                                       , sortEnv : empty
                                       , pos : UnknownPos
                                       }

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
                       else local (map \env -> insert name ty env)

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

-- TODO: combine two type errors
instance Semigroup TypeError where
  append = const

throwTypeError :: forall a. String -> Typing a
throwTypeError msg = TypeError msg <$> askPos >>= throwError
