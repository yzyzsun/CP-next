module Zord.Context where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Data.Either (Either)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), lookup)
import Text.Parsing.Parser.Pos (Position)
import Zord.Syntax.Common (Name, (<+>))
import Zord.Syntax.Core as C
import Zord.Syntax.Source as S

type Ctx = { tmBindEnv :: Env C.Ty -- typing
           , tyBindEnv :: Env C.Ty -- disjointness
           , tyAliasEnv :: Env S.Ty -- synonym
           , sortEnv :: Env Name -- distinguishing
           , pos :: Pos
           }

type Env a = List (Tuple Name a)

data Pos = UnknownPos
         | Pos Position S.Tm

type Typing = ReaderT Ctx (Except TypeError)

runTyping :: forall a. Typing a -> Either TypeError a
runTyping m = runExcept $ runReaderT m { tmBindEnv : Nil
                                       , tyBindEnv : Nil
                                       , tyAliasEnv : Nil
                                       , sortEnv : Nil
                                       , pos : UnknownPos
                                       }

lookupTmBind :: Name -> Typing C.Ty
lookupTmBind name = do
  env <- asks (_.tmBindEnv)
  case lookup name env of
    Just t -> pure t
    Nothing -> throwTypeError $ "term variable" <+> show name <+> "is undefined"

lookupTyBind :: Name -> Typing (Maybe C.Ty)
lookupTyBind name = lookup name <$> asks (_.tyBindEnv)

lookupTyAlias :: Name -> Typing (Maybe S.Ty)
lookupTyAlias name = lookup name <$> asks (_.tyAliasEnv)

lookupSort :: Name -> Typing (Maybe Name)
lookupSort name = lookup name <$> asks (_.sortEnv)

addToEnv :: forall a b. ((Env b -> Env b) -> Ctx -> Ctx) ->
                        Name -> b -> Typing a -> Typing a
addToEnv map name ty = local (map (Tuple name ty : _))

addTmBind :: forall a. Name -> C.Ty -> Typing a -> Typing a
addTmBind = addToEnv \f r -> r { tmBindEnv = f r.tmBindEnv }

addTyBind :: forall a. Name -> C.Ty -> Typing a -> Typing a
addTyBind = addToEnv \f r -> r { tyBindEnv = f r.tyBindEnv }

addTyAlias :: forall a. Name -> S.Ty -> Typing a -> Typing a
addTyAlias = addToEnv \f r -> r { tyAliasEnv = f r.tyAliasEnv }

addSort :: forall a. Name -> Typing a -> Typing a
addSort name = addToEnv (\f r -> r { sortEnv = f r.sortEnv }) name ("#" <> name)

setPos :: forall a. Pos -> Typing a -> Typing a
setPos p = local (_ { pos = p })

getPos :: Typing Pos
getPos = asks (_.pos)

data TypeError = TypeError String Pos

throwTypeError :: forall a. String -> Typing a
throwTypeError msg = TypeError msg <$> getPos >>= throwError
