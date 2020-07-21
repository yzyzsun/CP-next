module Zord.Context where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.Reader (ReaderT, ask, lift, local, runReaderT)
import Data.Either (Either)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), lookup)
import Zord.Syntax (Name, Ty(..))

type Ctx = List (Tuple Name Binding)

data Binding = TmBind Ty -- typing
             | TyBind Ty -- disjointness

type Typing = ReaderT Ctx (Except TypeError)

runTyping :: forall a. Typing a -> Either TypeError a
runTyping m = runExcept $ runReaderT m Nil

lookupBinding :: Name -> Typing Binding
lookupBinding name = do
  ctx <- ask
  case lookup name ctx of
    Just binding -> pure binding
    Nothing -> throwTypeError $ "Variable " <> show name <> " is not defined"

lookupTmBind :: Name -> Typing Ty
lookupTmBind x = do
  binding <- lookupBinding x
  case binding of
    TmBind t -> pure t
    _  -> throwTypeError $ "Variable " <> show x <> " is not a term"

lookupTyBind :: Name -> Typing Ty
lookupTyBind a = do
  binding <- lookupBinding a
  case binding of
    TyBind t -> pure t
    _  -> throwTypeError $ "Variable " <> show a <> " is not a type"

addBinding :: forall a. Name -> Binding -> Typing a -> Typing a
addBinding name binding = local (Tuple name binding : _)

addTmBind :: forall a. Name -> Ty -> Typing a -> Typing a
addTmBind x t = addBinding x (TmBind t)

addTyBind :: forall a. Name -> Ty -> Typing a -> Typing a
addTyBind a t = addBinding a (TyBind t)

emptyCtx :: forall a. Typing a -> Typing a
emptyCtx = local (const Nil)

openRecInCtx :: forall a. Ty -> Typing a -> Typing a
openRecInCtx r m = do
  ctx <- lift $ open r
  local (ctx <> _) m
  where open :: Ty -> Except TypeError Ctx
        open (TyRec l t) = pure $ Tuple l (TmBind t) : Nil
        open (TyAnd t1 t2) = do ctx1 <- open t1
                                ctx2 <- open t2
                                pure $ ctx1 <> ctx2
        open t = throwTypeError $ show t <> " cannot be opened"

data TypeError = TypeError String

instance showTypeError :: Show TypeError where
  show (TypeError str) = "TypeError: " <> str

throwTypeError :: forall a m. MonadThrow TypeError m => String -> m a
throwTypeError = throwError <<< TypeError
