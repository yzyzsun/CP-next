module Zord.Context where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Data.Either (Either)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), lookup)
import Text.Parsing.Parser.Pos (Position)
import Zord.Syntax.Core (Expr, Name, Ty(..), (<+>))

type Ctx = { ctx :: Mapping
           , pos :: Pos
           }

type Mapping = List (Tuple Name Binding)

data Binding = TmBind Ty -- typing
             | TyBind Ty -- disjointness

data Pos = UnknownPos
         | Pos Position Expr

type Typing = ReaderT Ctx (Except TypeError)

runTyping :: forall a. Typing a -> Either TypeError a
runTyping m = runExcept $ runReaderT m { ctx : Nil, pos : UnknownPos }

lookupBinding :: Name -> Typing Binding
lookupBinding name = do
  ctx <- asks (_.ctx)
  case lookup name ctx of
    Just binding -> pure binding
    Nothing -> throwTypeError $ "variable" <+> show name <+> "is not defined"

lookupTmBind :: Name -> Typing Ty
lookupTmBind x = do
  binding <- lookupBinding x
  case binding of
    TmBind t -> pure t
    _  -> throwTypeError $ "variable" <+> show x <+> "is not a term"

lookupTyBind :: Name -> Typing Ty
lookupTyBind a = do
  binding <- lookupBinding a
  case binding of
    TyBind t -> pure t
    _  -> throwTypeError $ "variable" <+> show a <+> "is not a type"

mapCtx :: (Mapping -> Mapping) -> Ctx -> Ctx
mapCtx f r = r { ctx = f r.ctx }

addBinding :: forall a. Name -> Binding -> Typing a -> Typing a
addBinding name binding = local (mapCtx (Tuple name binding : _))

addTmBind :: forall a. Name -> Ty -> Typing a -> Typing a
addTmBind x t = addBinding x (TmBind t)

addTyBind :: forall a. Name -> Ty -> Typing a -> Typing a
addTyBind a t = addBinding a (TyBind t)

emptyCtx :: forall a. Typing a -> Typing a
emptyCtx = local (mapCtx (const Nil))

openRecInCtx :: forall a. Ty -> Typing a -> Typing a
openRecInCtx r m = do
  ctx <- open r
  local (mapCtx (ctx <> _)) m
  where open :: Ty -> Typing Mapping
        open (TyRec l t) = pure $ Tuple l (TmBind t) : Nil
        open (TyAnd t1 t2) = do ctx1 <- open t1
                                ctx2 <- open t2
                                pure $ ctx1 <> ctx2
        open t = throwTypeError $ show t <+> "cannot be opened"

setPos :: forall a. Pos -> Typing a -> Typing a
setPos p = local (_ { pos = p })

getPos :: Typing Pos
getPos = asks (_.pos)

data TypeError = TypeError String Pos

throwTypeError :: forall a. String -> Typing a
throwTypeError msg = TypeError msg <$> getPos >>= throwError
