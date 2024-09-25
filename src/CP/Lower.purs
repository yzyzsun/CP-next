module Language.CP.Lower where

import Prelude

import Control.Monad.Except (Except, runExcept)
import Control.Monad.Reader (ReaderT, runReaderT)
import Data.Bifunctor (rmap)
import Data.Either (Either)
import Data.Map (Map, empty, fromFoldable)
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\))
import Language.CP.Context (REPLState)
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.RcdIR as R
import Language.CP.Util ((<+>))
import Partial.Unsafe (unsafeCrashWith)

type Lowering = ReaderT Ctx (Except String)

type Ctx = { tmBindEnv :: Map Name C.Ty
           , tyBindEnv :: Map Name C.Ty
           , inTrait   :: Boolean
           }

emptyCtx :: Ctx
emptyCtx = { tmBindEnv: empty
           , tyBindEnv: empty
           , inTrait: false
           }

fromState :: REPLState -> Ctx
fromState st = emptyCtx { tmBindEnv = fromFoldable $ rmap fst <$> st.tmBindings }

runLowering :: C.Tm -> Ctx -> Either String (R.Tm /\ R.Ty)
runLowering e ctx = runExcept $ runReaderT (infer e) ctx

infer :: C.Tm -> Lowering (R.Tm /\ R.Ty)
-- TODO: all core terms should be lowered to some forms of records
--       e.g. 42 ~~> { "int": 42 }
infer e = unsafeCrashWith $ "CP.Lower.infer:" <+> show e
