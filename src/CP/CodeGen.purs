module Language.CP.CodeGen where

import Prelude

import Control.Monad.Except (Except, runExcept)
import Control.Monad.State (StateT, evalStateT, modify)
import Data.Either (Either)
import Data.String (Pattern(..), Replacement(..), replaceAll)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.RcdIR (Tm)
import Language.CP.Util ((<+>))
import Language.JS.AST (JS(..))
import Partial.Unsafe (unsafeCrashWith)

type CodeGen = StateT Int (Except String)

type AST = Array JS

runCodeGen :: Tm -> Either String AST
runCodeGen e = do
  ast /\ _ <- runExcept $ evalStateT (codegen e DstNil) 0
  pure $ [ JSRawCode prelude ] <> ast

prelude :: String
prelude = """function copyProp(dst, src, prop) {
    var getter = src.__lookupGetter__(prop);
    if (getter) dst.__defineGetter__(prop, getter);
    else dst[prop] = src[prop];
}
function copyObj(dst, src) {
    for (const prop in src) copyProp(dst, src, prop);
}
function primitive(tt) {
    var pt = ['int', 'double', 'string', 'bool'];
    if (tt.length === 1 && pt.includes(tt[0])) return tt[0];
    else return null;
}
function toIndex(tt) {
    var ts = tt.sort().filter((t, i) => t === 0 || t !== tt[i-1]);
    if (ts.length === 1) return ts[0];
    else return '(' + ts.join('&') + ')';
}"""

data Destination = DstNil | DstOpt Name | DstVar Name

codegen :: Tm -> Destination -> CodeGen (AST /\ Name)
-- TODO: compile RcdIRs to JavaScript; no need for types hopefully
codegen e = unsafeCrashWith $ "CP.CodeGen.codegen:" <+> show e

freshVarName :: CodeGen Name
freshVarName = do
  count <- modify (_ + 1)
  pure $ variable $ show count

variable :: Name -> Name
variable = ("$" <> _) <<< replaceAll (Pattern "'") (Replacement "$prime")
