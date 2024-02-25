--> 81

type Env T = String -> T;
type EnvN = Env Int;
type Func = Int -> Int;
type EnvF = Env Func;

empty T = \(_ : String) -> undefined : T;
lookup T (s : String) (env : Env T) = env s;
insert T (s : String) (v : T) (env : Env T) =
  \(s': String) -> if s == s' then v else lookup @T s' env;

type Eval Context = { eval : Context -> Int };
type CtxN = { envN : EnvN };
type CtxF = { envF : EnvF };

type ExpSig<Exp> = {
  Lit : Int -> Exp;
  Add : Exp -> Exp -> Exp;
};
evalNum Context = trait implements ExpSig<Eval Context> => {
  (Lit     n).eval ctx = n;
  (Add e1 e2).eval ctx = e1.eval ctx + e2.eval ctx;
};

type VarSig<Exp> = {
  Let : String -> Exp -> Exp -> Exp;
  Var : String -> Exp;
};
evalVar (Context * CtxN) = trait implements VarSig<Eval (CtxN&Context)> => {
  (Let s e1 e2).eval ctx =
    e2.eval { ctx with envN = insert @Int s (e1.eval ctx) ctx.envN };
  (Var       s).eval ctx = lookup @Int s ctx.envN;
};

type FuncSig<Exp> = {
  LetF : String -> Func -> Exp -> Exp;
  AppF : String -> Exp -> Exp;
};
evalFunc (Context * CtxF) = trait implements FuncSig<Eval (CtxF&Context)> => {
  (LetF s f e).eval ctx =
    e.eval { ctx with envF = insert @Func s f ctx.envF };
  (AppF  s  e).eval ctx = (lookup @Func s ctx.envF) (e.eval ctx);
};

expPoly Exp = trait [self : ExpSig<Exp> & VarSig<Exp> & FuncSig<Exp>] => {
  exp = open self in
        LetF "f" (\(x:Int) -> x * x)
             (Let "x" (Lit 9) (AppF "f" (Var "x")));
};

e = new evalNum @(CtxN&CtxF) , evalVar @CtxF , evalFunc @CtxN ,
        expPoly @(Eval (CtxN&CtxF));
e.exp.eval { envN = empty @Int; envF = empty @Func }
