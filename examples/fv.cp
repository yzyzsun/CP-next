--> "let x = 4 in let y = 8 in x + y is 12"

type Env = String -> Int;

empty = undefined;
lookup (s : String) (env : Env) = env s;
insert (s : String) (v : Int) (env : Env) =
  \(s': String) -> if s == s' then v else lookup s' env;

elem (s : String) (a : [String]) =
  letrec elem' (i : Int) : Bool =
    if i == #a then false
    else if a!!i == s then true
    else elem' (i+1)
  in elem' 0;

filter (p : String -> Bool) (a : [String]) =
  letrec filter' (i : Int) : [String] =
    if i == #a then []
    else (let x = a!!i in if p x then [x] else []) ++ filter' (i+1)
  in filter' 0;

union (a : [String]) (b : [String]) =
  a ++ filter (\(x : String) -> !(elem x a)) b;

delete (x : String) (a : [String]) = filter (\(y : String) -> y != x) a;

type NumSig<Exp> = {
  Lit : Int -> Exp;
  Add : Exp -> Exp -> Exp;
};

type Eval Ctx = { eval : Ctx -> Int };
evalNum Ctx = trait implements NumSig<Eval Ctx> => {
  (Lit     n).eval _   = n;
  (Add e1 e2).eval ctx = e1.eval ctx + e2.eval ctx;
};

type VarSig<Exp> = {
  Let : String -> Exp -> Exp -> Exp;
  Var : String -> Exp;
};

type Env = { env : String -> Int };
evalVar (Ctx * Env) = trait implements VarSig<Eval (Env&Ctx)> => {
  (Let s e1 e2).eval ctx = e2.eval { ctx | env = insert s (e1.eval ctx) ctx.env };
  (Var       s).eval ctx = lookup s ctx.env;
};

type ExpSig<Exp> = NumSig<Exp> & VarSig<Exp>;

type FV = { fv : [String] };
fv = trait implements ExpSig<FV> => {
  (Lit       n).fv = [];
  (Add   e1 e2).fv = union e1.fv e2.fv;
  (Let s e1 e2).fv = union e1.fv (delete s e2.fv);
  (Var       s).fv = [s];
};

eval' (Ctx * Env) = trait implements ExpSig<FV => Eval (Env&Ctx)> => {
  (Lit       n).eval _   = n;
  (Add   e1 e2).eval ctx = e1.eval ctx + e2.eval ctx;
  (Let s e1 e2).eval ctx = if elem s e2.fv
                           then e2.eval { ctx | env = insert s (e1.eval ctx) ctx.env }
                           else e2.eval ctx;
  (Var       s).eval ctx = lookup s ctx.env;
};

type Print = { print : String };
print = trait implements ExpSig<Print> => {
  (Lit       n).print = toString n;
  (Add   e1 e2).print = e1.print ++ " + " ++ e2.print;
  (Let s e1 e2).print = "let " ++ s ++ " = " ++ e1.print ++ " in " ++ e2.print;
  (Var       s).print = s;
};

repo Exp = trait [self : ExpSig<Exp>] => {
  num = Add (Lit 4) (Lit 8);
  var = Let "x" (Lit 4) (Let "y" (Lit 8) (Add (Var "x") (Var "y")));
};

exp = new repo @(Eval Env) , evalNum @Env , evalVar @Top;

exp' = new repo @(Eval Env & FV & Print) , eval' @Top , fv , print;
exp'.var.print ++ " is " ++ toString (exp'.var.eval { env = empty })
