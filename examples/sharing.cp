--> 2097152

type ExpSig<Exp> = {
  Lit : Int -> Exp;
  Add : Exp -> Exp -> Exp;
};

type Eval = { eval : Int };
eval = trait implements ExpSig<Eval> => {
  (Lit     n).eval = n;
  (Add e1 e2).eval = e1.eval + e2.eval;
};

type Dble Exp = { dble : Exp };
dble Exp = trait [self : ExpSig<Exp>] implements ExpSig<Dble Exp> => {
  (Lit     n).dble = Lit (n*2);
  (Add e1 e2).dble = Add e1.dble e2.dble;
};

exp Exp = trait [self : ExpSig<Exp>] => {
  test = letrec tree (n:Int) : Exp =
    if n == 0 then Lit 1
    else let shared = tree (n-1) in Add shared shared
  in tree 20;
};

e = new exp @(Eval & Dble Eval) , eval , dble @Eval;
e.test.dble.eval
