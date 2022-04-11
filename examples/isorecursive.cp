--> true

type ExpSig<Exp> = {
  Lit: Int -> Exp;
  Add: Exp -> Exp -> Exp;
};

typerec Exp = {
  eval: Int;
  dbl:  Exp;
  eq:   Exp -> Bool;
};

exp = trait [self: ExpSig<Exp>] implements ExpSig<Exp> => {
  Lit n = trait => {
    eval  = n;
    dbl   = Lit (n * 2);
    eq e' = e'.eval == n;
  };
  Add e1 e2 = trait => {
    eval  = e1.eval + e2.eval;
    dbl   = Add e1.dbl e2.dbl;
    eq e' = e'.eval == e1.eval + e2.eval;
  };
};

repo Exp = trait [self: ExpSig<Exp>] => {
  seven = Lit 7;
  seven' = Add (Lit 3) (Lit 4);
};

e = new repo @Exp , exp;
e.seven.dbl.eq e.seven'.dbl
