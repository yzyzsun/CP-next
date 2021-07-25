--> true

type Exp = mu Exp. {
  eval: Int;
  dbl: Exp;
  eq: Exp -> Bool;
};

eval' (e: Exp) = (unfold @Exp e).eval;
dbl' (e: Exp) = (unfold @Exp e).dbl;
eq' (e1: Exp) (e2: Exp) = (unfold @Exp e1).eq e2;

lit (n: Int) : Exp = fold @Exp {
  eval = n;
  dbl = lit (n * 2);
  eq (e': Exp) = eval' e' == n;
};

add (e1: Exp) (e2: Exp) : Exp = fold @Exp {
  eval = eval' e1 + eval' e2;
  dbl = add (dbl' e1) (dbl' e2);
  eq (e': Exp) = eval' e' == eval' e1 + eval' e2;
};

e1 = lit 7;
e2 = add (lit 3) (lit 4);
eq' (dbl' e1) (dbl' e2)
