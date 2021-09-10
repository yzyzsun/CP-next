--> "((4 + 8) * 4) is 48"

type Eval = { eval : Int };
type Print = { print : String };

type AddSig<Exp> = {
  Lit: Int -> Exp;
  Add: Exp -> Exp -> Exp;
};
evalAdd = trait implements AddSig<Eval> => {
  (Lit     n).eval = n;
  (Add e1 e2).eval = e1.eval + e2.eval;
};
printAdd = trait implements AddSig<Print> => {
  (Lit     n).print = toString n;
  (Add e1 e2).print = "(" ++ e1.print ++ " + " ++ e2.print ++ ")";
};
expAdd Exp = trait [self : AddSig<Exp>] => {
  exp = Add (Lit 4) (Lit 8);
};

type MulSig<Exp> = AddSig<Exp> & {
  Mul : Exp -> Exp -> Exp;
};
evalMul = trait implements MulSig<Eval> inherits evalAdd => {
  (Mul e1 e2).eval = e1.eval * e2.eval;
};
printMul = trait implements MulSig<Print> inherits printAdd => {
  (Mul e1 e2).print = "(" ++ e1.print ++ " * " ++ e2.print ++ ")";
};
expMul Exp = trait [self : MulSig<Exp>] inherits expAdd @Exp => {
  override exp = Mul super.exp (Lit 4);
};

e = new evalMul , printMul , expMul @(Eval & Print);
e.exp.print ++ " is " ++ toString e.exp.eval
