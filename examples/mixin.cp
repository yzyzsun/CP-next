--> "48 + -(2) = 46"

type AddSig<Exp> = {
  Lit: Int -> Exp;
  Add: Exp -> Exp -> Exp;
};

type Eval = { eval: Int };

familyEval =
  trait implements AddSig<Eval> => {
    (Lit   n).eval = n;
    (Add l r).eval = l.eval + r.eval;
  };

type Print = { print: String };

familyPrint =
  trait implements AddSig<Print> => {
    (Lit   n).print = toString n;
    (Add l r).print = l.print ++ " + "
                   ++ r.print;
  };

type NegSig<Exp> = { Neg: Exp -> Exp };

-- mixin-style dynamic inheritance
familyNeg (TBase * NegSig<Eval&Print>) (base: Trait<TBase>) =
  trait [this: TBase] implements NegSig<Eval&Print> inherits base => {
    (Neg e).eval  = -e.eval;
    (Neg e).print = "-(" ++ e.print ++ ")";
  };

fam = new familyNeg @AddSig<Eval&Print> (familyEval,familyPrint)
    : AddSig<Eval&Print> & NegSig<Eval&Print>;

e = new fam.Add (new fam.Lit 48) (new fam.Neg (new fam.Lit 2));
e.print ++ " = " ++ toString e.eval
