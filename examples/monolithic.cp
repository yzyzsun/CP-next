--> 46

type Mono = {
  eval : Int;
  plus : Int -> Int;
  print : String;
};

type LitSig<Exp> = {
  IntLit : Int -> Exp;
  StrLit : String -> Exp;
};

eval = trait implements LitSig<Mono> => {
  (IntLit n).eval = n;
  (IntLit n).print = toString n;
  (StrLit s).print = s;
  _.eval = 0;
  [self:Mono].plus m = self.eval + m;
};

lit Exp = trait [self : LitSig<Exp>] => {
  int = new IntLit 48;
  str = new StrLit "HKG";
};

l = new eval , lit @Mono;
l.int.plus (-2)
