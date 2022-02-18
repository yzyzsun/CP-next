--> "(({2}+{3})+({5}+{6}))"

type ExpSig<Exp> = {
  Lit : Int -> Exp;
  Add : Exp -> Exp -> Exp;
};

type Cnt = { cnt : Int };

expCnt = trait implements ExpSig<Cnt> => {
  (Lit     n).cnt = 1;
  (Add e1 e2).cnt = e1.cnt + e2.cnt + 1;
};

type Pos = { pos : Int };
type InhPos = { pos1 : Pos -> Int; pos2 : Pos -> Cnt -> Int };
type PrintPos Ctx = { print : Pos&Ctx -> String };

printPos (Ctx * Pos) = trait [self : InhPos] implements ExpSig<Cnt => PrintPos Ctx> => {
  (Lit     n).print inh = "{" ++ toString inh.pos ++ "}";
  (Add e1 e2).print inh =
    "(" ++ e1.print { inh with pos = pos1 inh } ++ "+" ++
           e2.print { inh with pos = pos2 inh e1 } ++ ")";
  pos1 (e0:Pos) = e0.pos + 1;
  pos2 (e0:Pos) (e1:Cnt) = e0.pos + e1.cnt + 1;
};

expPoly Exp = trait [self : ExpSig<Exp>] => {
  exp = Add (Add (Lit 1) (Lit 2)) (Add (Lit 3) (Lit 4));
};

e = new expCnt , printPos @Top , expPoly @(Cnt & PrintPos Top);
e.exp.print { pos = 0 }
