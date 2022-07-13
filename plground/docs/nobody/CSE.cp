{- Infrastructure -}

type Pair A B = { fst : A; snd : B };

type MaybeSig<M> A = {
  Nothing : M;
  Just : A -> M;
};

type Maybe A = { maybe : forall B. B -> (A -> B) -> B };

maybe A = trait implements MaybeSig<Maybe A> A => {
  (Nothing).maybe = /\ B. \ y f -> y;
  (Just  x).maybe = /\ B. \ y f -> f x;
};

{- DAG nodes -}

type NodeId = Int;

type NodeSig<Node> = {
  NVar : String -> Node;
  NLit : Int -> Node;
  NAdd : NodeId -> NodeId -> Node;
};

interface Node {
  eq : Node -> Bool;
  eqNVar : String -> Bool;
  eqNLit : Int -> Bool;
  eqNAdd : NodeId -> NodeId -> Bool;
  print : String;
};

node = trait implements NodeSig<Node> => {
  NVar s = trait => {
    eq node = node.eqNVar s;
    eqNVar s' = s' == s;
    eqNLit _ = false;
    eqNAdd _ _ = false;
    print = s;
  };
  NLit n = trait => {
    eq node = node.eqNLit n;
    eqNLit n' = n' == n;
    eqNVar _ = false;
    eqNAdd _ _ = false;
    print = toString n;
  };
  NAdd e1 e2 = trait => {
    eq node = node.eqNAdd e1 e2;
    eqNAdd e1' e2' = e1' == e1 && e2' == e2;
    eqNVar _ = false;
    eqNLit _ = false;
    print = "v" ++ toString e1 ++ " + v" ++ toString e2;
  };
};

{- DAG helpers -}

lookup (e:Node) (m:[Node]) =
  letrec lookup' (i:Int) : Maybe Int = open new maybe @Int in
    if i == #m then Nothing
    else if e.eq (m!!i) then Just i else lookup' (i+1)
  in lookup' 0;

hashcons (e:Node) (m:[Node]) =
  (lookup e m).maybe @(Pair NodeId [Node])
    { fst = #m; snd = m ++ [e] }
    (\(i:NodeId) -> { fst = i; snd = m });

print (p : Pair NodeId [Node]) =
  letrec print' (i:Int) : String =
    let root = p.fst in let m = p.snd in
    if i == #m then ""
    else if i == root then (m!!i).print
    else "let v" ++ toString i ++ " = " ++ (m!!i).print ++
         " in " ++ print' (i+1)
  in print' 0;

{- Hash-consing -}

type ExpSig<Exp> = {
  Var : String -> Exp;
  Lit : Int -> Exp;
  Add : Exp -> Exp -> Exp;
};

type HashCons = { hc : [Node] -> Pair NodeId [Node] };

hc = trait [self : NodeSig<Node>] implements ExpSig<HashCons> => {
  (Var s).hc m = hashcons (NVar s) m;
  (Lit n).hc m = hashcons (NLit n) m;
  (Add e1 e2).hc m = let p1 = e1.hc m in
                     let p2 = e2.hc p1.snd in
                     hashcons (NAdd p1.fst p2.fst) p2.snd;
};

{- Example -}

repo Exp = trait [self : ExpSig<Exp>] => {
  mul4 = Add (Add (Var "x") (Var "x")) (Add (Var "x") (Var "x"));
};

e = new node , hc , repo @HashCons;
print (e.mul4.hc [])