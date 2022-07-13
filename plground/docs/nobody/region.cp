pow (b:Double) (n:Int) : Double =
  if n == 0 then 1.0
  else if n > 0 then pow b (n-1) * b
  else pow b (n+1) / b;

type Vector = { x : Double; y : Double };

type HudakSig<Region> = {
  Circle    : Double -> Region;
  Outside   : Region -> Region;
  Union     : Region -> Region -> Region;
  Intersect : Region -> Region -> Region;
  Translate : Vector -> Region -> Region;
};

type Size = { size : Int };
sz = trait implements HudakSig<Size> => {
  (Circle      _).size = 1;
  (Outside     a).size = a.size + 1;
  (Union     a b).size = a.size + b.size + 1;
  (Intersect a b).size = a.size + b.size + 1;
  (Translate _ a).size = a.size + 1;
};

type Text = { text : String };
txt = trait implements HudakSig<Size => Text> => {
         (Circle      r).text = "a circular region of radius " ++ toString r;
         (Outside     a).text = "outside a region of size " ++ toString a.size;
  [self]@(Union     _ _).text = "the union of two regions of size " ++ toString self.size ++ " in total";
  [self]@(Intersect _ _).text = "the intersection of two regions of size " ++ toString self.size ++ " in total";
  [self]@(Translate _ _).text = "a translated region of size " ++ toString self.size;
};

type HoferSig<Region> = {
  Univ  : Region;
  Empty : Region;
  Scale : Vector -> Region -> Region;
};

sz' = trait implements HoferSig<Size> => {
  (Univ     ).size = 1;
  (Empty    ).size = 1;
  (Scale _ a).size = a.size + 1;
};

txt' = trait implements HoferSig<Size => Text> => {
              (Univ).text = "the universal region";
             (Empty).text = "the empty region";
  [self]@(Scale _ _).text = "a scaled region of size " ++ toString self.size;
};

type RegionSig<Region> = HudakSig<Region> & HoferSig<Region>;

type Eval = { contains : Vector -> Bool };
eval = trait implements RegionSig<Eval> => {
  (Circle         r).contains p = pow p.x 2 + pow p.y 2 <= pow r 2;
  (Outside        a).contains p = !(a.contains p);
  (Union        a b).contains p = a.contains p || b.contains p;
  (Intersect    a b).contains p = a.contains p && b.contains p;
  (Translate {..} a).contains p = a.contains { x = p.x - x; y = p.y - y };
  (Univ            ).contains _ = true;
  (Empty           ).contains _ = false;
  (Scale     {..} a).contains p = a.contains { x = p.x / x; y = p.y / y };
};

type IsUniv  = { isUniv  : Bool };
type IsEmpty = { isEmpty : Bool };

chkUniv = trait implements RegionSig<IsEmpty => IsUniv> => {
  (Univ         ).isUniv = true;
  (Outside     a).isUniv = a.isEmpty;
  (Union     a b).isUniv = a.isUniv || b.isUniv;
  (Intersect a b).isUniv = a.isUniv && b.isUniv;
  (Translate _ a).isUniv = a.isUniv;
  (Scale     _ a).isUniv = a.isUniv;
                _.isUniv = false;
};

chkEmpty = trait implements RegionSig<IsUniv => IsEmpty> => {
  (Empty        ).isEmpty = true;
  (Outside     a).isEmpty = a.isUniv;
  (Union     a b).isEmpty = a.isEmpty && b.isEmpty;
  (Intersect a b).isEmpty = a.isEmpty || b.isEmpty;
  (Translate _ a).isEmpty = a.isEmpty;
  (Scale     _ a).isEmpty = a.isEmpty;
                _.isEmpty = false;
};

type Simplify Region = { simplify : Region };
simp Region = trait [fself : RegionSig<Region>]
             implements RegionSig<IsUniv&IsEmpty&Region => Simplify Region> => {
  [self].simplify = if self.isUniv then Univ
                    else if self.isEmpty then Empty
                    else self
};

type Eliminate Region = { eliminate : Region; delOutside : Region };
elim Region = trait [fself : RegionSig<Region>]
              implements RegionSig<Region => Eliminate Region> => {
  (Outside     a).eliminate = a.delOutside;
  (Union     a b).eliminate = Union a.eliminate b.eliminate;
  (Intersect a b).eliminate = Intersect a.eliminate b.eliminate;
  (Translate v a).eliminate = Translate v a.eliminate;
  (Scale     v a).eliminate = Scale v a.eliminate;
           [self].eliminate = self;

  -- delegated method patterns:
  (Outside a).delOutside = a.eliminate;
       [self].delOutside = Outside self.eliminate;
};

sharing Region = trait [self : RegionSig<Region>] => {
  circles = letrec go (n:Int) (offset:Double) : Region =
              if n == 0 then Outside (Outside (Circle 1.0))
              else let shared = go (n-1) (offset/2.0)
                   in Union (Translate { x = -offset; y = 0.0 } shared)
                            (Translate { x =  offset; y = 0.0 } shared)
            in let n = 20 in go n (pow 2.0 (n-2));
};

test = new sharing @(Size & Eliminate Size) , sz , sz' , elim @Size;
output1 = "(1) the example of sharing has a size of " ++ toString test.circles.size ++ " before transformation.";
output2 = "(2) the example of sharing has a size of " ++ toString test.circles.eliminate.size ++ " after transformation.";

repo Region = trait [self : RegionSig<Region>] => {
  annulus = Intersect (Outside (Circle 4.0)) (Circle 8.0);
  ellipse = Scale { x = 4.0; y = 8.0 } (Circle 1.0);
  universal = Union (Outside Empty) (Circle 1.0);
};

shapes = new repo @(Eval & Size & Text & IsUniv & IsEmpty & Simplify (Eval & Size & Text)) ,
             eval , sz , sz' , txt , txt' , chkUniv , chkEmpty , simp @(Eval & Size & Text);
output3 = "(3) " ++ shapes.universal.text ++ (if shapes.universal.simplify.contains { x = 0.0; y = 0.0 } then " contains " else " does not contain ") ++ "the origin and can be simplified to " ++ shapes.universal.simplify.text ++ ".";

output1 ++ "<br>" ++ output2 ++ "<br>" ++ output3