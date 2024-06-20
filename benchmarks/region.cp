not (x:Bool) = if x then false else true;

pow (b:Double) (n:Int) : Double =
  if n == 0 then 1.0
  else if n > 0 then pow b (n-1) * b
  else pow b (n+1) / b;

pair (s1:String) (s2:String) = "(" ++ s1 ++ ", " ++ s2 ++ ")";

type Vector = { x : Double; y : Double };
pv (v:Vector) = pair (toString v.x) (toString v.y);

type HudakSig<Region> = {
  Circle    : Double -> Region;
  Outside   : Region -> Region;
  Union     : Region -> Region -> Region;
  Intersect : Region -> Region -> Region;
  Translate : Vector -> Region -> Region;
};

type Text = { text : String };
txt = trait implements HudakSig<Text> => {
  (Circle      r).text = "○(" ++ toString r ++ ")";
  (Outside     a).text = "∁(" ++ a.text ++ ")";
  (Union     a b).text = "∪" ++ pair a.text b.text;
  (Intersect a b).text = "∩" ++ pair a.text b.text;
  (Translate v a).text = "T" ++ pair (pv v) a.text;
};

type HoferSig<Region> = {
  Univ  : Region;
  Empty : Region;
  Scale : Vector -> Region -> Region;
};

txt' = trait implements HoferSig<Text> => {
  (Univ     ).text = "U";
  (Empty    ).text = "∅";
  (Scale v a).text = "S" ++ pair (pv v) a.text;
};

type RegionSig<Region> = HudakSig<Region> & HoferSig<Region>;

type Eval = { contains : Vector -> Bool };
eval = trait implements RegionSig<Eval> => {
  (Circle         r).contains p = pow p.x 2 + pow p.y 2 <= pow r 2;
  (Outside        a).contains p = not (a.contains p);
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
opt Region = trait [fself : RegionSig<Region>]
             implements RegionSig<IsUniv&IsEmpty&Region => Simplify Region> => {
  [self].simplify = if self.isUniv then new fself.Univ
                    else if self.isEmpty then new fself.Empty
                    else self
};

type Eliminate Region = { eliminate : Region; delOutside : Region };
opt' Region = trait [fself : RegionSig<Region>]
              implements RegionSig<Region => Eliminate Region> => {
  (Outside     a).eliminate = a.delOutside;
  (Union     a b).eliminate = new fself.Union a.eliminate b.eliminate;
  (Intersect a b).eliminate = new fself.Intersect a.eliminate b.eliminate;
  (Translate v a).eliminate = new fself.Translate v a.eliminate;
  (Scale     v a).eliminate = new fself.Scale v a.eliminate;
           [self].eliminate = self;

  (Outside a).delOutside = a.eliminate;
       [self].delOutside = new fself.Outside self.eliminate;
};

repo Region = trait [self : RegionSig<Region>] => {
  universal (n:Double) = open self in letrec universal' (i:Int) : Region =
                           if i == 0 then Univ else
                           Intersect (Union (Outside Empty) (Circle n)) (universal' (i-1))
                         in universal' 200;
};

shapes = new repo @(Eval & Text & IsUniv & IsEmpty & Simplify (Eval&Text)) ,
             eval , txt , txt' , chkUniv , chkEmpty , opt @(Eval&Text);
go (n:Double) : String = if n == 0.0 then "" else toString ((shapes.universal n).isUniv) ++ go (n - 1.0);
go 18.0
