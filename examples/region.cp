--> "the universal region contains the origin"

type Vector = { x : Double; y : Double };

pow (b:Double) (n:Int) : Double =
  if n == 0 then 1.0
  else if n > 0 then pow b (n-1) * b
  else pow b (n+1) / b;

type HudakSig<Region> = {
  Circle    : Double -> Region;
  Outside   : Region -> Region;
  Union     : Region -> Region -> Region;
  Intersect : Region -> Region -> Region;
  Translate : Vector -> Region -> Region;
};

type Print = { text : String };
print = trait implements HudakSig<Print> => {
  (Circle         r).text = "a circle of radius " ++ toString r;
  (Outside        a).text = "outside " ++ a.text;
  (Union        a b).text = "the union of " ++ a.text ++ " and " ++ b.text;
  (Intersect    a b).text = "the intersection of " ++ a.text ++ " and " ++ b.text;
  (Translate {..} a).text = "a region translating " ++ a.text ++
                            " by (" ++ toString x ++ "," ++ toString y ++ ")";
};

type Eval = { contains : Vector -> Bool };
eval = trait implements HudakSig<Eval> => {
  (Circle         r).contains p = pow p.x 2 + pow p.y 2 <= pow r 2;
  (Outside        a).contains p = !(a.contains p);
  (Union        a b).contains p = a.contains p || b.contains p;
  (Intersect    a b).contains p = a.contains p && b.contains p;
  (Translate {..} a).contains p = a.contains {x = p.x - x; y = p.y - y};
};

type HoferSig<Region> = {
  Univ  : Region;
  Empty : Region;
  Scale : Vector -> Region -> Region;
};

print' = trait implements HoferSig<Print> => {
  (Univ        ).text = "the universal region";
  (Empty       ).text = "the empty region";
  (Scale {..} a).text = "a region scaling " ++ a.text ++
                        " by (" ++ toString x ++ "," ++ toString y ++ ")";
};

eval' = trait implements HoferSig<Eval> => {
  (Univ        ).contains _ = true;
  (Empty       ).contains _ = false;
  (Scale {..} a).contains p = a.contains {x = p.x / x; y = p.y / y};
};

type RegionSig<Region> = HudakSig<Region> & HoferSig<Region>;

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

type Opt Region = { optimized : Region };
opt Region = trait [fself : RegionSig<Region>]
             implements RegionSig<IsUniv&IsEmpty&Region => Opt Region> => {
  [self].optimized = if self.isUniv then Univ
                     else if self.isEmpty then Empty
                     else self
};

repo Region = trait [self : RegionSig<Region>] => {
  annulus = Intersect (Outside (Circle 4.0)) (Circle 8.0);
  ellipse = Scale {x = 4.0; y = 8.0} (Circle 1.0);
  universal = Union (Outside Empty) (Circle 1.0);
  circles = letrec recur (n:Int) (offset:Double) : Region =
              if n == 0 then Circle 1.0
              else let shared = recur (n-1) (offset/2.0)
                   in Union (Translate {x = -offset; y = 0.0} shared)
                            (Translate {x =  offset; y = 0.0} shared)
            in let n = 20 in recur n (pow 2.0 (n-2));
};

shapes = new repo @(Eval & Print & IsUniv & IsEmpty & Opt (Eval&Print)) ,
             eval , eval' , print , print' , chkUniv , chkEmpty , opt @(Eval&Print);
optimized = shapes.universal.optimized;
optimized.text ++ (if optimized.contains {x = 0.0; y = 0.0}
  then " contains " else " does not contain ") ++ "the origin"
