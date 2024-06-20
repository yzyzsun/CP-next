type RegionSig<Region> = {
  Circle    : Double -> Region;
  Outside   : Region -> Region;
  Union     : Region -> Region -> Region;
  Intersect : Region -> Region -> Region;
  Univ      : Region;
  Empty     : Region;
};

repo Region = trait [self : RegionSig<Region>] => {
  universal (n:Double) = open self in letrec universal' (i:Int) : Region =
                           if i == 0 then Univ else
                           Intersect (Union (Outside Empty) (Circle n)) (universal' (i-1))
                         in universal' 200;
};
type UE = {
  isUniv  : Top -> Bool;
  isEmpty : Top -> Bool;
};
ue = trait implements RegionSig<UE> => {
  (Univ         ).isUniv (_:Top) = true;
  (Outside     a).isUniv (_:Top) = a.isEmpty ();
  (Union     a b).isUniv (_:Top) = a.isUniv () || b.isUniv ();
  (Intersect a b).isUniv (_:Top) = a.isUniv () && b.isUniv ();
                _.isUniv (_:Top) = false;
  (Empty        ).isEmpty (_:Top) = true;
  (Outside     a).isEmpty (_:Top) = a.isUniv ();
  (Union     a b).isEmpty (_:Top) = a.isEmpty () && b.isEmpty ();
  (Intersect a b).isEmpty (_:Top) = a.isEmpty () || b.isEmpty ();
                _.isEmpty (_:Top) = false;
};

shapes = new repo @UE , ue;
go (n:Double) : String =
  if n == 0.0 then ""
  else let shape = shapes.universal n in
       letrec go' (i:Int) : String = if i == 0 then "" else toString (shape.isUniv ()) ++ go' (i - 1) in
       go' 1000 ++ go (n - 1.0);
go 100.0
