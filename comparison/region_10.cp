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

type Size1 = { size1 : Int };
sz1 = trait implements RegionSig<Size1> => {
  (Circle      r).size1 = 1;
  (Outside     a).size1 = a.size1 + 1;
  (Union     a b).size1 = a.size1 + b.size1 + 1;
  (Intersect a b).size1 = a.size1 + b.size1 + 1;
                _.size1 = 1;
};

type Size2 = { size2 : Int };
sz2 = trait implements RegionSig<Size2> => {
  (Circle      r).size2 = 1;
  (Outside     a).size2 = a.size2 + 1;
  (Union     a b).size2 = a.size2 + b.size2 + 1;
  (Intersect a b).size2 = a.size2 + b.size2 + 1;
                _.size2 = 1;
};

type Size3 = { size3 : Int };
sz3 = trait implements RegionSig<Size3> => {
  (Circle      r).size3 = 1;
  (Outside     a).size3 = a.size3 + 1;
  (Union     a b).size3 = a.size3 + b.size3 + 1;
  (Intersect a b).size3 = a.size3 + b.size3 + 1;
                _.size3 = 1;
};

type Size4 = { size4 : Int };
sz4 = trait implements RegionSig<Size4> => {
  (Circle      r).size4 = 1;
  (Outside     a).size4 = a.size4 + 1;
  (Union     a b).size4 = a.size4 + b.size4 + 1;
  (Intersect a b).size4 = a.size4 + b.size4 + 1;
                _.size4 = 1;
};

type Size5 = { size5 : Int };
sz5 = trait implements RegionSig<Size5> => {
  (Circle      r).size5 = 1;
  (Outside     a).size5 = a.size5 + 1;
  (Union     a b).size5 = a.size5 + b.size5 + 1;
  (Intersect a b).size5 = a.size5 + b.size5 + 1;
                _.size5 = 1;
};

type Size6 = { size6 : Int };
sz6 = trait implements RegionSig<Size6> => {
  (Circle      r).size6 = 1;
  (Outside     a).size6 = a.size6 + 1;
  (Union     a b).size6 = a.size6 + b.size6 + 1;
  (Intersect a b).size6 = a.size6 + b.size6 + 1;
                _.size6 = 1;
};

type Size7 = { size7 : Int };
sz7 = trait implements RegionSig<Size7> => {
  (Circle      r).size7 = 1;
  (Outside     a).size7 = a.size7 + 1;
  (Union     a b).size7 = a.size7 + b.size7 + 1;
  (Intersect a b).size7 = a.size7 + b.size7 + 1;
                _.size7 = 1;
};

type Size8 = { size8 : Int };
sz8 = trait implements RegionSig<Size8> => {
  (Circle      r).size8 = 1;
  (Outside     a).size8 = a.size8 + 1;
  (Union     a b).size8 = a.size8 + b.size8 + 1;
  (Intersect a b).size8 = a.size8 + b.size8 + 1;
                _.size8 = 1;
};

type Size9 = { size9 : Int };
sz9 = trait implements RegionSig<Size9> => {
  (Circle      r).size9 = 1;
  (Outside     a).size9 = a.size9 + 1;
  (Union     a b).size9 = a.size9 + b.size9 + 1;
  (Intersect a b).size9 = a.size9 + b.size9 + 1;
                _.size9 = 1;
};

type Size10 = { size10 : Int };
sz10 = trait implements RegionSig<Size10> => {
  (Circle      r).size10 = 1;
  (Outside     a).size10 = a.size10 + 1;
  (Union     a b).size10 = a.size10 + b.size10 + 1;
  (Intersect a b).size10 = a.size10 + b.size10 + 1;
                _.size10 = 1;
};

shapes = new repo @(UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9 & Size10) , ue , sz1 , sz2 , sz3 , sz4 , sz5 , sz6 , sz7 , sz8 , sz9 , sz10;
go (n:Double) : String =
  if n == 0.0 then ""
  else let shape = shapes.universal n in
       letrec go' (i:Int) : String = if i == 0 then "" else toString (shape.isUniv ()) ++ go' (i - 1) in
       go' 1000 ++ go (n - 1.0);
go 100.0
