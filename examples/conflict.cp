--> "1A2B3A"

type F = { f : Int };
type G = { g : String };

t1 = trait implements F & G => { f = 1; g = "A" };
t2 = trait implements F & G => { f = 2; g = "B" };

o1 = new t1 +, t2;
o2 = new t1 ,+ t2;

t3 = trait [self] inherits (t1 \ F) , (t2 \ G) implements F & G => {
  override f = super.f + (t1 ^ self).f;
};
o3 = new t3;

toString o1.f ++ o1.g ++
toString o2.f ++ o2.g ++
toString o3.f ++ o3.g
