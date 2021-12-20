--> "3A"

type F = { f : Int };
type G = { g : String };

t1 = trait implements F & G => { f = 1; g = "A" };
t2 = trait implements F & G => { f = 2; g = "B" };

t3 = trait [self] inherits (t1 \ F) , (t2 \ G) implements F & G => {
  override f = super.f + (t1 ^ self).f;
};

o = new t3;
toString o.f ++ o.g
