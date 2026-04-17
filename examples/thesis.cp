--> (({ y = 2 } , { color = "black" }) , { x = 0 })

type Point = { x: Int; y: Int };

point (x: Int) (y: Int) =
  trait implements Point => { x = x; y = y };

type ColorPoint = Point & { color: String };

colorPoint (x: Int) (y: Int) (c: String) =
  trait implements ColorPoint inherits point x y => { color = c };

blackPoint = colorPoint 1 2 "black";

reflected = trait inherits blackPoint => {
  override x = -super.x;
  override y = -super.y;
};

mixedPoint = trait [self] inherits blackPoint\color , reflected\\Point => {
  override x = super.x + (reflected^self).x;
};
new mixedPoint
