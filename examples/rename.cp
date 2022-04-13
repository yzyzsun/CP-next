--> 2

type X = { x : Int };
t = trait [self : X] => { x = 1; y = self.x };
o = new t [x <- z];
o.y + o.z
