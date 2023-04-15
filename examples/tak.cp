--> 99

tak (x:Int) (y:Int) (z:Int) : Int = if x <= y then y
  else tak (tak (x-1) y z) (tak (y-1) z x) (tak (z-1) x y);
tak 99 66 33
