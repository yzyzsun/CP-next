--> 1

x = 1;
f Dummy (y:Int) = x + y;
g (_:()) = let x = 2 in f @() 0;
g ()
