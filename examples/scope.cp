--> 1

x = 1;
f Dummy (y:Int) = x + y;
g (_:Top) = let x = 2 in f @Top 0;
g ()
