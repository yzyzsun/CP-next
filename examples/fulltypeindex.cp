--> 0

type A = (Int -> Int&Bool) -> Int;
type B = (Int -> Int&String) -> Int;
f (g : Int -> Int) = g 0;
f' = f : A & B;
f'' = f' : A;
f'' (\(x:Int) -> x,true)
