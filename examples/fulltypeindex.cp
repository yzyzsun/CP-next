--> 0

type A = (Int -> Int&Bool) -> Int;
type B = (Int -> Int&String) -> Int;
f (g : Int -> Int) = g 0;
h (x : Int) = x , true;
((f : A & B) : A) h
