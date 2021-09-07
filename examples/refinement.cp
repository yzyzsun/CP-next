--> 20

f (n : Int) = { x = n; y = n + 1; z = n * 2 };
f' = f : Int -> { y : Int; z : Int };
(f' 10).z
