--> 125000

n = 50;

f (x:Int) : Int = if x == 0 then 0 else f (x-1) + 1;
g (x:Int) : Int = if x == 0 then 0 else f n + g (x-1);
h (x:Int) : Int = if x == 0 then 0 else g n + h (x-1);
h n
