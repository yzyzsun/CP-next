n = 500.0;
f (x:Double) : Double = if x == 0.0 then 1.0 else f (x-1.0) * x;
g (x:Double) : Double = if x == 0.0 then 1.0 else f n * g (x-1.0);
h (x:Double) : Double = if x == 0.0 then 1.0 else g n * h (x-1.0);
h n
