--> 25

ints (i:Int) : [Int] = if i == 1 then [] else ints (i-1) ++ [i];
primes (nums:[Int]) =
  letrec primes' (nums':[Int]) (i:Int) : [Int] =
    if i >= #nums' then nums'
    else letrec filter (j:Int) : [Int] = let curr = nums'!!j in
           if j >= #nums' then []
           else (if j > i && curr % nums'!!i == 0 then [] else [curr]) ++ filter (j+1)
         in primes' (filter 0) (i+1)
  in primes' nums 0;
#(primes (ints 100))
