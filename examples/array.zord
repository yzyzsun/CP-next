--> 14

sum' (a : [Int]) (i : Int) : Int =
  if i == 0 then a!!0 else sum' a (i-1) + a!!i;
sum (a : [Int]) = sum' a (#a - 1);

double (i : Int) = i * 2;
array = [ 1; 1 + 1; double 2 ];

sum (array ++ array)
