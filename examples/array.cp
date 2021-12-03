--> 14

sum (a : [Int]) =
  letrec sum' (i : Int) : Int =
    if i == #a then 0 else a!!i + sum' (i+1)
  in sum' 0;

double (i : Int) = i * 2;
array = [ 1; 1 + 1; double 2 ];

sum (array ++ array)
