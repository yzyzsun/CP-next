fib (n:Int) : Int = if n <= 1 then n
                    else fib (n-1) + fib (n-2);
fib 42
