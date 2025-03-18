--> 6

f (arg: Int | ()) = switch arg as a
                    case Int => a + 1
                    case () => 2;
f 3 + f ()
