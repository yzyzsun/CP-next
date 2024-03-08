--> ()

counter = ref 0;
inc (c: Ref Int) = c := !c + 1 >> !c;
