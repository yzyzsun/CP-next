type Data = { mass : Double; x : Double; y : Double; vx : Double; vy : Double };
init = [ { mass = 2e32; x =       0.0; y =       0.0; vx =     0.0; vy =     0.0 }
       ; { mass = 6e24; x =   6.25e10; y =       0.0; vx =     0.0; vy =  5.66e5 }
       ; { mass = 6e24; x =  -6.25e10; y =       0.0; vx =     0.0; vy = -5.66e5 }
       ; { mass = 6e24; x =       0.0; y =   6.25e10; vx = -5.66e5; vy =     0.0 }
       ; { mass = 6e24; x =       0.0; y =  -6.25e10; vx =  5.66e5; vy =     0.0 }
       ; { mass = 1e26; x =  2.828e11; y =  2.828e11; vx =     1e5; vy =    -1e5 }
       ; { mass = 1e26; x =  2.828e11; y = -2.828e11; vx =    -1e5; vy =    -1e5 }
       ; { mass = 1e26; x = -2.828e11; y = -2.828e11; vx =    -1e5; vy =     1e5 }
       ; { mass = 1e26; x = -2.828e11; y =  2.828e11; vx =     1e5; vy =     1e5 }
       ; { mass = 1e16; x = -1.828e11; y =  1.828e11; vx =     1e5; vy =     1e5 }
       ];
kGravity = 6.673e-11;
eps = 0.01;

force (data:[Data]) (i:Int) =
  letrec force' (j:Int) : { x:Double; y:Double } =
    if j >= #data then { x = 0.0; y = 0.0 }
    else if j == i then force' (j+1)
    else let f = force' (j+1) in
         let dx = (data!!j).x - (data!!i).x in
         let dy = (data!!j).y - (data!!i).y in
         let dist = √(dx*dx + dy*dy) in
         let fxy = (kGravity * (data!!j).mass * (data!!i).mass) / (dist*dist + eps*eps) in
         { x = f.x + fxy * dx / dist; y = f.y + fxy * dy / dist }
  in force' 0;

update (data:[Data]) (dt:Double) =
  letrec update' (i:Int) : [Data] = if i >= #data then [] else
    let curr = data!!i in
    let f = force data i in
    let vx = curr.vx + dt * f.x / curr.mass in
    let vy = curr.vy + dt * f.y / curr.mass in
    [{ mass = curr.mass; x = curr.x + dt * vx; y = curr.y + dt * vy; vx = vx; vy = vy }] ++ update' (i+1)
  in update' 0;

repeat (i:Int) : [Data] = if i == 0 then init else update (repeat (i-1)) 100.0;
go (i:Int) : Double = if i == 0 then 0.0 else
  let head = repeat 1000 !! 0 in
  √(head.x*head.x + head.y*head.y) + go (i-1);
go 200
