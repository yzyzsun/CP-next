--| Pass

open doc;
open svg;

foldl' T (f : T -> T -> T) (z : T) (xs : [T]) (i : Int) : T =
  if i == 0 then z else f (foldl' @T f z xs (i-1)) (xs!!(i-1));
foldl T (f : T -> T -> T) (z : T) (xs : [T]) = foldl' @T f z xs (#xs);

type Fractal Graphic Color = {
  fractal : { level?: Int; x: Int; y: Int; width: Int; height: Int } -> Graphic;
};

doc T C = trait [self : DocSig<T> & GraphicSig<T><C> & ColorSig<C> & Fractal T C] implements Fractal T C => {
  fractal { level = 3; .. } =
    let args = { level = level-1; width = width/3; height = height/3 } in
    let center = new self.Rect (args,{ x = x + width/3; y = y + height/3; color = new self.White }) in
    if level == 0 then center
    else foldl @T (\(s:T) (x:T) -> new self.Comp s x) center
      [ self.fractal (args,{ x = x;             y = y })
      ; self.fractal (args,{ x = x + width/3;   y = y })
      ; self.fractal (args,{ x = x + width*2/3; y = y })
      ; self.fractal (args,{ x = x;             y = y + height/3 })
      ; self.fractal (args,{ x = x + width*2/3; y = y + height/3 })
      ; self.fractal (args,{ x = x;             y = y + height*2/3 })
      ; self.fractal (args,{ x = x + width/3;   y = y + height*2/3 })
      ; self.fractal (args,{ x = x + width*2/3; y = y + height*2/3 })
      ];
  body = let init = { x = 0; y = 0; width = 600; height = 600; color = new self.Black } in
         open self in `\Graph(init)[ \Rect(init) \fractal(init) ]`;
};

(new doc @HTML @Hex , html' , svg , color).body.html
