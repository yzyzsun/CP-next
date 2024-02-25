--| Pass

open doc;
open svg;

foldl' T (f : T -> T -> T) (z : T) (xs : [T]) (i : Int) : T =
  if i == 0 then z else f (foldl' @T f z xs (i-1)) (xs!!(i-1));
foldl T (f : T -> T -> T) (z : T) (xs : [T]) = foldl' @T f z xs (#xs);

type Draw Graphic Color = {
  init : { x: Int; y: Int; width: Int; height: Int; color: Color; level: Int };
  draw : { x: Int; y: Int; width: Int; height: Int; level: Int } -> Graphic;
};

doc T C = trait [self : DocSig<T> & GraphicSig<T><C> & ColorSig<C> & Draw T C] implements Draw T C => {
  init = { x = 0; y = 0; width = 600; height = 600; color = new self.Black; level = 3 };
  draw = \{..} ->
    let center = new self.Rect { x = x + width/3; y = y + height/3; width = width/3; height = height/3; color = new self.White } in
    if level == 0 then center else
      let opt = { width = width/3; height = height/3; level = level - 1 } in
      let arr = [
        self.draw (opt,{ x = x; y = y });
        self.draw (opt,{ x = x + width/3; y = y });
        self.draw (opt,{ x = x + width*2/3; y = y });
        self.draw (opt,{ x = x; y = y + height/3 });
        self.draw (opt,{ x = x + width*2/3; y = y + height/3 });
        self.draw (opt,{ x = x; y = y + height*2/3 });
        self.draw (opt,{ x = x + width/3; y = y + height*2/3 });
        self.draw (opt,{ x = x + width*2/3; y = y + height*2/3 });
      ] in foldl @T (\(s:T) (x:T) -> new self.Comp s x) center arr;
  body = open self in `
    \Graph{ width = init.width; height = init.height }[
      \Rect(init)
      \draw(init)
    ]
  `;
};

(new doc @HTML @Hex , html' , svg , color).body.html
