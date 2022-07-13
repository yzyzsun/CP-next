open LibShare;

type Draw Graphic Color = {
  init : { x: Int; y: Int; width: Int; height: Int; color: Color; level: Int };
  draw : { x: Int; y: Int; width: Int; height: Int; level: Int } -> Graphic;
};

doc T C = trait [self : DocSig<T> & GraphicSig<T><C> & ColorSig<C> & Draw T C] implements Draw T C => {
  init = { x = 0; y = 0; width = 486; height = 486; color = Black; level = 4 };
  draw {..} =
    let center = Rect { x = x + width/3; y = y + height/3; width = width/3; height = height/3; color = White } in
    if level == 0 then center else
      open {w = width/3; h = height/3; l = level-1} in
      let g = draw {x = x; y = y; width = w; height = h; level = l} in `\Group(toString x ++ "," ++ toString y ++ "," ++ toString w ++ "," ++ toString h)[
       \g    \Translate{h=w; v=0}(g)   \Translate{h=2*w; v=0}(g)
       \Translate{h=0; v=h}(g)  \center  \Translate{h=2*w; v=h}(g)
       \Translate{h=0; v=2*h}(g) \Translate{h=w; v=2*h}(g) \Translate{h=2*w; v=2*h}(g)
      ]`;
  body = `
    \Section[Sierpiński Carpet]
    \Graph{ width = init.width; height = init.height }[
      \Rect(init)
      \draw(init)
    ]
  `;
};

(new doc @(HTML&ID) @Hex , html , svg , color , getid).body.html