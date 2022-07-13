open LibShare;

type Draw Graphic Color = {
  init : { x: Int; y: Int; width: Int; height: Int; color: Color; level: Int };
  draw : { x: Int; y: Int; width: Int; height: Int; level: Int } -> Graphic;
};

doc T C = trait [self : DocSig<T> & GraphicSig<T><C> & ColorSig<C> & Draw T C] implements Draw T C => {
  init = { x = 0; y = 0; width = 512; height = 512; color = White; level = 6 };
  draw {..} =
      let center = Rect { x = x + width/4; y = y + height/4; width = width/2; height = height/2; color = Black } in
    if level == 0 then center else
      open {w = width/2; h = height/2} in
      let g = draw {x=x; y=y; width=w; height=h; level=level-1} in `\Group(toString x ++ "," ++ toString y ++ "," ++ toString w ++ "," ++ toString h)[
       \g                      \Translate{h=w;v=0}(g)
                       \center
       \Translate{h=0;v=h}(g)  \Translate{h=w;v=h}(g)
      ]`;
  body = `
    \Section[T-Square]
    \Graph{ width = init.width; height = init.height}[
      \Rect(init)
      \draw((init))
    ]
  `;
};

(new doc @(HTML&ID) @Hex , html , svg , color, getid).body.html