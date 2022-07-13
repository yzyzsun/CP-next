open LibKoch;

doc T C = trait [self : DocSig<T> & GraphicSig<T><C> & ColorSig<C> & Draw T C] inherits draw @T @C => {
  override init = { x1 = 0; y1 = 150; x2 = 486; y2 = 150; width = 1; level = 5 };
  body = let curve = draw init in
  let flipped = `\Rotate{angle=180; x=(init.x1+init.x2)/2; y=init.y1}(curve)` in
  `\Section[Koch Snowflake]
    \Graph{ width = init.x2+1; height = init.y2+init.x2}[
      \curve
      \Rotate{angle=-60; x = init.x2; y = init.y1}(flipped)
      \Rotate{angle=60; x = init.x1; y = init.y1}(flipped)
    ]
  `;
};

(new doc @HTML @Hex , html , svg , color).body.html