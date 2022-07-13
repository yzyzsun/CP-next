open LibKoch;

doc T C = trait [self : DocSig<T> & GraphicSig<T><C> & ColorSig<C> & Draw T C] => {
  body = `
  \Section[Koch Curve]
    \Graph{ width = init.x2+1; height = init.y2+1}[
      \draw(init)
    ]
  `;
};

(new doc @HTML @Hex , draw @HTML @Hex, html , svg , color).body.html