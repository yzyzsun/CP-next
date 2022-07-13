open LibTikz;

doc = trait [self : GraphicSig<TIKZ><Hex> & ColorSig<Hex>] => {
  body = `
  \Graph{ width = 375; height = 300}[
  		\Rect{ x = 0; y = 0; width = 375; height = 150; color = Red }
  		\Rect{ x = 0; y = 150; width = 375; height = 150; color = White}
]`;
};

(new doc, tikz, xcolor).body.tikz