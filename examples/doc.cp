--| Pass

open doc;

doc T = trait [self : DocSig'<T>] => {
  body = `
    \Section[
      Welcome to \Href("https://plground.org")[PLGround]!
    ]
    \Bold[CP] is a \Emph[compositional] programming language. \\
    There are \( 1+1+1+1 ) key concepts in CP:
    \Enumerate[
      \Item[Compositional interfaces;]
      \Item[Compositional traits;]
      \Item[Method patterns;]
      \Item[Nested trait composition.]
    ]
  `
};

(new doc @(HTML & LaTeX) , html' , latex').body.html
