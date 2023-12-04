--| Pass

open doc;

type ProgSig<Element> = {
  Foreach : forall A. [A] -> (A -> Element) -> Element
};

prog Element = trait [self : DocSig<Element>] implements ProgSig<Element> => {
  Foreach = /\A. \xs f -> trait =>
    letrec go (i:Int) : Element = if i == #xs then Str ""
                                  else Comp (f (xs!!i)) (go (i+1))
    in go 0
};

fruits = [ "apple"; "banana"; "cherry" ];

repo Element = trait [self : DocSig'<Element> & ProgSig<Element>] => {
  ex = `\Itemize[
    \Foreach@String(fruits)(\(x:String) -> `\Item[\(x)]`)
  ] TODO: support @T and nested backticks in the ANTLR parser`
};

(new repo @HTML , prog @HTML , html').ex.html
