--| Pass

open doc;

type ProgSig<Element> = {
  Foreach : forall A. [A] -> (A -> Element) -> Element
};

prog Element = trait [self : DocSig<Element>] implements ProgSig<Element> => {
  Foreach = /\A. \xs f -> trait =>
    letrec go (i:Int) : Element = if i == #xs then new self.Str ""
                                  else new self.Comp (f (xs!!i)) (go (i+1))
    in go 0
};

fruits = [ "apple"; "banana"; "cherry" ];

repo Element = trait [self : DocSig'<Element> & ProgSig<Element>] => {
  ex = open self in `\Itemize[
    \Foreach@String(fruits)(\(x:String) -> `\Item[\(x)]`)
  ] TODO: support @T and nested backticks in the ANTLR parser`
};

(new repo @HTML , prog @HTML , html').ex.html
