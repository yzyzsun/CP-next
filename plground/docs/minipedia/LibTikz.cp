type Hex = { hex : String };

type ColorSig<Color> = {
  Black   : Color;
  Silver  : Color;
  Gray    : Color;
  White   : Color;
  Maroon  : Color;
  Red     : Color;
  Purple  : Color;
  Fuchsia : Color;
  Green   : Color;
  Lime    : Color;
  Olive   : Color;
  Yellow  : Color;
  Navy    : Color;
  Blue    : Color;
  Teal    : Color;
  Aqua    : Color;
};

color = trait implements ColorSig<Hex> => {
  (Black).hex   = "#000000";
  (Silver).hex  = "#C0C0C0";
  (Gray).hex    = "#808080";
  (White).hex   = "#FFFFFF";
  (Maroon).hex  = "#800000";
  (Red).hex     = "#FF0000";
  (Purple).hex  = "#800080";
  (Fuchsia).hex = "#FF00FF";
  (Green).hex   = "#008000";
  (Lime).hex    = "#00FF00";
  (Olive).hex   = "#808000";
  (Yellow).hex  = "#FFFF00";
  (Navy).hex    = "#000080";
  (Blue).hex    = "#0000FF";
  (Teal).hex    = "#008080";
  (Aqua).hex    = "#00FFFF";
};

xcolor = trait implements ColorSig<Hex> => {
  (Black).hex   = "000000";
  (Silver).hex  = "C0C0C0";
  (Gray).hex    = "808080";
  (White).hex   = "FFFFFF";
  (Maroon).hex  = "800000";
  (Red).hex     = "FF0000";
  (Purple).hex  = "800080";
  (Fuchsia).hex = "FF00FF";
  (Green).hex   = "008000";
  (Lime).hex    = "00FF00";
  (Olive).hex   = "808000";
  (Yellow).hex  = "FFFF00";
  (Navy).hex    = "000080";
  (Blue).hex    = "0000FF";
  (Teal).hex    = "008080";
  (Aqua).hex    = "00FFFF";
};

type GraphicSig<Graphic><Color> = {
  Comp : Graphic -> Graphic -> Graphic;
  Str : String -> Graphic;
  Graph : { width: Int; height: Int } -> Graphic -> Graphic;
  Line : { x1: Int; y1: Int; x2: Int; y2: Int; color: Color; width: Int } -> Graphic;
  Rect : { x: Int; y: Int; width: Int; height: Int; color: Color } -> Graphic;
  Circle : { cx: Int; cy: Int; r: Int; color: Color } -> Graphic;
  Ellipse : { cx: Int; cy: Int; rx: Int; ry: Int; color: Color } -> Graphic;
  Path : { d: String; fill: Color; stroke: Color; width: Int } -> Graphic;
  Text : { x: Int; y: Int; color: Color } -> Graphic -> Graphic;
  Use : String -> String -> Graphic;
  Group : String -> Graphic -> Graphic;
  Defs : Graphic -> Graphic;
};

defcolor (colorname:String) (color:Hex) : String = "\\definecolor{" ++ colorname ++ "}{HTML}{" ++ color.hex ++ "}\n";

type TIKZ = { tikz : String };
tikz = trait implements GraphicSig<TIKZ><Hex> => {

  (Comp l r).tikz = l.tikz ++ r.tikz;
  (Str s).tikz = s;
  
  (Graph {..} e).tikz = "\\begin{tikzpicture}[x=1pt,y=-1pt]\n\\draw [draw = white, fill = white] (0.0, 0.0) rectangle (" ++ toString width ++ "," ++ toString height ++ ");\n" ++ e.tikz ++ "\\end{tikzpicture}\n";
  
  (Line {..}).tikz = let colorname = "cpclr" ++ color.hex in
  defcolor colorname color ++ 
  "\\draw[draw = " ++ colorname ++ ", line width = " ++ toString width ++ "] (" ++ toString x1 ++ "," ++ toString y1 ++ ") -- (" ++ toString x2 ++ "," ++ toString y2 ++ ");\n";

  (Rect {..}).tikz = let colorname = "cpclr" ++ color.hex in
  defcolor colorname color ++
  "\\draw[draw = " ++ colorname ++ ", fill = " ++ colorname ++ "] (" ++ toString x ++ "," ++ toString y ++ ") rectangle (" ++ toString (x+width) ++ "," ++ toString (y+height) ++ ");\n";

  (Circle {..}).tikz = let colorname = "cpclr" ++ color.hex in
  defcolor colorname color ++
  "\\draw[draw = " ++ colorname ++ ", fill = " ++ colorname ++ "] (" ++ toString cx ++ "," ++ toString cy ++ ") circle [radius = " ++ toString r ++ "pt];\n";
  
  (Ellipse {..}).tikz = let colorname = "cpclr" ++ color.hex in
  defcolor colorname color ++
  "\\draw[draw = " ++ colorname ++ ", fill = " ++ colorname ++ "] (" ++ toString cx ++ "," ++ toString cy ++ ") ellipse [x radius = " ++ toString rx ++ "pt, y radius = " ++ toString ry ++ "pt];\n";
  
  (Path {..}).tikz =
  let strokecolorname = "cpclr" ++ stroke.hex in
  let fillcolorname = "cpclr" ++ fill.hex in
  defcolor strokecolorname stroke ++
  defcolor strokecolorname fill ++
  "\\draw[draw = " ++ strokecolorname ++ ", fill = " ++ fillcolorname ++ ",line width=" ++ toString width ++ "] svg[scale=1cm]{" ++ d ++ "};\n";
  
  (Text {..} e).tikz = let colorname = "cpclr" ++ color.hex in
  defcolor colorname color ++
  "\\draw[color =" ++ colorname ++ "] (" ++ toString x ++ "," ++ toString y ++ ") node {" ++ e.tikz ++ "};\n";
  
  (Use id tr).tikz = "\\pic{" ++ id ++ "};";
  (Group id e).tikz = "\\tikzset{\n" ++ id ++ "/.pic={\n" ++ e.tikz ++ "}}\n\\pic{" ++ id ++ "}\n";
  (Defs e).tikz = "";
};

doc = trait [self : GraphicSig<TIKZ><Hex> & ColorSig<Hex>] => {
  body = `
  \Graph{ width = 375; height = 300}[
  		\Rect{ x = 0; y = 0; width = 375; height = 150; color = Red }
  		\Rect{ x = 0; y = 150; width = 375; height = 150; color = White }
]`;
};

(new doc, tikz, xcolor).body.tikz