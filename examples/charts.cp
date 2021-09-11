--| Pass

open doc;
open svg;

config = {
  width  = 600;
  height = 400;
  margin = 30;
  maxY   = 140;
  numY   = 7;
  line   = false;
  legend = true;
  border = true;
  label  = {
    data = true;
    axes = ["Month"; "Price"]
  }
};

factory = new html , svg , color;

type Data = {
  name: String;
  color: Hex;
  d: [{ month: String; price: Int }];
};

apple = {
  name = "Apple";
  color = new factory.Red;
  d = [
    { month = "Jan";  price = 81 };
    { month = "Feb";  price = 68 };
    { month = "Mar";  price = 61 };
    { month = "Apr";  price = 72 };
    { month = "May";  price = 80 };
    { month = "June"; price = 91 };
    { month = "July"; price = 96 };
    { month = "Aug";  price = 134 };
    { month = "Sept"; price = 117 };
    { month = "Oct";  price = 109 };
    { month = "Nov";  price = 123 };
    { month = "Dec";  price = 133 };
  ];
} : Data;

tsmc = {
  name = "TSMC";
  color = new factory.Blue;
  d = [
    { month = "Jan";  price = 54 };
    { month = "Feb";  price = 54 };
    { month = "Mar";  price = 48 };
    { month = "Apr";  price = 53 };
    { month = "May";  price = 50 };
    { month = "June"; price = 57 };
    { month = "July"; price = 79 };
    { month = "Aug";  price = 79 };
    { month = "Sept"; price = 81 };
    { month = "Oct";  price = 84 };
    { month = "Nov";  price = 97 };
    { month = "Dec";  price = 109 };
  ];
} : Data;

type Base = {
  data_   : [Data];
  xAxis   : HTML;
  yAxis   : HTML;
  caption : HTML;
};
type Render = { render : HTML };
type Chart = Base & Render;
type ChartT = Trait<Chart => Chart>;

baseChart (data : [Data]) = trait implements Base => open factory in {
  data_ = data;
  xAxis = letrec xAxis' (i:Int) : HTML = open config in let d = (data!!0).d in
    let x = margin + (width - margin) * (i*2 + 1) / (#d*2) in let y = height - margin in
    if i == #d then `
      \Line{ x1 = margin; y1 = y; x2 = width; y2 = y }
    ` else `
      \Line{ x1 = x; y1 = y - 5; x2 = x; y2 = y }
      \Text{ x = x - 10; y = y + 15 }[\((d!!i).month)]
      \xAxis'(i+1)
    ` in xAxis' 0;
  yAxis = letrec yAxis' (i:Int) : HTML = open config in
    if i == numY then `` else let y = height - margin - (height - margin*2) * (i+1) / numY in `
      \Line{ x1 = margin; y1 = y; x2 = margin + 5; y2 = y }
      \Text{ x = margin - 22; y = y + 3 }[\(maxY * (i+1) / numY)]
      \yAxis'(i+1)
    ` in yAxis' 0;
  caption = letrec caption' (n:Int) : String =
    if n == #data - 1 then (data!!n).name else (data!!n).name ++ " vs " ++ caption' (n+1)
    in `\Text{ x = 50; y = 10 }[\(caption' 0)]`;
};

lineStrategy = trait [self : Base] implements Render => open factory in {
  render = letrec lines' (n:Int) (i:Int) : HTML = open config in
    if n == #data_ then `` else let c = (data_!!n).color in let d = (data_!!n).d in
    if i == #d - 1 then `\lines'(n+1)(0)` else
    let p1 = (d!!i).price in let p2 = (d!!(i+1)).price in `
      \Line{
        x1 = margin + (width - margin) * (i*2 + 1) / (#d*2);
        y1 = height - margin - (height - margin*2) * p1 / maxY;
        x2 = margin + (width - margin) * (i*2 + 3) / (#d*2);
        y2 = height - margin - (height - margin*2) * p2 / maxY;
        color = c;
      }
      \lines'(n)(i+1)
    ` in let lines = lines' 0 0 in `\xAxis \yAxis \lines \caption`
};

barStrategy = trait [self : Base] implements Render => open factory in {
  render = letrec bars' (n:Int) (i:Int) : HTML = open config in
    if n == #data_ then `` else let c = (data_!!n).color in let d = (data_!!n).d in
    if i == #d then `\bars'(n+1)(0)` else let price = (d!!i).price in `
      \Rect{
        x = margin + (width - margin) * i / #d + 5;
        y = height - margin - (height - margin*2) * price / maxY;
        width = (width - margin) / #d - 10;
        height = (height - margin*2) * price / maxY;
        color = c;
      }
      \bars'(n)(i+1)
    ` in let bars = bars' 0 0 in `\xAxis \yAxis \bars \caption`
};

legendDecorator (chart : ChartT) =
    trait [self : Chart] implements Chart inherits chart => open factory in {
  override caption = letrec legends' (n:Int) : HTML = open config in
    if n == #data_ then `` else let datum = data_ !! n in `
      \Rect{ x = margin + 20 + 50*n; y = margin - 20; width = 5; height = 5; color = datum.color }
      \Text{ x = margin + 30 + 50*n; y = margin - 15 }[\(datum.name)]
      \legends'(n+1)
    ` in `\legends'(0)`
};

borderDecorator (chart : ChartT) =
    trait [self : Chart] implements Chart inherits chart => open factory in {
  override render = let sr = super.render in open config in `\sr
    \Line{ x1 = margin; y1 = margin; x2 = width; y2 = margin }
    \Line{ x1 = margin; y1 = margin; x2 = margin; y2 = height - margin }
    \Line{ x1 = width - 1; y1 = margin; x2 = width - 1; y2 = height - margin }
  `;
};

dataLabelDecorator (chart : ChartT) =
    trait [self : Chart] implements Chart inherits chart => open factory in {
  override render = letrec labels' (n:Int) (i:Int) : HTML = open config in
    if n == #data_ then `` else let c = (data_!!n).color in let d = (data_!!n).d in
    if i == #d then `\labels'(n+1)(0)` else let price = (d!!i).price in `
      \Text{
        x = margin + (width - margin) * (i*2 + 1) / (#d*2) - 6;
        y = height - margin - (height - margin*2) * price / maxY - 3;
        color = c;
      }[\(price)]
      \labels'(n)(i+1)
    ` in let sr = super.render in `\sr \labels'(0)(0)`;
};

axisLabelDecorator (labels : [String]) (chart : ChartT) =
    trait [self : Chart] implements Chart inherits chart => open factory in {
  override xAxis = let sx = super.xAxis in open config in `\sx
    \Text{ x = (width + margin) / 2; y = height - margin + 30; color = Gray }[\(labels!!0)]
  `;
  override yAxis = let sy = super.yAxis in open config in `\sy
    \Text{ x = margin - 30; y = height - margin - 10; color = Gray }[\(labels!!1)]
  `;
};

type ChartSig<Element> = {
  Chart : Chart -> Element;
};

chart = trait implements ChartSig<HTML> => {
  Chart chart = trait => chart.render;
};

doc = trait [self : DocSig<HTML> & GraphicSig<HTML><Hex> & ColorSig<Hex> & ChartSig<HTML>] => {
  body =
    let chart = baseChart [apple; tsmc] in
    let chart = chart , if config.line then lineStrategy else barStrategy in
    let chart = if config.legend then legendDecorator chart else chart in
    let chart = if config.border then borderDecorator chart else chart in
    let chart = if config.label.data then dataLabelDecorator chart else chart in
    let chart = if #config.label.axes == 2 then axisLabelDecorator config.label.axes chart else chart in `
      \Graph{ width = config.width; height = config.height }[\Chart(new chart)]
    `
};

(new html , svg , color , chart , doc).body.html
