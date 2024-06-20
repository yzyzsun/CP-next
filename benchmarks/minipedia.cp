type HTML Context = { html : Context -> String };

type DocSig<Element> = {
  Comp : Element -> Element -> Element;
  Str : String -> Element;
  Endl : Element;
  Section : Element -> Element;
  SubSection : Element -> Element;
  SubSubSection : Element -> Element;
  Enumerate : Element -> Element;
  Itemize : Element -> Element;
  Item : Element -> Element;
  Href : String -> Element -> Element;
  Bold : Element -> Element;
  Emph : Element -> Element;
};

html Context = trait implements DocSig<HTML Context> => {
  (Comp l r).html ctx = l.html ctx ++ r.html ctx;
  (Str s).html _ = s;
  (Endl).html _ = "<br>";
  (Section e).html ctx = "<h2>" ++ e.html ctx ++ "</h2>";
  (SubSection e).html ctx = "<h3>" ++ e.html ctx ++ "</h3>";
  (SubSubSection e).html ctx = "<h4>" ++ e.html ctx ++ "</h4>";
  (Enumerate e).html ctx = "<ol>" ++ e.html ctx ++ "</ol>";
  (Itemize e).html ctx = "<ul>" ++ e.html ctx ++ "</ul>";
  (Item e).html ctx = "<li>" ++ e.html ctx ++ "</li>";
  (Href s e).html ctx = "<a href=\"" ++ s ++ "\">" ++ e.html ctx ++ "</a>";
  (Bold e).html ctx = "<b>" ++ e.html ctx ++ "</b>";
  (Emph e).html ctx = "<em>" ++ e.html ctx ++ "</em>";
};

type ContentsSig<Element> = DocSig<Element> & {
  TOC : Element;
};

type TOC = { toc : String };

type SCnt = { scnt : Int };
type SSCnt = { sscnt : Int };
type SSSCnt = { ssscnt : Int };
type Cnts = SCnt & SSCnt & SSSCnt;

type Contents Context = {
  toc : Cnts&Context -> TOC&Cnts&Context;
};

getIndex (l:Int) (e:Cnts) : String =
  if l == 0 then toString (e.scnt+1) ++ "&nbsp;&nbsp;"
  else if l == 1 then toString e.scnt ++ "." ++ toString (e.sscnt+1) ++ "&nbsp;&nbsp;"
  else toString e.scnt ++ "." ++ toString e.sscnt ++ "." ++ toString(e.ssscnt+1) ++ "&nbsp;&nbsp;";

getAnchor (s:String) : String = "<a href=\"#" ++ s ++ "\">" ++ s ++ "</a>";

listItem (l:Int) (s:String) : String =
  if l == 0 then "<li style=\"list-style-type:none\">" ++ s ++ "</li>"
  else "<li style=\"list-style-type:none\"><ul>" ++ listItem (l-1) s ++ "</ul></li>";

contents (Context * TOC&Cnts) = trait implements ContentsSig<HTML (TOC&Context) => Contents Context> => {
  (Comp l r).toc ctx =
    let ltoc = l.toc ctx in
    let rtoc = r.toc ltoc in
    { toc = ltoc.toc ++ rtoc.toc } , (rtoc : Cnts&Context);
  (Section e).toc ctx = {
    scnt = ctx.scnt + 1;
    toc = listItem 0 (getIndex 0 ctx ++ getAnchor (e.html ({ toc = "" } , (ctx:Context))));
  } , (ctx : SSCnt&SSSCnt&Context);
  (SubSection e).toc ctx = {
    sscnt = ctx.sscnt + 1;
    toc = listItem 1 (getIndex 1 ctx ++ getAnchor (e.html ({ toc = "" } , (ctx:Context))));
  } , (ctx : SCnt&SSSCnt&Context);
  (SubSubSection e).toc ctx = {
    ssscnt = ctx.ssscnt + 1;
    toc = listItem 2 (getIndex 2 ctx ++ getAnchor (e.html ({ toc = "" } , (ctx:Context))));
  } , (ctx : SCnt&SSCnt&Context);
  (Href s e).toc ctx = e.toc ctx;
  (Bold e).toc ctx = e.toc ctx;
  (Emph e).toc ctx = e.toc ctx;
  _.toc ctx = { toc = "" } , ctx;
};

htmlTOC (Context * TOC) = trait implements ContentsSig<HTML (TOC&Context)> inherits html @(TOC&Context) => {
  override (Section e).html ctx = "<h2 id=\"" ++ e.html ctx ++ "\">" ++ e.html ctx ++ "</h2>";
  override (SubSection e).html ctx = "<h3 id=\"" ++ e.html ctx ++ "\">" ++ e.html ctx ++ "</h3>";
  override (SubSubSection e).html ctx = "<h4 id=\"" ++ e.html ctx ++ "\">" ++ e.html ctx ++ "</h4>";
  (TOC).html ctx = "<ul id=\"toc\">" ++ ctx.toc ++ "</ul>";
};

doc T = trait [self : ContentsSig<T>] => {
  body = open self in `\TOC
    \Section[Lorem]\SubSection[Ipsum]
    Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.
    \Section[Ut]
    Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat.
  `
};

document = new doc @(HTML TOC & Contents Top) , htmlTOC @Top , contents @Top;
document.body.html (document.body.toc { scnt = 0; sscnt = 0; ssscnt = 0; toc = "" })
