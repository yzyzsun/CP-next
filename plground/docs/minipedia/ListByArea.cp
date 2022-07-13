open LibTOC;
open database;
open LibInfobox;
open LibArray;
open LibNum;

merge (a:[StateInfo]) (b:[StateInfo]) : [StateInfo] = 
  if (#a) == 0 then b
  else if (#b) == 0 then a
  else if (head @StateInfo a).area < (head @StateInfo b).area then ([head @StateInfo a] ++ (merge (tail @StateInfo a) b))
  else [head @StateInfo b] ++ merge a (tail @StateInfo b);

sort (a:[StateInfo]) : [StateInfo] = 
  if (#a)<=1 then a
  else merge (sort (subArray @StateInfo a 0 ((#a)/2) )) (sort (subArray @StateInfo a ((#a)/2) (#a)));

printStates' (a:[DivInfo]) (i:Int) : String = 
  (if i==0 then "[" else "") ++ 
  (if i==(#a) then "]" else (a!!i).name ++ "; " ++ printStates' a (i+1));
printStates (a:[DivInfo]) = printStates' a 0;

sorteddb = sort (statesdb);

doc T = trait [self : DocSig<T> & CiteSig<T> & TableSig<T>] => {
  table = letrec rows (i:Int) : T = if i == #sorteddb then `` else
  	let state = sorteddb !! i in `\Trow[
      \Tdata[\(i+1)]
      \Tdata[\Href(state.link)[\Str(state.name)]]
      \Tdata[\(state.area)]
      \Tdata[\Str(intToMil (doubleToInt (state.population*1000000.0)))]
      \Tdata[\Href(state.capital.link)[\Str(state.capital.name)]]
  		\rows(i+1)
  	]` in `\Tbody[
  		\Trow[
  			\Theader[No.]
  			\Theader[Country]
  			\Theader[Area (km²)]
  			\Theader[Population]
  			\Theader[Capital]
      ]
  		\rows(0)
  	]\\`;
  body = `\Section[Smallest Microstates By Area]\\`;
};

document = new doc @HTML , html , cite [], table;
document.body.html ++ document.table.html