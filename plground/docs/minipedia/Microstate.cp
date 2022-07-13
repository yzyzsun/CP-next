open LibTOC;
open MicrostateRef;
open LibTable;
open database;
open LibNum;

microstates = [ vatican; monaco; nauru; tuvalu; sanmarino; liechtenstein; marshall; skan ];
statelinks = [ "VaticanCity"; "Monaco"; "Nauru"; "Tuvalu"; "SanMarino"; "Liechtenstein"; "MarshallIslands"; "SaintKittsAndNevis" ];
capitallinks = [ "VaticanCity"; "Monaco"; "Yaren"; "Funafuti"; "SanMarinoCity"; "Vaduz"; "Majuro"; "Basseterre" ];

doc T = trait [self : DocSig<T> & CiteSig<T> & TableSig<T>] => {
  table = letrec rows (i:Int) : T = if i == #microstates then `` else
  	let state = microstates !! i in `\Trow[
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
  body = `
\Section[Microstate]
A \Bold[microstate] or \Bold[ministate] is a sovereign state having a very small population or very small land area, usually both. The meanings of "state" and "very small" are not well-defined in international law.\Cite("ref1") Recent attempts, since 2010, to define microstates have focused on identifying political entities with unique qualitative features linked to their geographic or demographic limitations. According to a qualitative definition, microstates are "modern protected states, i.e. sovereign states that have been able to unilaterally depute certain attributes of sovereignty to larger powers in exchange for benign protection of their political and economic viability against their geographic or demographic constraints."\Cite("ref2") In line with this and most other definitions, examples of microstates include Andorra, the Federated States of Micronesia, Liechtenstein, the Marshall Islands, Monaco, Palau, and San Marino. The smallest political entity recognized as a sovereign state is Vatican City, with around 1,000 citizens as of 2017 and an area of only 44 hectares (110 acres). Some microstates are city-states consisting of a single municipality.
\\
Microstates are distinct from micronations, which are not recognized as sovereign states. Special territories without full sovereignty, such as the British Crown dependencies, the special administrative regions of China (like \Href("HongKong")[Hong Kong]), and the overseas territories of various recognized states are also not usually considered microstates.
\\\\
\Section[References]
\Bib
`;
};

document = new doc @HTML , html , cite refs, table;
document.table.html ++ document.body.html