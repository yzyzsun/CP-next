open LibTOC;
open database;

doc T = trait [self : DocSig<T> & CiteSig<T> & TableSig<T>] => {
  
  body = 
    letrec citylist (i:Int) : T = if i == #citiesdb then `` else 
      let city = citiesdb!!i in `\Item[\Href(city.link)[\Str(city.name)]] \citylist(i+1)`
    in
    letrec countrylist (i:Int) : T = if i == #statesdb then `` else 
      let country = statesdb!!i in `\Item[\Href(country.link)[\Str(country.name)]] \countrylist(i+1)`
    in
  `
\Section[Minipedia]
Minipedia is a repository of documents of Cities and Countries. It contains pages about 8 \Href("Microstate")[Microstates] and 7 cities. Besides, it also contains containes lists like sorted lists of Smallest countries by Area and Population.
\SubSection[Countries]
Following is the list of countries in Minipedia:
\Enumerate[
  \countrylist(0)
]
\SubSection[Cities]
Following is the list of cities in Minipedia:
\Enumerate[
  \citylist(0)
]
\SubSection[Lists]
Following documents are sorted lists of microstates by population and area:
\Enumerate[
  \Item[\Href("smallestmicrostatesbyarea")[List of Smallest Microstates by Area]]
  \Item[\Href("smallestmicrostatesbypopulation")[List of Smallest Microstates by Population]]
]
\Section[See Also]
\Itemize[
  \Item[\Href("../fractals/home")[Fractals]]
]

`;
};

document = new doc @HTML , html , cite [], table;
document.body.html
