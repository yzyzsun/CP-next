--> 48

type Sig<T> = { Ctor: { x?: Int; y?: Int; z: Int } -> T };
type Sum = { sum: Int };
t = trait implements Sig<Sum> => {
  (Ctor { x = 0; y = 0; .. }).sum = x + y + z;
};
(new (new t).Ctor { y = 40; z = 8 }).sum
