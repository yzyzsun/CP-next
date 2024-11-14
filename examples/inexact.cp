--> "FOOBAR"

toUpperCase (s: String) = s; -- dummy implementation

mixin (TBase * { m: Int }) (base: Trait<TBase>) =
  trait [this: TBase] inherits base => { m = 48 };

mkA = trait [this: { m: String; n: String }] => {
  m = "FOOBAR";
  n = toUpperCase this.m;
};

o = new mixin @{ m: String; n: String } mkA;
o.n
