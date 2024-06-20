type UE = {
  isUniv: () => boolean;
  isEmpty: () => boolean;
};

class Family0 {
  Circle(r: number) {
    return class {
      isUniv() { return false }
      isEmpty() { return false }
    }
  }
  Outside(a: UE) {
    return class {
      isUniv() { return a.isEmpty() }
      isEmpty() { return a.isUniv() }
    }
  }
  Union(a: UE, b: UE) {
    return class {
      isUniv() { return a.isUniv() || b.isUniv() }
      isEmpty() { return a.isEmpty() && b.isEmpty() }
    }
  }
  Intersect(a: UE, b: UE) {
    return class {
      isUniv() { return a.isUniv() && b.isUniv() }
      isEmpty() { return a.isEmpty() || b.isEmpty() }
    }
  }
  Univ() {
    return class {
      isUniv() { return true }
      isEmpty() { return false }
    }
  }
  Empty() {
    return class {
      isUniv() { return false }
      isEmpty() { return true }
    }
  }
}

type Size1 = { size1: () => number };
class Family1 extends Family0 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size1() { return 1 }
    }
  }
  Outside(a: UE & Size1) {
    return class extends super.Outside(a) {
      size1() { return a.size1() + 1 }
    }
  }
  Union(a: UE & Size1, b: UE & Size1) {
    return class extends super.Union(a, b) {
      size1() { return a.size1() + b.size1() + 1 }
    }
  }
  Intersect(a: UE & Size1, b: UE & Size1) {
    return class extends super.Intersect(a, b) {
      size1() { return a.size1() + b.size1() + 1 }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size1() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size1() { return 1 }
    }
  }
}

type Size2 = { size2: () => number };
class Family2 extends Family1 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size2() { return 1 }
    }
  }
  Outside(a: UE & Size1 & Size2) {
    return class extends super.Outside(a) {
      size2() { return a.size2() }
    }
  }
  Union(a: UE & Size1 & Size2, b: UE & Size1 & Size2) {
    return class extends super.Union(a, b) {
      size2() { return a.size2() + b.size2() }
    }
  }
  Intersect(a: UE & Size1 & Size2, b: UE & Size1 & Size2) {
    return class extends super.Intersect(a, b) {
      size2() { return a.size2() + b.size2() }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size2() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size2() { return 1 }
    }
  }
}

type Size3 = { size3: () => number };
class Family3 extends Family2 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size3() { return 1 }
    }
  }
  Outside(a: UE & Size1 & Size2 & Size3) {
    return class extends super.Outside(a) {
      size3() { return a.size3() }
    }
  }
  Union(a: UE & Size1 & Size2 & Size3, b: UE & Size1 & Size2 & Size3) {
    return class extends super.Union(a, b) {
      size3() { return a.size3() + b.size3() }
    }
  }
  Intersect(a: UE & Size1 & Size2 & Size3, b: UE & Size1 & Size2 & Size3) {
    return class extends super.Intersect(a, b) {
      size3() { return a.size3() + b.size3() }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size3() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size3() { return 1 }
    }
  }
}

type Size4 = { size4: () => number };
class Family4 extends Family3 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size4() { return 1 }
    }
  }
  Outside(a: UE & Size1 & Size2 & Size3 & Size4) {
    return class extends super.Outside(a) {
      size4() { return a.size4() }
    }
  }
  Union(a: UE & Size1 & Size2 & Size3 & Size4, b: UE & Size1 & Size2 & Size3 & Size4) {
    return class extends super.Union(a, b) {
      size4() { return a.size4() + b.size4() }
    }
  }
  Intersect(a: UE & Size1 & Size2 & Size3 & Size4, b: UE & Size1 & Size2 & Size3 & Size4) {
    return class extends super.Intersect(a, b) {
      size4() { return a.size4() + b.size4() }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size4() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size4() { return 1 }
    }
  }
}

type Size5 = { size5: () => number };
class Family5 extends Family4 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size5() { return 1 }
    }
  }
  Outside(a: UE & Size1 & Size2 & Size3 & Size4 & Size5) {
    return class extends super.Outside(a) {
      size5() { return a.size5() }
    }
  }
  Union(a: UE & Size1 & Size2 & Size3 & Size4 & Size5, b: UE & Size1 & Size2 & Size3 & Size4 & Size5) {
    return class extends super.Union(a, b) {
      size5() { return a.size5() + b.size5() }
    }
  }
  Intersect(a: UE & Size1 & Size2 & Size3 & Size4 & Size5, b: UE & Size1 & Size2 & Size3 & Size4 & Size5) {
    return class extends super.Intersect(a, b) {
      size5() { return a.size5() + b.size5() }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size5() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size5() { return 1 }
    }
  }
}

type Size6 = { size6: () => number };
class Family6 extends Family5 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size6() { return 1 }
    }
  }
  Outside(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6) {
    return class extends super.Outside(a) {
      size6() { return a.size6() }
    }
  }
  Union(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6) {
    return class extends super.Union(a, b) {
      size6() { return a.size6() + b.size6() }
    }
  }
  Intersect(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6) {
    return class extends super.Intersect(a, b) {
      size6() { return a.size6() + b.size6() }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size6() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size6() { return 1 }
    }
  }
}

type Size7 = { size7: () => number };
class Family7 extends Family6 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size7() { return 1 }
    }
  }
  Outside(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7) {
    return class extends super.Outside(a) {
      size7() { return a.size7() }
    }
  }
  Union(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7) {
    return class extends super.Union(a, b) {
      size7() { return a.size7() + b.size7() }
    }
  }
  Intersect(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7) {
    return class extends super.Intersect(a, b) {
      size7() { return a.size7() + b.size7() }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size7() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size7() { return 1 }
    }
  }
}

type Size8 = { size8: () => number };
class Family8 extends Family7 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size8() { return 1 }
    }
  }
  Outside(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8) {
    return class extends super.Outside(a) {
      size8() { return a.size8() }
    }
  }
  Union(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8) {
    return class extends super.Union(a, b) {
      size8() { return a.size8() + b.size8() }
    }
  }
  Intersect(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8) {
    return class extends super.Intersect(a, b) {
      size8() { return a.size8() + b.size8() }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size8() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size8() { return 1 }
    }
  }
}

type Size9 = { size9: () => number };
class Family9 extends Family8 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size9() { return 1 }
    }
  }
  Outside(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9) {
    return class extends super.Outside(a) {
      size9() { return a.size9() }
    }
  }
  Union(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9) {
    return class extends super.Union(a, b) {
      size9() { return a.size9() + b.size9() }
    }
  }
  Intersect(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9) {
    return class extends super.Intersect(a, b) {
      size9() { return a.size9() + b.size9() }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size9() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size9() { return 1 }
    }
  }
}

type Size10 = { size10: () => number };
class Family10 extends Family9 {
  Circle(r: number) {
    return class extends super.Circle(r) {
      size10() { return 1 }
    }
  }
  Outside(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9 & Size10) {
    return class extends super.Outside(a) {
      size10() { return a.size10() }
    }
  }
  Union(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9 & Size10, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9 & Size10) {
    return class extends super.Union(a, b) {
      size10() { return a.size10() + b.size10() }
    }
  }
  Intersect(a: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9 & Size10, b: UE & Size1 & Size2 & Size3 & Size4 & Size5 & Size6 & Size7 & Size8 & Size9 & Size10) {
    return class extends super.Intersect(a, b) {
      size10() { return a.size10() + b.size10() }
    }
  }
  Univ() {
    return class extends super.Univ() {
      size10() { return 1 }
    }
  }
  Empty() {
    return class extends super.Empty() {
      size10() { return 1 }
    }
  }
}

var fam = new Family{{i}}();

function universal(n: number) {
  function universal_(i: number) {
    if (i === 0) return new (fam.Univ());
    else return new (fam.Intersect(new (fam.Union(new (fam.Outside(new (fam.Empty()))), new (fam.Circle(n)))), universal_(i-1)));
  }
  return universal_(200);
}

function go(n: number) {
  if (n === 0) return "";

  const shape = universal(n);
  function go_(i: number) {
    if (i === 0) return "";
    else return shape.isUniv() + go_(i-1);
  }
  return go_(1000) + go(n-1);
}

export function main() {
  return go(100);
}
