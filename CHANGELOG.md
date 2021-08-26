## Unreleased

- [WIP] iso-recursive types w/o distributive subtyping...
- [New] polymorphic record updates, e.g. `{ rcd | x = 1; y = 2 }`.
- [New] default values for record wildcards, e.g. `(Ctor { z = 0; .. }.method = ……`.
- Implicit self-type annotations (introduced in 0.1.2) are removed. Instead, self-references can be declared without type annotations, e.g. `[self]`, whose type will be inferred.

## 0.1.2

- [New] default patterns, e.g. `_.method = ……`.
- [New] record wildcards for method patterns, e.g. `(Ctor {..}).method = ……`.
- The delimiter for Zordoc is changed from triple quotes (`"""doc"""`) to backticks (`` `doc` ``), for the sake of parsing performance.
- The type checking of if-then-else is relaxed slightly: if one branch returns a supertype of the other, then that type is inferred.
- `[self : In & Out]` is implicitly added to method patterns if a trait family implements `Sig<In => Out>` (suggested by an anonymous reviewer from TOPLAS).
- The delimiter for input/output parts in trait types and sorts is changed from `%` to `=>` (suggested by @JimmyZJX).

## 0.1.1

- [New] Zor*doc*, e.g. `"""Zor\Emph[doc]"""`.
- [New] open directives (currently implemented as C-style `#include`), e.g. `open lib;`.
- Built-in `List` (a linked list) is replaced by JavaScript-based `Array`.
- Implemented call-by-need evaluation via JS FFI.

## 0.1.0

Initial Version of Zord. Most functionalities of CP are reimplemented.

## Appendix: (Incomplete) Syntactic Differences from CP

- The merge operator is simplified from double commas (`,,`) to a single comma (`,`). Meanwhile, the delimiter for record fields and array elements is always semicolon (`;`) instead of comma (`,`).
- `Trait[T]` is now `Trait<T>` and `Trait[I, O]` is now `Trait<I => O>`.
- `Sig<I1 % O1, I2 % O2>` is now `Sig<I1 => O1><I2 => O2>`.
- The syntax of object self-type annotations is changed from `(Ctor x [self : T])` to `[self : T]@(Ctor x)`.
- The keyword `extends` is removed: `type A extends B = C` can be rewritten as `type A = B & C`.
- `number.toString` is now `toString number`.
- Exclusion operators have a lower priority now. For example, the parentheses in `(t1 \ T1) , (t2 \ T2)` are necessary.
- Type annotations have the lowest priority now. For example, the parentheses in `{} , (ctx:Context)` are necessary.
