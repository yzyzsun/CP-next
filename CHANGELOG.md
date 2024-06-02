## 0.2.0

- [New] a compiler targeting JavaScript; try `:compile` in the REPL or `npm run compiler` in a terminal.
- [New] an alternative ANTLR parser, which is faster than purescript-parsing.
- [New] type difference (`T1 \ T2`), term difference (`e1 \- e2`), field removal (`e \ l`), and label renaming (`e [ old <- new ]`).
- [New] leftist merge (`+,`) and rightist merge (`,+`).
- [Experimental] reference types (`Ref T`), introducing its value (`ref e`), dereference (`!e`), assignment (`e1 := e2`), and sequential composition (`e1 >> e2`); see the [example](examples/ref.cp). Currently only available in the compiler. 
- The logical not operator `!` is removed because `!` is now for dereference.
- Implicit `open self in` for traits is removed because `open` is strictly evaluated in compiled code. In other words, `self.` cannot be omitted unless explicitly writing `open self in` at the beginning of a field.
- Support `x ,, y` as an alias to `x , y` for compatibility.
- In a trait definition, `implements` and `inherits` clauses can be written in any order.
- Change the notation of record updates from `{ rcd | x = 1 }` (Elm-style) to `{ rcd with x = 1 }` (OCaml-style).
- If a self-reference is declared without a type annotation, e.g. `trait [self] implements Sig`, the type of `self` defaults to `Sig` instead of `Top`.

## 0.1.3

- [Experimental] iso-recursive types with nominal unfoldings; see examples [here](examples/isorecursive.cp) for implicit foldings and [there](examples/mutype.cp) for explicit ones.
- [New] polymorphic record updates, e.g. `{ rcd | x = 1; y = 2 }`.
- [New] default values for record wildcards, e.g. `(Ctor { z = 0; .. }.method = ……`.
- Implicit self-type annotations (introduced in 0.1.2) are removed. Instead, self-references can be declared without type annotations, e.g. `[self]`, whose type will be inferred.
- An uppercase variable should be prefixed with `$`, or it is regarded as a constructor invocation with `new` inserted.

## 0.1.2

- [New] default patterns, e.g. `_.method = ……`.
- [New] record wildcards for method patterns, e.g. `(Ctor {..}).method = ……`.
- The delimiter for documents is changed from triple quotes (`"""doc"""`) to backticks (`` `doc` ``), for the sake of parsing performance.
- The type checking of if-then-else is relaxed slightly: if one branch returns a supertype of the other, then that type is inferred.
- `[self : In & Out]` is implicitly added to method patterns if a trait family implements `Sig<In => Out>` (suggested by an anonymous reviewer from TOPLAS).
- The delimiter for input/output parts in trait types and sorts is changed from `%` to `=>` (suggested by @JimmyZJX).

## 0.1.1

- [New] an embedded document DSL, e.g. `"""Zor\Emph[doc]"""`.
- [New] open directives (currently implemented as C-style `#include`), e.g. `open lib;`.
- Built-in `List` (a linked list) is replaced by JavaScript-based `Array`; see the [example](examples/array.cp).
- Implemented call-by-need evaluation via JS FFI.

## 0.1.0

Initial version of Next-Gen CP; most functionalities of CP are reimplemented.

## Appendix: Syntactic Differences from the Original CP

- The merge operator is simplified from double commas (`,,`) to a single comma (`,`). Meanwhile, the delimiter for record fields and array elements is always semicolon (`;`) instead of comma (`,`).
- `new` is automatically inserted when constructors are invoked. In other words, `Ctor x y` is equivalent to `new $Ctor x y` now.
- `Trait[T]` is now `Trait<T>`, which is short for `Trait<T => T>` instead of `Trait<Top => T>`.
- `Trait[I, O]` is now `Trait<I => O>`.
- `Sig<I1 % O1, I2 % O2>` is now `Sig<I1 => O1><I2 => O2>`.
- The syntax of object self-type annotations is changed from `(Ctor x [self : T])` to `[self : T]@(Ctor x)`.
- The keyword `extends` is removed: `type A extends B = C` can be rewritten as `type A = B & C`.
- `number.toString` is now `toString number`.
- The exclusion operator is changed from a single backslash (`\`) to double backslashes (`\\`), e.g. `e1\\T1 , e2\\T2`.
- Type annotations have the lowest priority now. For example, the parentheses in `{} , (ctx:Context)` are necessary.
- The value `()` is no longer typed `Top` but a unit type `()`. An empty record `{}` is now allowed and typed `Top`.
