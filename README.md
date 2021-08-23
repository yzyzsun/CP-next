# Zord

Zord is a *compositional programming* language. It is founded on a core calculus named *Fi+*. The definitional interpreter is implemented in [PureScript](https://www.purescript.org) (a Haskell-like language that compiles to JavaScript).

## Language Features

- A typed lambda calculus with six base types (`Int` `Double` `String` `Bool` `Top` `Bot`), built-in arrays (`[1; 2; 3] : [Int]`), and some built-in operations over them;
- A merge operator [^Merge], disjoint intersection types [^λi] and polymorphism [^Fi];
- Nested composition and distributive subtyping [^NeColus];
- Object-oriented programming à la first-class traits [^SEDEL];
- Compositional interfaces, virtual constructors, method patterns, and nested trait composition [^CP];
- Type-directed operational semantics [^TDOS] for *Fi+* with {substitution,closure,HOAS}-based {big,small}-step variants.

[^Merge]: Jana Dunfield. [Elaborating Intersection and Union Types](https://research.cs.queensu.ca/home/jana/papers/intcomp-jfp/Dunfield14_elaboration.pdf). In *JFP 2014*.  
[^λi]: Bruno C. d. S. Oliveira, Zhiyuan Shi, and João Alpuim. [Disjoint Intersection Types](https://i.cs.hku.hk/~bruno/papers/icfp2016.pdf). In *ICFP 2016*.  
[^Fi]: João Alpuim, Bruno C. d. S. Oliveira, and Zhiyuan Shi. [Disjoint Polymorphism](https://i.cs.hku.hk/~bruno/papers/ESOP2017.pdf). In *ESOP 2017*.  
[^SEDEL]: Xuan Bi and Bruno C. d. S. Oliveira. [Typed First-Class Traits](https://i.cs.hku.hk/~bruno/papers/traits.pdf). In *ECOOP 2018*.  
[^NeColus]: Xuan Bi, Bruno C. d. S. Oliveira, and Tom Schrijvers. [The Essence of Nested Composition](https://i.cs.hku.hk/~bruno/papers/nested.pdf). In *ECOOP 2018*.  
[^Fi+]: Xuan Bi, Ningning Xie, Bruno C. d. S. Oliveira and Tom Schrijvers. [Distributive Disjoint Polymorphism for Compositional Programming](https://i.cs.hku.hk/~bruno/papers/esop2019.pdf). In *ESOP 2019*.  
[^CP]: Weixin Zhang, Yaozhu Sun, and Bruno C. d. S. Oliveira. [Compositional Programming](https://i.cs.hku.hk/~bruno/papers/toplas2021.pdf). In *TOPLAS 2021*.  
[^TDOS]: Xuejing Huang, Jinxu Zhao, and Bruno C. d. S. Oliveira. [Taming the Merge Operator](https://i.cs.hku.hk/~bruno/papers/jfp2021.pdf). In *JFP 2021*.  

## Setup

- First of all, you need to install [Node.js](https://nodejs.org).
- Then execute `npm install` to get all of the dev dependencies.
- After installation, you can choose either of the following npm scripts:
  - `npm start` to run a Zord REPL;
  - `npm test` to run a test suite checking `examples/*.zord`.

## REPL Example

```
$ npm start
...
Zord REPL, version x.x.x (press Ctrl-C to quit)

> :load examples/bench.zord
832
<BigStep mode: 0.198s>

> :mode StepTrace

> 1+2*3
(1 + (2 * 3))
→ Step-BinaryR
↓ Step-BinaryV
(1 + 6)
↓ Step-BinaryV
7
<StepTrace mode: 0.021s>
```

## PLGround

[PLGround.org](https://plground.org) provides an open document repository. Documents are written in Zordoc (a DSL embedded in Zord) and rendered with an in-browser interpreter. It is integrated with a [CodeMirror 6](https://codemirror.net/6/) editor with syntax highlighting. Its grammar file written in [Lezer](https://lezer.codemirror.net) can be found at [zord.grammar](zord.grammar).

Since the frontend code uses the Fetch API, PLGround is expected to work on Chrome 42+, Firefox 39+, Edge 14+, Safari 10.1+, or other modern browsers.

If you want to start a web server locally, [Ruby](https://www.ruby-lang.org) is needed. Besides, execute `bundle install` to get [Ruby on Rails](https://rubyonrails.org) and other gems. Finally, execute `npm run server` to start a web server. (If you changed the frontend code, PureScript included, please execute `npm run build` to update `backend/app/assets/javascripts/bundle.js`.)

## VS Code Extension

Zord Language Support can be found on [VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=yzyzsun.zord). This extension provides basic support for syntax highlighting. [Extension API](https://code.visualstudio.com/api) should be useful for further development.

If you want to build it from scratch, please execute `npm run vscode`. Then a `.vsix` file will be generated in `vscode/`.

## Zord versus CP

If you have read our TOPLAS paper *Compositional Programming*, you may wonder about the relation between Zord and CP. In fact, CP may refer to two things: one is the language design specified in the paper, the other is the reference implementation included in the [artifact](https://github.com/wxzh/CP). Zord is a brand-new implementation for our extension of the CP language and can be regarded as the successor of the original implementation.

Concerning implementation languages, CP is written in Haskell, while Zord is written in PureScript. Thus, Zord can easily run in a web browser without losing the ability to run traditionally in a terminal. From a perspective of semantics, the core calculus *Fi+* is further elaborated to *F-co* in CP but has direct operational semantics in Zord. Furthermore, new features recently added and some syntactic differences can be found at [CHANGELOG.md](CHANGELOG.md).

## Naming

The name [*Zord*](https://powerrangers.fandom.com/wiki/Category:Zords) comes from the television series *Power Rangers*. Zords are giant robots piloted by superheroes, which can join together into a more powerful humanoid Megazord. It is used as a metaphor for compositional programming.
