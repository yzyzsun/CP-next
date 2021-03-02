# The Zord Programming Language

Zord is a functional programming language that advocates compositional programming. The interpreter is implemented in [PureScript](https://www.purescript.org) (a Haskell-like language that compiles to JavaScript).

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
Zord REPL, version 0.1.1 (press Ctrl-C to quit)

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

[PLGround.org](https://plground.org) provides a wiki-like document repository. Documents are written in Zord and rendered with an in-browser interpreter. It is integrated with a [CodeMirror 6](https://codemirror.net/6/) editor with syntax highlighting. Its grammar file written in [Lezer](https://lezer.codemirror.net) can be found at `zord.grammar`.

Since the frontend code uses the Fetch API, PLGround is expected to work on Chrome 42+, Firefox 39+, Edge 14+, Safari 10.1+, or other modern browsers.

If you want to start a web server locally, [Ruby](https://www.ruby-lang.org) is needed. Besides, execute `bundle install` to get [Ruby on Rails](https://rubyonrails.org) and other gems. Finally, execute `npm run server` to start a web server. (If you changed the frontend code, PureScript included, please execute `npm run build` to update `backend/app/assets/javascripts/bundle.js`.)

## VS Code Extension

Zord Language Support can be found on [VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=yzyzsun.zord). This extension provides basic support for syntax highlighting. [Extension API](https://code.visualstudio.com/api) should be useful for further development.

If you want to build it from scratch, please execute `npm run vscode`. Then a `.vsix` file will be generated in `vscode/`.

## Naming

The name [*Zord*](https://powerrangers.fandom.com/wiki/Category:Zords) comes from the television series *Power Rangers*. Zords are giant robots piloted by superheroes, which can join together into a more powerful humanoid Megazord. It is used as a metaphor for compositional programming.
