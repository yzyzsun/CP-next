# The Zord Programming Language

Zord is a functional programming language that advocates compositional programming. It is implemented using [PureScript](https://www.purescript.org) (a Haskell-like language that compiles to JavaScript).

## Setup

- First of all, you need to install [Node.js](https://nodejs.org).
- Then execute `npm install` to get all of the dev dependencies.
- After installation, you can choose any of the following npm scripts:
  - `npm start` to run a Zord REPL;
  - `npm test` to run a test suite checking `examples/*.zord`;
  - `npm run vscode` to package the VS Code extension into a VSIX file;
  - `npm run lezer` to generate an LR parser for the online code editor;
  - `npm run build` to pack all scripts needed by PL Ground to `dist/bundle.js`;
  - `npm run dev` to start a webpack dev server providing live reloading.

## Online Demo

[PL Ground](https://plground.org) provides an in-browser interpreter for Zord. It is integrated with a CodeMirror editor with syntax highlighting. Its grammar file written in Lezer can be found at `plground/zord.grammar`.

If you want to build it from scratch, please follow the setup instructions above.

## Naming

The name [*Zord*](https://powerrangers.fandom.com/wiki/Category:Zords) comes from the television series *Power Rangers*. Zords are giant robots piloted by superheroes, which can join together into a more powerful humanoid Megazord. It is used as a metaphor for compositional programming.
