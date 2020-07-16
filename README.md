# The Zord Programming Language

## Setup

- First of all, you need to install [Node.js](https://nodejs.org).
- Then the PureScript compiler and its build tool Spago can be installed globally via `npm`:

```sh
$ npm install -g purescript spago
```

- After installation, you can run the Zord interpreter via Spago:

```sh
$ spago run
```

## PL Ground

[PL Ground](https://plground.org) provides an online interpreter for Zord. It is integrated with a CodeMirror editor with syntax highlighting. If you want to build it from scratch, the following command will install dev dependencies and invoke `webpack` to bundle all of the required scripts.

```sh
$ npm install && npm run build
```

The generated `bundle.js` can be found in the `dist` directory; meanwhile, `index.html` is copied to the same directory for convenience.

## Naming

The name [*Zord*](https://powerrangers.fandom.com/wiki/Category:Zords) comes from the television series *Power Rangers*. Zords are the giant robots piloted by superheroes, which can join together into a more powerful humanoid Megazord. It is used as a metaphor for compositional programming.

For your information, the predecessors of the Zord programming language are called *SEDEL* and *CP* in earlier papers.
