# Compositional Embeddings of Domain-Specific Languages (Artifact)

This is the artifact of the OOPSLA'22 paper *Compositional Embeddings of Domain-Specific Languages*. The artifact contains an in-browser interpreter of the <abbr title="Compositional Programming">CP</abbr> language with support for the <abbr title="Extensible Typesetting">ExT</abbr> DSL. The code examples and applications mentioned in the paper are also included.

You can always check [github.com/yzyzsun/CP-next](https://github.com/yzyzsun/CP-next) for the up-to-date version and build from source.

## Online Demo

[PLGround.org](https://plground.org) provides an online interpreter and a wiki-like document repository. Documents are written in ExT and rendered in your web browser.

Since the frontend code uses the Fetch API, PLGround is expected to work on Chrome 42+, Firefox 39+, Edge 14+, Safari 10.1+, or other modern browsers.

## Docker Images

If you prefer to run CP programs using a CLI or start a PLGround server locally, the most accessible way is to use the Docker images.

### CLI

To start a CP REPL via Docker, please run the following command:

```
docker run -it yzyzsun/cp-next
```

In the REPL, you can load CP programs using commands like `:load examples/calc.cp` or switch to other evaluation modes using commands like `:mode StepTrace`.

To run a test suite that checks all of `examples/*.cp`, please run `spago test` in the shell inside the Docker container; or simply run in your terminal:

```
docker run -it yzyzsun/cp-next spago test
```

### PLGround

To start a local server for PLGround, please specify the tag `plground`:

```
docker run -p 3000:3000 -it yzyzsun/cp-next:plground
```

Then you can visit PLGround at [127.0.0.1:3000](http://127.0.0.1:3000) on your browser. The website is preloaded with the code examples and applications mentioned in the paper:

1. The main example: Region DSL;
2. Extra demo of transformation: CSE;
3. Application #1: Minipedia;
4. Application #2: Fractals;
5. Application #3: Charts.

Since the paper does not perform any quantitative evaluation, there is no experimental data to be reproduced. Instead, you can click the [Render] button on each page to check that all code can type check and produce human-readable outputs.
