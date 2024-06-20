# Type-Safe Compilation of Dynamic Inheritance via Merging (Artifact)

This is the artifact of the TOPLAS journal-first submission *Type-Safe Compilation of Dynamic Inheritance via Merging*. The artifact consists of three parts:

- **Coq formalization:** see separate documentation in [theories/](./theories).
- **Compiler implementation:** the most important code is located at [src/CP/CodeGen.purs](./src/CP/CodeGen.purs), written in PureScript.
- **Benchmark suite:** [benchmarks/](./benchmarks) and [bench.sh](./bench.sh) for Section 7.1; [comparison/](./comparison) and [comp.sh](./comp.sh) for Section 7.2.

## How to Build the Compiler?

- First of all, you need to install [Node.js](https://nodejs.org). Note that our experiments were done using v20.12.2 LTS.
- Then execute `npm install` to install dev dependencies (i.e. PureScript, Spago, and TypeScript).
- After installation, you can choose either of the following npm scripts:
  - `npm start` to run a REPL, and then `:compile benchmarks/fib.cp` to compile and run a CP file;
  - `npm run compiler "benchmarks/*.cp"` to compile CP files to JavaScript.

## How to Run the Benchmarks?

We have automated benchmarks with `bench.sh` and `comp.sh`. Simply running them should show execution time for each benchmark and each variant:

```bash
$ ./bench.sh
[base]                                     # 1st variant (w/ all optim.) of CP compiler
[info] Build succeeded.                    # compiler is already built
benchmarks/color.lib compiled in 0.055s    # compilation time in blue (not used)
......
benchmarks/chart.cp.mjs: 516ms             # execution time (used in the paper)
......
[dps]                                      # 2nd variant (w/o DPS) of CP compiler
[1 of 4] Compiling Language.CP.CodeGen     # rebuilding compiler...
[2 of 4] Compiling Language.CP
[3 of 4] Compiling REPL
[4 of 4] Compiling Main
[info] Build succeeded.
......

$ ./comp.sh
comparison/fib.mjs: 2.423s                 # JavaScript version of fib
......
comparison/region_0.mjs: 1.513s            # JavaScript version of region^0
......
comparison/region_0.ts.js: 1.575s          # TypeScript version of region^0
......
[info] Build succeeded.
comparison/region_0.cp compiled in 0.117s  # compilation time in blue (not used)
......
comparison/region_0.cp.mjs: 1.137s         # CP version of region^0
......
```

For your reference, we also provide original data (in milliseconds) and gnuplot scripts in [plot/](./plot) that are used to draw Fig. 25 and Fig. 26 in the paper.

## Appendix

In the appendix of the paper, we show our compilation scheme from Fi+ to JavaScript. Those inference rules are generated using the [Ott](https://github.com/ott-lang/ott) tool. Please find the source files in [ott/](./ott) if you are interested.
