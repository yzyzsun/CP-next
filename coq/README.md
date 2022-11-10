### Prerequisites for building from scratch

- Coq **8.14.1**. The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.14.1).

- [Metalib](https://github.com/plclub/metalib) for the locally nameless
  representation. You can down the code from GitHub and install the library locally.
  We use the latest verison `be0f81c`.

  ```
  git clone https://github.com/plclub/metalib
  cd metalib/Metalib
  git checkout be0f81c
  make install
  ```

  Or use opam to install it:

  ```
  opam update
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  opam install coq-metalib
  ```

- [LibTactics.v](https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html)
  by Arthur Chargueraud. The file is included in the artifact.

- [Ott 0.31](https://github.com/ott-lang/ott/releases/tag/0.31) and
  [LNgen coq-8.10](https://github.com/plclub/lngen/releases/tag/coq-8.10).

  `Ott` and `LNgen` are used to generate some Coq code from `spec/rules.ott`.
   You can run all code without them installed unless you want to modify the
   Ott definitions and generate the coq files.

   Ott can be installed via opam, just replace the last line in the above commands
   for Metalib by:

  ```
  opam install ott.0.31
  ```

   For LNgen, one option is to use cabal to build and install it:

  ```
  curl -LJO https://github.com/plclub/lngen/archive/refs/tags/coq-8.10.zip
  unzip lngen-coq-8.10.zip
  cd lngen-coq-8.10
  cabal new-build
  cabal new-install
  ```

   Cabal can be installed via [GHCup](https://www.haskell.org/ghcup/). Note that
   you need to adjust your PATH variable (you can follow the interactive instructions).

   You can also use stack to install LNgen(instruction [here](https://github.com/plclub/lngen)).

### Sanity-testing

To compile the proofs:

1. Enter [coq](./coq) directory.

2. Type `make` in the terminal to build and compile the proofs.

3. You should see something like the following (suppose `>` is the prompt):

   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQDEP VFILES
   COQC LibTactics.v
   ```

### Proof Structure

- [spec/](./spec) for the Ott specification (that is used to generate the syntax
  definition in Coq)

- [coq/](./coq) for the Coq formalization
