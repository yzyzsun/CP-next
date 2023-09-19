### Prerequisites for building from scratch

- Coq **8.16.1**. The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.16.1).

- [Metalib](https://github.com/plclub/metalib) for the locally nameless
  representation. You can down the code from GitHub and install the library locally.
  We use the latest verison `4ea92d8`.

  ```
  git clone https://github.com/plclub/metalib
  cd metalib/Metalib
  git checkout 4ea92d8
  make install
  ```

  Or use [OPAM](https://opam.ocaml.org/doc/Install.html) to install it:

  ```
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  opam install coq-metalib
  ```
- [StructTact](https://github.com/uwplse/StructTact) for defining orders on strings.
   It can be install via [OPAM](https://opam.ocaml.org/doc/Install.html) or download from GitHub.

   ```shell
   opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
   opam install coq-struct-tact
   ```

  - [LibTactics.v](https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html)
  by Arthur Chargueraud. The file provides some general tactics. It is included in the artifact.

- [Ott 0.31](https://github.com/ott-lang/ott/releases/tag/0.31) (Ott 0.32 is not
yet supported by LNgen)

- [LNgen coq-8.10](https://github.com/plclub/lngen/releases/tag/coq-8.10).

  `Ott` and `LNgen` are used to generate some Coq code from
  [spec/rules.ott](./spec/rules.ott) and [spec/target.ott](./spec/target.ott)
   You can run all code without them installed unless you want to modify the
   Ott definitions and generate the coq files.

   Ott can be installed via [OPAM](https://opam.ocaml.org/doc/Install.html):

  ```
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
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

3. You should see something like the following:

   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQDEP VFILES
   COQC LibTactics.v
   ```

To generate `syntax_ott.v`, `rules_inf.v` and `rules_inf2.v`.

1. Delete the old generated files or
edit [spec/rules.ott](./spec/rules.ott) or [spec/target.ott](./spec/target.ott).
They are for the source calculus and the target calculus respectively.

2. Run `make` to generate [coq/syntax.ott](./coq/syntax.ott).

3. Edit [coq/syntax_ott.v](./coq/syntax_ott.v) to manually solve the errors. It will complain
`rec_typ` is not defined before its first occurrence in `subTarget`. Please move the definition of
`rec_typ` before the definition of `subTarget`.

4. Run `make` again to generate [coq/rules_inf.v](./coq/rules_inf.v) and [coq/rules_inf2.v](./coq/rules_inf2.v).


### Proof Structure

- [spec/](./spec) for the Ott specification (that is used to generate the syntax
  definition in Coq)

- [coq/](./coq) for the Coq formalization.

+  [syntax_ott.v](./coq/syntax_ott.v) contains the definitions.

+  [rules_inf.v](./coq/rules_inf.v) and [coq/rules_inf2.v](./coq/rules_inf2.v)
are the locally nameless representation related lemmas.

+ [Infrastructure.v](./coq/Infrastructure.v) contains the notation definitions and
auxiliary tactics.

+  [TargetTypeSafety.v](./coq/TargetTypeSafety.v) contains the proofs in Section 3.1.

+  [Translation.v](./coq/Translation.v) contains the proofs about translation
functions that is introduced at the beginning of Section 3.2. The two admitted lemmas
are at the beginning of this file.

+  [ElaborationSoundness.v](./coq/ElaborationSoundness.v) contains the proofs
about the source type system which elaborates source terms to the target language.
It corresponds to the last paragraph of Section 3.2.
