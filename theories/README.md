# Coq Formalization

This directory contains the Coq formalization of our compilation scheme.
The core of the formalization is an elaboration semantics from λ<sub>i</sub><sup>+</sup> to λ<sub>r</sub>.
We mechanically prove the type safety of the elaboration.

## How to Build?

The proofs are tested against [Coq 8.16.1](https://github.com/coq/coq/releases/tag/V8.16.1).
Note that Ott/LNgen may not work on newer versions of Coq.
The easiest way to install Coq 8.16.1 is using opam:

```
> opam pin add coq 8.16.1
```

[StructTact](https://github.com/uwplse/StructTact), [Metalib](https://github.com/plclub/metalib) and auxiliary files for Ott are required to build our code. You can also install them using opam:

```
> opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
> opam install coq-struct-tact coq-metalib coq-ott
```

After installing Coq and required libraries, you can execute `make` under the `coq/` subdirectory. A successful build would be like:

```
> cd coq
> make
......
coq_makefile -arg '-w -deprecated,-fragile-hint-constr' -f _CoqProject -o CoqSrc.mk
COQDEP VFILES
COQC LibTactics.v
COQC syntax_ott.v
COQC source_inf.v
COQC target_inf.v
COQC Infrastructure.v
COQC TargetTypeSafety.v
COQC Translation.v
COQC ElaborationSoundness.v
```

### Sidenote: Locally Nameless

Most locally nameless definitions and proofs are automatically generated.
The command line tools [Ott](https://github.com/ott-lang/ott) and [LNgen](https://github.com/plclub/lngen) are used to generate `coq/syntax_ott.v` and `coq/{source,target}_inf.v`.
You can build all Coq proofs without installing Ott/LNgen.

However, if you modify `ott/{source,target}.ott`, you need to regenerate those Coq files.
Simply executing `make all` instead of `make` should do the job.
But note that some manual work is needed to make `coq/syntax_ott.v` compile.
We apologize that we have not automated the modifications so far.

## Directory Structure

- [ott/](./ott) for the Ott specification, which is used to generate the locally nameless definitions and proofs in Coq.
- [coq/](./coq) for the Coq formalization.
  + [LibTactics.v](./coq/LibTactics.v) is borrowed from a chapter of [Software Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html).
  + [syntax_ott.v](./coq/syntax_ott.v) contains the locally nameless definitions.
  + [source_inf.v](./coq/source_inf.v) and [target_inf.v](./coq/target_inf.v) contain the locally nameless lemmas.
  + [Infrastructure.v](./coq/Infrastructure.v) contains the notation definitions and auxiliary tactics.
  + [TargetTypeSafety.v](./coq/TargetTypeSafety.v) proves the type soundness of the target calculus in Section 5.1.
  + [Translation.v](./coq/Translation.v) contains the proofs about translation functions at the beginning of Section 5.2.
  + [ElaborationSoundness.v](./coq/ElaborationSoundness.v) contains the proofs about the type-directed elaboration from the source calculus to the target calculus. It corresponds to the last paragraph of Section 5.2.

## Correspondence Guide

| Theorem in Paper                                | File                     | Name in Coq                                                                                          |
| ----------------------------------------------- | ------------------------ | ---------------------------------------------------------------------------------------------------- |
| Lemma 5.1 (Equivalent types in lookups)         | `TargetTypeSafety.v`     | `lookup_ST_eq_some` / `lookup_eq`                                                                    |
| Theorem 5.2 (Progress)                          | `TargetTypeSafety.v`     | `progress`                                                                                           |
| Lemma 5.3 (Substitution preserves typing)       | `TargetTypeSafety.v`     | `substitution_preserves_typing_relax`                                                                |
| Theorem 5.4 (Type preservation)                 | `TargetTypeSafety.v`     | `preservation`                                                                                       |
| Lemma 5.7 (Translation)                         | `Translation.v`          | `st_eq_arrow` / `st_eq_rcd`                                                                          |
| Lemma 5.8 (Equivalent types)                    | `Translation.v`          | `lookup_sub` / `eqIndTyp_sound_alt_gen` / `sub_source2target`                                        |
| Lemma 5.9 (Well-formedness of translated types) | `Translation.v`          | `ttyp_trans_wf`                                                                                      |
| Theorem 5.10 (Elaboration soundness)            | `ElaborationSoundness.v` | `cosub_well_typed` / `distapp_well_typed_app` / `distapp_well_typed_proj` / `elaboration_well_typed` |
