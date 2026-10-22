<div align="center">

# Formalizations

Lean 4 formalizations of research papers in mathematics

[![CI](https://github.com/takschdube/formalizations/actions/workflows/ci.yml/badge.svg)](https://github.com/takschdube/formalizations/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.33.1-2563eb)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.33.1-7c3aed)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache--2.0-0d9488)](LICENSE)

</div>

## Goal

This repository collects the Lean 4 formalizations of papers by Taksch Dube and coauthors. The aim is a body of research mathematics in which every result is checked by machine and each new paper builds on the checked work of earlier ones. A paper joins the library on the day it is posted, formalized in full: every theorem, proposition and lemma. Its definitions remain available to later papers, so the library extends into each area of mathematics that the papers reach.

## Organization

```mermaid
%%{init: {"flowchart": {"wrappingWidth": 400}}}%%
flowchart TB
    P["<b>Paper libraries</b><br/>one per paper, frozen at its release"]
    S["<b>Subject libraries</b><br/>definitions shared by several papers"]
    M["<b>Mathlib</b><br/>general formalized mathematics"]
    P --> S --> M
    classDef paper fill:#dbeafe,stroke:#2563eb,color:#1e3a8a
    classDef subject fill:#ede9fe,stroke:#7c3aed,color:#4c1d95
    classDef base fill:#ccfbf1,stroke:#0d9488,color:#134e4a
    class P paper
    class S subject
    class M base
```

Each layer imports the ones below it.

- **Paper libraries.** Each paper is a Lean library in the folder of the same name, with a README that maps the paper's statements to files. A paper cites its release, the tag `<paper>-v1`, which never moves, so Mathlib upgrades on `main` do not change the code a paper cites.
- **Subject libraries.** A definition that a second paper needs moves out of the first paper's library into a subject library that both import. Results of general use can move on into Mathlib, which is why this library uses Mathlib's license.
- **Checks.** CI builds every library with warnings as errors, so an unfinished proof fails the build, and checks that each formalized statement depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Papers

| Paper | Release |
| :--- | :--- |
| [Excision fails for inductive-product cubical homology of closure spaces](ClosureExcision) | `closure-space-excision-v1` |

## Building

```sh
git clone https://github.com/takschdube/formalizations.git
cd formalizations
lake exe cache get    # compiled Mathlib, several GB
lake build
lake env lean scripts/closure-space-excision/check_axioms.lean
```

To build the code a paper cites, check out its release first:

```sh
git checkout closure-space-excision-v1
```

## Citing

```bibtex
@misc{formalizations,
  author       = {Dube, Taksch},
  title        = {Lean 4 formalizations},
  howpublished = {GitHub repository, \url{https://github.com/takschdube/formalizations}},
  year         = {2026}
}
```

## License

Apache License 2.0, the license of Mathlib. See [LICENSE](LICENSE).
