# formalizations

Lean 4 formalizations of the results in papers by Taksch Dube (Kent State University). Each paper has its own Lean library in this repository and is cited by a git tag and a Zenodo DOI minted from that tag.

## Papers

| Paper | MSC 2020 | Library | Tag | DOI |
|---|---|---|---|---|

## Layout

- One Lake package and one Mathlib version for all papers, currently Lean 4 v4.33.1 with Mathlib v4.33.1.
- One `lean_lib` per paper, in the folder of the same name.
- `scripts/<paper>/` holds the paper's axiom check `check_axioms.lean` and any other script the paper cites.
- Fields are recorded as MSC codes in the table above, primary first, not as folders. Definitions that a second paper needs move into a subject folder, such as `ClosureSpace/`, which both libraries import.
- A paper's tag (`<paper>-v1`, then `-v2` for a revision) never moves. Later Mathlib upgrades on `main` do not change the code a paper cites.

## Building

    lake exe cache get
    lake build
    lake env lean scripts/<paper>/check_axioms.lean

Each statement in a `check_axioms.lean` depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. CI checks this on every pull request and builds with warnings as errors, so a `sorry` fails the build.
