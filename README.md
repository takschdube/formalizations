# formalizations

Lean 4 formalizations of the results in papers by Taksch Dube (Kent State University). Each paper has its own Lean library in this repository and is cited by a git tag and a Zenodo DOI minted from that tag.

## Papers

| Paper | MSC 2020 | Library | Tag | DOI |
|---|---|---|---|---|
| Excision fails for inductive-product cubical homology of closure spaces | 55N35 (primary), 54A05, 05C10, 68V20 | `ClosureExcision` | pending | pending |

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

## Excision fails for inductive-product cubical homology of closure spaces

Library `ClosureExcision`, scripts in `scripts/closure-space-excision/`. Statement numbers are the paper's; each kind of statement is numbered separately.

- `ClosureExcision/Basic.lean`: closure spaces, interiors, closures of reflexive relations.
- `ClosureExcision/Cubes.lean`: (J1, box) cubes and chains; Theorem 1 for J1, Lemma 1, Theorem 4, Lemma 2, Proposition 1.
- `ClosureExcision/Q3.lean`: Theorem 2 (interior cover of the 3-cube graph) for J1.
- `ClosureExcision/Interval.lean`: (I, box) and (I, x) paths, squares and chains; Lemmas 3 and 4, Theorem 3 (a) for the six-cycle and (b).
- `ClosureExcision/Winding.lean`: a winding number for maps into the six-cycle, which vanishes on boundaries of jointly continuous squares (Lebesgue number); Theorem 3 (c).
- `ClosureExcision/DegreeOne.lean`: Proposition 2 (excision fails in degree one when two points are joined in A and in B but not in their intersection) and Theorem 3 (a) for the circle.
- `ClosureExcision/Bridge.lean`: Cech continuity, product and inductive product closures, and the equivalence of conditions (1) to (3) with continuity.
- `ClosureExcision/PlusTransfer.lean`: the (J+, box) chain groups agree with the (J1, box) ones on symmetric spaces; Theorems 1 and 2 for the directed interval.
- `scripts/closure-space-excision/check_axioms.lean`: the axiom check for the formalized statements.
- `scripts/closure-space-excision/q3_homology.py`: exact enumeration of the singular cubes of Q3 up to dimension 3 and the ranks in Remark 3 (mod 2^31 - 1). Run with `python3 scripts/closure-space-excision/q3_homology.py`.
