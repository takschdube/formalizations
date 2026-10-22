# Excision fails for inductive-product cubical homology of closure spaces

Taksch Dube and Alexander Tregub. MSC 2020: 55N35 (primary); 54A05, 05C10, 68V20.

Release `closure-space-excision-v1`. Statement numbers are the paper's; each kind of statement is numbered separately.

| File | Contents |
| :--- | :--- |
| `Basic.lean` | Closure spaces, interiors, closures of reflexive relations. |
| `Cubes.lean` | (J1, box) cubes and chains; Theorem 1 for J1, Lemma 1, Theorem 4, Lemma 2, Proposition 1. |
| `Q3.lean` | Theorem 2 (interior cover of the 3-cube graph) for J1. |
| `Interval.lean` | (I, box) and (I, x) paths, squares and chains; Lemmas 3 and 4, Theorem 3 (a) for the six-cycle and (b). |
| `Winding.lean` | A winding number for maps into the six-cycle, which vanishes on boundaries of jointly continuous squares (Lebesgue number); Theorem 3 (c). |
| `DegreeOne.lean` | Proposition 2 (excision fails in degree one when two points are joined in A and in B but not in their intersection) and Theorem 3 (a) for the circle. |
| `Bridge.lean` | Cech continuity, product and inductive product closures, and the equivalence of conditions (1) to (3) with continuity. |
| `PlusTransfer.lean` | The (J+, box) chain groups agree with the (J1, box) ones on symmetric spaces; Theorems 1 and 2 for the directed interval. |

Scripts in [`scripts/closure-space-excision/`](../scripts/closure-space-excision):

| Script | Contents |
| :--- | :--- |
| `check_axioms.lean` | The axiom check for the formalized statements. |
| `q3_homology.py` | Exact enumeration of the singular cubes of Q3 up to dimension 3 and the ranks in Remark 3 (mod 2^31 - 1). Run with `python3 scripts/closure-space-excision/q3_homology.py`. |
