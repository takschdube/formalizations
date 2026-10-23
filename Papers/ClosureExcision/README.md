# Excision fails for inductive-product cubical homology of closure spaces

Taksch Dube and Alexander Tregub. MSC 2020: 55N35 (primary); 54A05, 05C10, 68V20.

Release `closure-space-excision-v1`. The general results of the paper are in the cubical homology area of the library, and this folder holds its three examples: the 3-cube graph, the six-cycle and the circle. Statement numbers are the paper's; each kind of statement is numbered separately. The Lean name of each statement is in Table 2 of the paper and in [`check_axioms.lean`](../../scripts/closure-space-excision/check_axioms.lean).

| Statement | File |
| :--- | :--- |
| Theorem 1 | [`TwoPointInterval/Excision.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/TwoPointInterval/Excision.lean); for the directed interval, [`TwoPointInterval/Directed.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/TwoPointInterval/Directed.lean) |
| Theorem 2 | [`Q3.lean`](Q3.lean) |
| Theorem 3 (a) | [`SixCycle.lean`](SixCycle.lean) for the six-cycle, [`Circle.lean`](Circle.lean) for the circle |
| Theorem 3 (b) | [`UnitInterval/Homology.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/UnitInterval/Homology.lean) |
| Theorem 3 (c) | [`Winding.lean`](Winding.lean) |
| Theorem 4 | [`TwoPointInterval/Excision.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/TwoPointInterval/Excision.lean) |
| Lemma 1 | [`TwoPointInterval/Cube.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/TwoPointInterval/Cube.lean) |
| Lemma 2 | [`TwoPointInterval/Excision.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/TwoPointInterval/Excision.lean) |
| Lemma 3 | [`UnitInterval/Homology.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/UnitInterval/Homology.lean) |
| Lemma 4 | [`UnitInterval/Path.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/UnitInterval/Path.lean), [`UnitInterval/Chain.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/UnitInterval/Chain.lean) |
| Proposition 1 | [`TwoPointInterval/Excision.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/TwoPointInterval/Excision.lean) |
| Proposition 2 | [`UnitInterval/Homology.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/UnitInterval/Homology.lean) |
| (1) | [`UnitInterval/Path.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/UnitInterval/Path.lean) |
| (2), (3) | [`TwoPointInterval/Cube.lean`](../../Formalizations/AlgebraicTopology/CubicalHomology/TwoPointInterval/Cube.lean) |

Scripts in [`scripts/closure-space-excision/`](../../scripts/closure-space-excision):

| Script | Contents |
| :--- | :--- |
| `check_axioms.lean` | The axiom check for the formalized statements. |
| `q3_homology.py` | Exact enumeration of the singular cubes of Q3 up to dimension 3 and the ranks in Remark 3 (mod 2^31 - 1). Run with `python3 scripts/closure-space-excision/q3_homology.py`. |
