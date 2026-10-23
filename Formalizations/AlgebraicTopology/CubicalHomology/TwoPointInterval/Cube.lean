import Formalizations.Topology.ClosureSpace.Product

/-!
# Singular cubes for the two-point intervals

The two-point intervals are `J₁`, in which each point lies in the closure of the other, and `J₊`,
in which `1` lies in the closure of `0` but not conversely. The `n`-cube `J^{⊡ n}` is the `n`-fold
inductive product, and a singular `n`-cube in a closure space `X` is a continuous map
`J^{⊡ n} → X`. For `J₁` these are the maps `σ` from the corners `Fin n → Bool` such that corners
differing in one coordinate go to points in each other's closures (`IsCube`); for `J₊` the
condition is required only along edges oriented from `0` to `1` (`IsPlusCube`). On a symmetric
closure space the two conditions agree.

## Main definitions

* `ClosureSpace.IsCube`, `ClosureSpace.IsPlusCube`: the cube conditions.
* `ClosureSpace.J1`, `ClosureSpace.Jplus`: the two-point intervals.
* `ClosureSpace.cubeSp J n`: the inductive product `J^{⊡ n}`.

## Main statements

* `ClosureSpace.isCube_iff_continuous`, `ClosureSpace.isPlusCube_iff_continuous`: the cube
  conditions are continuity on `J₁^{⊡ n}` and on `J₊^{⊡ n}` ([DT], (2) and (3)).
* `ClosureSpace.isCube_iff_isPlusCube`: on a symmetric closure space the two conditions agree
  ([DT], Lemma 1).

## References

* P. Bubenik and N. Milićević, *Homotopy, homology, and persistent homology using closure
  spaces*, J. Appl. Comput. Topol. 8 (2024), 579-641.
* [DT] T. Dube and A. Tregub, *Excision fails for inductive-product cubical homology of closure
  spaces*.
-/

namespace ClosureSpace

noncomputable section

variable {X : Type*}

/-! ## Cubes -/

/-- Change coordinate `i` of a corner. -/
def flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

@[simp] theorem flipAt_apply_self {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipAt x i i = !x i := by
  simp [flipAt]

theorem flipAt_apply_ne {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (h : j ≠ i) :
    flipAt x i j = x j := by
  simp [flipAt, Function.update_of_ne h]

@[simp] theorem flipAt_flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipAt (flipAt x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · rw [flipAt_apply_ne _ h, flipAt_apply_ne _ h]

/-- A `(J₁, ⊡)` singular cube: neighbouring corners go to points in each other's closures.
Since `flipAt` is an involution, the condition holds in both directions along every edge. -/
def IsCube (C : ClosureSpace X) {n : ℕ} (σ : (Fin n → Bool) → X) : Prop :=
  ∀ x i, σ (flipAt x i) ∈ C.cl {σ x}

/-- A `(J₊, ⊡)` singular cube: the condition is required only along edges oriented from `0` to `1`. -/
def IsPlusCube (C : ClosureSpace X) {n : ℕ} (σ : (Fin n → Bool) → X) : Prop :=
  ∀ x i, x i = false → σ (flipAt x i) ∈ C.cl {σ x}

/-- On a symmetric closure space the directed and undirected intervals give the same cubes. -/
theorem isCube_iff_isPlusCube {C : ClosureSpace X}
    (hsymm : ∀ x y, y ∈ C.cl {x} → x ∈ C.cl {y}) {n : ℕ} (σ : (Fin n → Bool) → X) :
    C.IsCube σ ↔ C.IsPlusCube σ := by
  constructor
  · intro h x i _
    exact h x i
  · intro h x i
    cases hx : x i
    · exact h x i hx
    · have h' := h (flipAt x i) i (by simp [hx])
      rw [flipAt_flipAt] at h'
      exact hsymm _ _ h'

/-! ## The cubes `J^{⊡ n}` -/

/-- The undirected two-point interval: each point lies in the closure of the other. -/
def J1 : ClosureSpace Bool := ofRel (fun _ _ => True) (fun _ => trivial)

/-- The directed two-point interval: `true ∈ cl {false}` but `false ∉ cl {true}`. -/
def Jplus : ClosureSpace Bool :=
  ofRel (fun a b => a = b ∨ (a = false ∧ b = true)) (by intro a; exact Or.inl rfl)

/-- The `n`-fold inductive product `J ⊡ ⋯ ⊡ J`, built as `J ⊡ J^{⊡ n}` and transported along
the bijection `x ↦ (x 0, Fin.tail x)` (`Fin.consEquiv`). -/
def cubeSp (J : ClosureSpace Bool) : (n : ℕ) → ClosureSpace (Fin n → Bool)
  | 0 => ofRel (fun _ _ => True) (fun _ => trivial)
  | n + 1 => comap (fun x : Fin (n + 1) → Bool => (x 0, Fin.tail x)) (indProd J (cubeSp J n))

/-- Corners that are equal or neighbors. -/
def nbr {n : ℕ} (x y : Fin n → Bool) : Prop := x = y ∨ ∃ i, y = flipAt x i

/-- Corners that are equal, or where `y` raises one coordinate of `x` from `false` to `true`. -/
def upNbr {n : ℕ} (x y : Fin n → Bool) : Prop := x = y ∨ ∃ i, x i = false ∧ y = flipAt x i

theorem nbr_refl {n : ℕ} (x : Fin n → Bool) : nbr x x := Or.inl rfl

theorem upNbr_refl {n : ℕ} (x : Fin n → Bool) : upNbr x x := Or.inl rfl

theorem eq_iff_head_tail {n : ℕ} {x y : Fin (n + 1) → Bool} :
    x = y ↔ x 0 = y 0 ∧ Fin.tail x = Fin.tail y := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, h0, ht]

theorem flipAt_zero_tail {n : ℕ} (x : Fin (n + 1) → Bool) :
    Fin.tail (flipAt x 0) = Fin.tail x := by
  funext j
  exact flipAt_apply_ne x (Fin.succ_ne_zero j)

theorem flipAt_succ_head {n : ℕ} (x : Fin (n + 1) → Bool) (i : Fin n) :
    flipAt x i.succ 0 = x 0 :=
  flipAt_apply_ne x (Fin.succ_ne_zero i).symm

theorem flipAt_succ_tail {n : ℕ} (x : Fin (n + 1) → Bool) (i : Fin n) :
    Fin.tail (flipAt x i.succ) = flipAt (Fin.tail x) i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Fin.tail]
  · rw [Fin.tail, flipAt_apply_ne _ (fun e => h (Fin.succ_injective _ e)), flipAt_apply_ne _ h,
      Fin.tail]

theorem nbr_succ {n : ℕ} (x y : Fin (n + 1) → Bool) :
    nbr x y ↔ (x 0 = y 0 ∧ nbr (Fin.tail x) (Fin.tail y)) ∨ (Fin.tail x = Fin.tail y ∧ True) := by
  constructor
  · rintro (rfl | ⟨i, rfl⟩)
    · exact Or.inr ⟨rfl, trivial⟩
    · cases i using Fin.cases with
      | zero => exact Or.inr ⟨(flipAt_zero_tail x).symm, trivial⟩
      | succ i => exact Or.inl ⟨(flipAt_succ_head x i).symm, Or.inr ⟨i, flipAt_succ_tail x i⟩⟩
  · rintro (⟨h0, ht | ⟨i, hi⟩⟩ | ⟨ht, -⟩)
    · exact Or.inl (eq_iff_head_tail.mpr ⟨h0, ht⟩)
    · refine Or.inr ⟨i.succ, eq_iff_head_tail.mpr ⟨?_, ?_⟩⟩
      · rw [flipAt_succ_head, h0]
      · rw [flipAt_succ_tail, hi]
    · by_cases h0 : x 0 = y 0
      · exact Or.inl (eq_iff_head_tail.mpr ⟨h0, ht⟩)
      · refine Or.inr ⟨0, eq_iff_head_tail.mpr ⟨?_, ?_⟩⟩
        · rw [flipAt_apply_self]
          cases hx : x 0 <;> cases hy : y 0 <;> simp_all
        · rw [flipAt_zero_tail, ht]

theorem upNbr_succ {n : ℕ} (x y : Fin (n + 1) → Bool) :
    upNbr x y ↔ (x 0 = y 0 ∧ upNbr (Fin.tail x) (Fin.tail y)) ∨
      (Fin.tail x = Fin.tail y ∧ (x 0 = y 0 ∨ (x 0 = false ∧ y 0 = true))) := by
  constructor
  · rintro (rfl | ⟨i, hxi, rfl⟩)
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
    · cases i using Fin.cases with
      | zero =>
          refine Or.inr ⟨(flipAt_zero_tail x).symm, Or.inr ⟨hxi, ?_⟩⟩
          rw [flipAt_apply_self, hxi]
          rfl
      | succ i =>
          exact Or.inl ⟨(flipAt_succ_head x i).symm, Or.inr ⟨i, hxi, flipAt_succ_tail x i⟩⟩
  · rintro (⟨h0, ht | ⟨i, hxi, hi⟩⟩ | ⟨ht, h0 | ⟨hx0, hy0⟩⟩)
    · exact Or.inl (eq_iff_head_tail.mpr ⟨h0, ht⟩)
    · refine Or.inr ⟨i.succ, hxi, eq_iff_head_tail.mpr ⟨?_, ?_⟩⟩
      · rw [flipAt_succ_head, h0]
      · rw [flipAt_succ_tail, hi]
    · exact Or.inl (eq_iff_head_tail.mpr ⟨h0, ht⟩)
    · refine Or.inr ⟨0, hx0, eq_iff_head_tail.mpr ⟨?_, ?_⟩⟩
      · rw [flipAt_apply_self, hx0, hy0]
        rfl
      · rw [flipAt_zero_tail, ht]

/-- `J₁^{⊡ n}` is the closure of the neighbor relation. -/
theorem cubeSp_J1 : ∀ n, cubeSp J1 n = ofRel (@nbr n) nbr_refl
  | 0 => ofRel_congr fun x y => ⟨fun _ => Or.inl (Subsingleton.elim x y), fun _ => trivial⟩
  | n + 1 => by
      rw [cubeSp, cubeSp_J1 n, J1, indProd_ofRel, comap_ofRel]
      exact ofRel_congr fun x y => (nbr_succ x y).symm

/-- `J₊^{⊡ n}` is the closure of the raising relation. -/
theorem cubeSp_Jplus : ∀ n, cubeSp Jplus n = ofRel (@upNbr n) upNbr_refl
  | 0 => ofRel_congr fun x y => ⟨fun _ => Or.inl (Subsingleton.elim x y), fun _ => trivial⟩
  | n + 1 => by
      rw [cubeSp, cubeSp_Jplus n, Jplus, indProd_ofRel, comap_ofRel]
      exact ofRel_congr fun x y => (upNbr_succ x y).symm

/-- The `(J₁, ⊡)` singular cubes are the maps satisfying `IsCube` ([DT], (2)). -/
theorem isCube_iff_continuous (C : ClosureSpace X) {n : ℕ} (σ : (Fin n → Bool) → X) :
    C.IsCube σ ↔ (cubeSp J1 n).ContinuousMap C σ := by
  rw [cubeSp_J1, continuousMap_ofRel]
  constructor
  · rintro h x y (rfl | ⟨i, rfl⟩)
    · exact C.subset_cl _ rfl
    · exact h x i
  · intro h x i
    exact h x _ (Or.inr ⟨i, rfl⟩)

/-- The `(J₊, ⊡)` singular cubes are the maps satisfying `IsPlusCube` ([DT], (3)). -/
theorem isPlusCube_iff_continuous (C : ClosureSpace X) {n : ℕ} (σ : (Fin n → Bool) → X) :
    C.IsPlusCube σ ↔ (cubeSp Jplus n).ContinuousMap C σ := by
  rw [cubeSp_Jplus, continuousMap_ofRel]
  constructor
  · rintro h x y (rfl | ⟨i, hi, rfl⟩)
    · exact C.subset_cl _ rfl
    · exact h x i hi
  · intro h x i hi
    exact h x _ (Or.inr ⟨i, hi, rfl⟩)

end

end ClosureSpace
