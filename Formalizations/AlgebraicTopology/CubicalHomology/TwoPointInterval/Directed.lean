import Formalizations.AlgebraicTopology.CubicalHomology.TwoPointInterval.Excision

/-!
# The directed interval

The chain groups of the `(J₊, ⊡)` theory are built like those of the `(J₁, ⊡)` theory, with the
cube condition `IsPlusCube` in place of `IsCube`. On a symmetric closure space the two conditions
agree (`isCube_iff_isPlusCube`), so the chain groups coincide and excision for covers by iterated
interiors holds for the directed interval as well.

## Main statements

* `ClosureSpace.cubesInP_eq`: on a symmetric closure space the `(J₊, ⊡)` and `(J₁, ⊡)` chain
  groups coincide.
* `ClosureSpace.plus_excision_of_iterate_int_cover`, `ClosureSpace.plus_cube_small`: [DT],
  Theorem 1 and Proposition 1 for the directed interval, on symmetric closure spaces.

## References

* [DT] T. Dube and A. Tregub, *Excision fails for inductive-product cubical homology of closure
  spaces*.
-/

namespace ClosureSpace

open Finset

noncomputable section

variable {X : Type*}

/-- Chains supported on `(J₊, ⊡)` cubes with image in `S`. -/
def cubesInP (C : ClosureSpace X) (S : Set X) (n : ℕ) : AddSubgroup (Chain X n) :=
  AddSubgroup.closure {c | ∃ σ, C.IsPlusCube σ ∧ InSet S σ ∧ c = Finsupp.single σ 1}

/-- Chains supported on degenerate `(J₊, ⊡)` cubes with image in `S`. -/
def degInP (C : ClosureSpace X) (S : Set X) (n : ℕ) : AddSubgroup (Chain X n) :=
  AddSubgroup.closure
    {c | ∃ σ, C.IsPlusCube σ ∧ InSet S σ ∧ IsDegenerate σ ∧ c = Finsupp.single σ 1}

/-- Boundaries of `(J₊, ⊡)` chains in `S`. -/
def bndInP (C : ClosureSpace X) (S : Set X) (n : ℕ) : AddSubgroup (Chain X n) :=
  (cubesInP C S (n + 1)).map (bd n)

/-- Null relative classes in the `(J₊, ⊡)` theory. -/
def NullRelP (C : ClosureSpace X) (S T : Set X) (n : ℕ) (z : Chain X n) : Prop :=
  z ∈ bndInP C S n ⊔ cubesInP C T n ⊔ degInP C S n

/-- Relative cycles in the `(J₊, ⊡)` theory. -/
def IsRelCycleP (C : ClosureSpace X) (S T : Set X) (n : ℕ) (z : Chain X (n + 1)) : Prop :=
  z ∈ cubesInP C S (n + 1) ∧ bd n z ∈ cubesInP C T n ⊔ degInP C S n

section Symmetric

variable {C : ClosureSpace X} (hsymm : ∀ x y, y ∈ C.cl {x} → x ∈ C.cl {y})
include hsymm

theorem cubesInP_eq (S : Set X) (n : ℕ) : cubesInP C S n = cubesIn C S n := by
  unfold cubesInP cubesIn
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨σ, hσ, hS, rfl⟩
    exact ⟨σ, (isCube_iff_isPlusCube hsymm σ).mpr hσ, hS, rfl⟩
  · rintro ⟨σ, hσ, hS, rfl⟩
    exact ⟨σ, (isCube_iff_isPlusCube hsymm σ).mp hσ, hS, rfl⟩

theorem degInP_eq (S : Set X) (n : ℕ) : degInP C S n = degIn C S n := by
  unfold degInP degIn
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨σ, hσ, hS, hd, rfl⟩
    exact ⟨σ, (isCube_iff_isPlusCube hsymm σ).mpr hσ, hS, hd, rfl⟩
  · rintro ⟨σ, hσ, hS, hd, rfl⟩
    exact ⟨σ, (isCube_iff_isPlusCube hsymm σ).mp hσ, hS, hd, rfl⟩

theorem bndInP_eq (S : Set X) (n : ℕ) : bndInP C S n = bndIn C S n := by
  unfold bndInP bndIn
  rw [cubesInP_eq hsymm]

theorem nullRelP_iff (S T : Set X) (n : ℕ) (z : Chain X n) :
    NullRelP C S T n z ↔ NullRel C S T n z := by
  unfold NullRelP NullRel
  rw [bndInP_eq hsymm, cubesInP_eq hsymm, degInP_eq hsymm]

theorem isRelCycleP_iff (S T : Set X) (n : ℕ) (z : Chain X (n + 1)) :
    IsRelCycleP C S T n z ↔ IsRelCycle C S T n z := by
  unfold IsRelCycleP IsRelCycle
  rw [cubesInP_eq hsymm, cubesInP_eq hsymm, degInP_eq hsymm]

/-- **Excision for covers by iterated interiors, for the directed interval** ([DT], Theorem 1),
on a symmetric closure space. -/
theorem plus_excision_of_iterate_int_cover {A B : Set X} {k : ℕ}
    (hcov : ∀ x, x ∈ C.int^[k] A ∨ x ∈ C.int^[k] B) (d : ℕ) (hd : d + 1 ≤ 2 * k) :
    (∀ z ∈ cubesInP C B d, NullRelP C Set.univ A d z → NullRelP C B (A ∩ B) d z) ∧
    (∀ z ∈ cubesInP C Set.univ d, ∃ z' ∈ cubesInP C B d, NullRelP C Set.univ A d (z - z')) ∧
    (∀ m (z : Chain X (m + 1)), m + 1 = d → IsRelCycleP C Set.univ A m z →
      ∃ z', IsRelCycleP C B (A ∩ B) m z' ∧ NullRelP C Set.univ A (m + 1) (z - z')) := by
  simp only [cubesInP_eq hsymm, nullRelP_iff hsymm, isRelCycleP_iff hsymm]
  exact excision_of_iterate_int_cover hcov d hd

/-- **Small cubes for the directed interval** on a symmetric closure space. -/
theorem plus_cube_small {n k : ℕ} {σ : (Fin n → Bool) → X} (hσ : C.IsPlusCube σ)
    (hn : n ≤ 2 * k) {A B : Set X} (hcov : ∀ x, x ∈ C.int^[k] A ∨ x ∈ C.int^[k] B) :
    (∀ x, σ x ∈ A) ∨ (∀ x, σ x ∈ B) :=
  cube_small ((isCube_iff_isPlusCube hsymm σ).mpr hσ) hn hcov

end Symmetric

end

end ClosureSpace
