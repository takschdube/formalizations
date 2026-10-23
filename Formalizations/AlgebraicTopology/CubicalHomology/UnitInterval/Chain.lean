import Formalizations.AlgebraicTopology.CubicalHomology.UnitInterval.Path

/-!
# Chains of paths and squares

`1`-chains are integer combinations of paths and `0`-chains are integer combinations of points.
The boundary of a square `σ` is `∑ᵢ (-1)ⁱ (Aᵢ - Bᵢ)` over its faces, and the degenerate `1`-cubes
are the constant paths, so a `1`-chain is null in the `(I, ⊡)` theory when it is a sum of
boundaries of box squares and constant paths (`Null`).

A Coons square `pext γ ∘ ψ`, for a path `γ` and a continuous `ψ : 𝕀 × 𝕀 → ℝ`, is a product square
and hence a box square. Coons squares show that `γ` plus its reversal is null and that `α + β`
differs from the concatenation of `α` and `β` by a null chain.

## Main definitions

* `ClosureSpace.PChain X`, `ClosureSpace.bdPath`: `1`-chains and their boundary.
* `ClosureSpace.pathsIn C S`, `ClosureSpace.boxBnd C S`, `ClosureSpace.prodBnd C S`,
  `ClosureSpace.constIn S`: chains of paths in `S`, boundaries of box squares and of product
  squares in `S`, and constant paths in `S`.
* `ClosureSpace.Null C`: the null `1`-chains of the `(I, ⊡)` theory.

## Main statements

* `ClosureSpace.add_rev_mem_null`, `ClosureSpace.pcat_mem_null`: reversal and concatenation up to
  null chains ([DT], Lemma 4).

## References

* [DT] T. Dube and A. Tregub, *Excision fails for inductive-product cubical homology of closure
  spaces*.
-/

namespace ClosureSpace

open Topology Filter

local notation "𝕀" => unitInterval

noncomputable section

variable {X : Type*} {C : ClosureSpace X}

/-- `0`-chains. -/
abbrev PtChain (X : Type*) := X →₀ ℤ
/-- Chains of paths. -/
abbrev PChain (X : Type*) := (𝕀 → X) →₀ ℤ
/-- Chains of squares. -/
abbrev SqChain (X : Type*) := (𝕀 × 𝕀 → X) →₀ ℤ

/-- The boundary of a square, `∑ᵢ (-1)ⁱ (Aᵢ - Bᵢ)`. -/
def sqBd (σ : 𝕀 × 𝕀 → X) : PChain X :=
  -Finsupp.single (sqA1 σ) 1 + Finsupp.single (sqB1 σ) 1 + Finsupp.single (sqA2 σ) 1 -
    Finsupp.single (sqB2 σ) 1

/-- The boundary of paths. -/
def bdPath : PChain X →+ PtChain X :=
  Finsupp.liftAddHom fun γ =>
    zmultiplesHom (PtChain X) (Finsupp.single (γ 1) 1 - Finsupp.single (γ 0) 1)

theorem bdPath_single (γ : 𝕀 → X) :
    bdPath (Finsupp.single γ 1) = Finsupp.single (γ 1) 1 - Finsupp.single (γ 0) 1 := by
  simp [bdPath]

/-- Chains of paths with image in `S`. -/
def pathsIn (C : ClosureSpace X) (S : Set X) : AddSubgroup (PChain X) :=
  AddSubgroup.closure {c | ∃ γ, IsPath C γ ∧ (∀ t, γ t ∈ S) ∧ c = Finsupp.single γ 1}

/-- Chains of constant paths (the degenerate `1`-cubes) with value in `S`. -/
def constIn (S : Set X) : AddSubgroup (PChain X) :=
  AddSubgroup.closure {c | ∃ x ∈ S, c = Finsupp.single (fun _ => x) 1}

/-- `0`-chains supported in `S`. -/
def ptsIn (S : Set X) : AddSubgroup (PtChain X) :=
  AddSubgroup.closure {c | ∃ x ∈ S, c = Finsupp.single x 1}

/-- Boundaries of box squares with image in `S`. -/
def boxBnd (C : ClosureSpace X) (S : Set X) : AddSubgroup (PChain X) :=
  AddSubgroup.closure {c | ∃ σ, IsBoxSq C σ ∧ (∀ p, σ p ∈ S) ∧ c = sqBd σ}

/-- Boundaries of product squares with image in `S`. -/
def prodBnd (C : ClosureSpace X) (S : Set X) : AddSubgroup (PChain X) :=
  AddSubgroup.closure {c | ∃ σ, IsProdSq C σ ∧ (∀ p, σ p ∈ S) ∧ c = sqBd σ}

theorem sqBd_mem_boxBnd {σ : 𝕀 × 𝕀 → X} (hσ : IsBoxSq C σ) :
    sqBd σ ∈ boxBnd C Set.univ :=
  AddSubgroup.subset_closure ⟨σ, hσ, fun _ => trivial, rfl⟩

theorem const_mem_constIn (x : X) : Finsupp.single (fun _ : 𝕀 => x) 1 ∈ constIn (Set.univ : Set X) :=
  AddSubgroup.subset_closure ⟨x, trivial, rfl⟩

/-- The subgroup of null `1`-chains in the `(I, ⊡)` theory. -/
abbrev Null (C : ClosureSpace X) : AddSubgroup (PChain X) := boxBnd C Set.univ ⊔ constIn Set.univ

theorem sqBd_mem_null {σ : 𝕀 × 𝕀 → X} (hσ : IsBoxSq C σ) : sqBd σ ∈ Null C :=
  AddSubgroup.mem_sup_left (sqBd_mem_boxBnd hσ)

theorem const_mem_null (x : X) : Finsupp.single (fun _ : 𝕀 => x) 1 ∈ Null C :=
  AddSubgroup.mem_sup_right (const_mem_constIn x)

theorem pathsIn_mono {S T : Set X} (h : S ⊆ T) : pathsIn C S ≤ pathsIn C T := by
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨γ, hγ, hS, rfl⟩
  exact AddSubgroup.subset_closure ⟨γ, hγ, fun t => h (hS t), rfl⟩

/-! ## Coons squares -/

/-- A Coons square: a path composed with a continuous map of the square into the line. -/
theorem isBoxSq_pext_comp {γ : 𝕀 → X} (hγ : IsPath C γ) {ψ : 𝕀 × 𝕀 → ℝ} (hψ : Continuous ψ) :
    IsBoxSq C (fun p => pext γ (ψ p)) :=
  isProdSq_isBoxSq fun p => hγ.pext_comp hψ p

/-- `γ + γ̄` bounds. -/
theorem add_rev_mem_null {γ : 𝕀 → X} (hγ : IsPath C γ) :
    Finsupp.single γ 1 + Finsupp.single (rev γ) 1 ∈ Null C := by
  set Φ : 𝕀 × 𝕀 → X := fun p => pext γ ((p.1 : ℝ) * (1 - (p.2 : ℝ))) with hΦ
  have hbox : IsBoxSq C Φ := isBoxSq_pext_comp hγ (by fun_prop)
  have hA1 : sqA1 Φ = fun _ => pext γ 0 := by funext t; simp [sqA1, Φ]
  have hB1 : sqB1 Φ = rev γ := by funext t; simp [sqB1, Φ, rev]
  have hA2 : sqA2 Φ = γ := by funext s; simp [sqA2, Φ, pext_coe]
  have hB2 : sqB2 Φ = fun _ => pext γ 0 := by funext s; simp [sqB2, Φ]
  have hbd : sqBd Φ = Finsupp.single (rev γ) 1 + Finsupp.single γ 1 -
      2 • Finsupp.single (fun _ : 𝕀 => pext γ 0) 1 := by
    rw [sqBd, hA1, hB1, hA2, hB2]
    abel
  have : Finsupp.single γ 1 + Finsupp.single (rev γ) 1 =
      sqBd Φ + 2 • Finsupp.single (fun _ : 𝕀 => pext γ 0) 1 := by
    rw [hbd]; abel
  rw [this]
  exact add_mem (sqBd_mem_null hbox) (AddSubgroup.nsmul_mem _ (const_mem_null _) 2)

/-- `α + β - α·β` bounds. -/
theorem pcat_mem_null {α β : 𝕀 → X} (hα : IsPath C α) (hβ : IsPath C β) (h : α 1 = β 0) :
    Finsupp.single α 1 + Finsupp.single β 1 - Finsupp.single (pcat α β) 1 ∈ Null C := by
  set Φ : 𝕀 × 𝕀 → X := fun p => pext (pcat α β) ((p.1 : ℝ) * (1 - (p.2 : ℝ) / 2)) with hΦ
  have hbox : IsBoxSq C Φ := isBoxSq_pext_comp (isPath_pcat hα hβ h) (by fun_prop)
  have hA1 : sqA1 Φ = fun _ => pext (pcat α β) 0 := by funext t; simp [sqA1, Φ]
  have hB1 : sqB1 Φ = rev β := by
    funext t
    have ht0 := unitInterval.nonneg t
    have ht1 := unitInterval.le_one t
    simp only [sqB1, Φ, rev, Set.Icc.coe_one, one_mul]
    rw [pext_of_mem _ (by linarith) (by linarith)]
    simp only [pcat]
    split_ifs with h1
    · have h2 : (t : ℝ) = 1 := by linarith
      have e1 : 2 * (1 - (t : ℝ) / 2) = 1 := by rw [h2]; norm_num
      have e2 : 1 - (t : ℝ) = 0 := by rw [h2]; norm_num
      rw [e1, e2, pext_one, pext_zero, h]
    · congr 1
      ring
  have hA2 : sqA2 Φ = pcat α β := by funext s; simp [sqA2, Φ, pext_coe]
  have hB2 : sqB2 Φ = α := by
    funext s
    have hs0 := unitInterval.nonneg s
    have hs1 := unitInterval.le_one s
    simp only [sqB2, Φ, Set.Icc.coe_one]
    rw [pext_of_mem _ (by nlinarith) (by nlinarith)]
    simp only [pcat]
    rw [if_pos (by linarith)]
    have e : 2 * ((s : ℝ) * (1 - 1 / 2)) = s := by ring
    rw [e, pext_coe]
  have : Finsupp.single α 1 + Finsupp.single β 1 - Finsupp.single (pcat α β) 1 =
      -sqBd Φ - Finsupp.single (fun _ : 𝕀 => pext (pcat α β) 0) 1 +
        (Finsupp.single β 1 + Finsupp.single (rev β) 1) := by
    rw [sqBd, hA1, hB1, hA2, hB2]
    abel
  rw [this]
  exact add_mem (sub_mem (neg_mem (sqBd_mem_null hbox)) (const_mem_null _))
    (add_rev_mem_null hβ)

end

end ClosureSpace
