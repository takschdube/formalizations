import ClosureExcision.Basic

/-!
# The topological interval with the inductive product

Singular `1`-cubes are paths `γ : 𝕀 → X` and singular `2`-cubes are maps `σ : 𝕀 × 𝕀 → X`.
For the inductive product `𝕀 ⊡ 𝕀` the canonical neighbourhoods are crosses, so a square is
continuous when it is continuous along every horizontal and every vertical line (`IsBoxSq`);
for the categorical product it is continuous for the product topology (`IsProdSq`).

Main results:
* `box_H1_eq_zero`: in the `(I, ⊡)` theory every `1`-cycle of every closure space bounds.
* `c6_box_excision_not_injective`: excision fails for `(I, ⊡)` on the six-cycle.
-/

namespace ClosureExcision

open Topology Filter

local notation "𝕀" => unitInterval

noncomputable section

variable {X : Type*}

/-! ## Continuity into a closure space -/

/-- Continuity at `t` of a map from a topological space into a closure space. -/
def ContAt (C : ClosureSpace X) {T : Type*} [TopologicalSpace T] (f : T → X) (t : T) : Prop :=
  ∀ W, C.IsNbhd (f t) W → ∀ᶠ s in 𝓝 t, f s ∈ W

/-- A path: a continuous map from the unit interval. -/
def IsPath (C : ClosureSpace X) (γ : 𝕀 → X) : Prop := ∀ t, ContAt C γ t

/-- A singular square for the inductive product: continuous along horizontal and vertical lines. -/
def IsBoxSq (C : ClosureSpace X) (σ : 𝕀 × 𝕀 → X) : Prop :=
  ∀ p W, C.IsNbhd (σ p) W →
    (∀ᶠ s in 𝓝 p.1, σ (s, p.2) ∈ W) ∧ (∀ᶠ t in 𝓝 p.2, σ (p.1, t) ∈ W)

/-- A singular square for the categorical product: continuous for the product topology. -/
def IsProdSq (C : ClosureSpace X) (σ : 𝕀 × 𝕀 → X) : Prop := ∀ p, ContAt C σ p

variable {C : ClosureSpace X}

theorem ContAt.comp {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T'] {f : T' → X}
    {g : T → T'} {t : T} (hf : ContAt C f (g t)) (hg : ContinuousAt g t) :
    ContAt C (f ∘ g) t := fun W hW => hg.tendsto.eventually (hf W hW)

theorem ContAt.congr {T : Type*} [TopologicalSpace T] {f g : T → X} {t : T}
    (hf : ContAt C f t) (h : ∀ᶠ s in 𝓝 t, f s = g s) (ht : f t = g t) : ContAt C g t := by
  intro W hW
  rw [← ht] at hW
  filter_upwards [hf W hW, h] with s hs hfs
  rwa [← hfs]

/-- Two continuous branches that agree at `t` give a continuous `if`. -/
theorem ContAt.ite {T : Type*} [TopologicalSpace T] {F G : T → X} {P : T → Prop}
    [DecidablePred P] {t : T} (hF : ContAt C F t) (hG : ContAt C G t) (hFG : F t = G t) :
    ContAt C (fun s => if P s then F s else G s) t := by
  intro W hW
  have hWF : C.IsNbhd (F t) W := by
    dsimp only at hW
    split_ifs at hW
    · exact hW
    · rw [hFG]; exact hW
  have hWG : C.IsNbhd (G t) W := hFG ▸ hWF
  filter_upwards [hF W hWF, hG W hWG] with s hs1 hs2
  split_ifs <;> assumption

theorem contAt_const {T : Type*} [TopologicalSpace T] (x : X) (t : T) :
    ContAt C (fun _ : T => x) t := fun _ hW => Filter.Eventually.of_forall fun _ => C.mem_of_isNbhd hW

theorem isPath_const (x : X) : IsPath C (fun _ => x) := fun t => contAt_const x t

/-- A product square is a box square. -/
theorem boxAt_of_contAt {σ : 𝕀 × 𝕀 → X} {p : 𝕀 × 𝕀} (h : ContAt C σ p) {W : Set X}
    (hW : C.IsNbhd (σ p) W) :
    (∀ᶠ s in 𝓝 p.1, σ (s, p.2) ∈ W) ∧ (∀ᶠ t in 𝓝 p.2, σ (p.1, t) ∈ W) := by
  constructor
  · have ht : Tendsto (fun s : 𝕀 => (s, p.2)) (𝓝 p.1) (𝓝 p) := by
      simpa using (tendsto_id.prodMk_nhds tendsto_const_nhds :
        Tendsto (fun s : 𝕀 => (s, p.2)) (𝓝 p.1) (𝓝 (p.1, p.2)))
    exact ht.eventually (h W hW)
  · have ht : Tendsto (fun s : 𝕀 => (p.1, s)) (𝓝 p.2) (𝓝 p) := by
      simpa using (tendsto_const_nhds.prodMk_nhds tendsto_id :
        Tendsto (fun s : 𝕀 => (p.1, s)) (𝓝 p.2) (𝓝 (p.1, p.2)))
    exact ht.eventually (h W hW)

theorem isProdSq_isBoxSq {σ : 𝕀 × 𝕀 → X} (h : IsProdSq C σ) : IsBoxSq C σ :=
  fun p _ hW => boxAt_of_contAt (h p) hW

/-! ## Extending a path to the real line -/

/-- The path `γ` extended to `ℝ` by clamping. -/
def pext (γ : 𝕀 → X) : ℝ → X := Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) γ

theorem pext_coe (γ : 𝕀 → X) (t : 𝕀) : pext γ t = γ t :=
  Set.IccExtend_val _ γ t

theorem pext_of_mem (γ : 𝕀 → X) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    pext γ r = γ ⟨r, h0, h1⟩ :=
  Set.IccExtend_of_mem _ γ ⟨h0, h1⟩

theorem pext_zero (γ : 𝕀 → X) : pext γ 0 = γ 0 := by
  rw [pext_of_mem γ le_rfl zero_le_one]
  rfl

theorem pext_one (γ : 𝕀 → X) : pext γ 1 = γ 1 := by
  rw [pext_of_mem γ zero_le_one le_rfl]
  rfl

theorem IsPath.contAt_pext {γ : 𝕀 → X} (hγ : IsPath C γ) (r : ℝ) : ContAt C (pext γ) r :=
  ContAt.comp (g := Set.projIcc (0 : ℝ) 1 zero_le_one) (hγ _)
    (continuous_projIcc).continuousAt

/-- Composing the extension of a path with a continuous real function gives a continuous map. -/
theorem IsPath.pext_comp {T : Type*} [TopologicalSpace T] {γ : 𝕀 → X} (hγ : IsPath C γ)
    {f : T → ℝ} (hf : Continuous f) (t : T) : ContAt C (fun s => pext γ (f s)) t :=
  ContAt.comp (f := pext γ) (g := f) (hγ.contAt_pext (f t)) hf.continuousAt

/-! ## Chains -/

/-- `0`-chains. -/
abbrev PtChain (X : Type*) := X →₀ ℤ
/-- Chains of paths. -/
abbrev PChain (X : Type*) := (𝕀 → X) →₀ ℤ
/-- Chains of squares. -/
abbrev SqChain (X : Type*) := (𝕀 × 𝕀 → X) →₀ ℤ

/-- Faces of a square: `A₁, B₁` fix the first coordinate to `0, 1`; `A₂, B₂` the second. -/
def sqA1 (σ : 𝕀 × 𝕀 → X) : 𝕀 → X := fun t => σ (0, t)
def sqB1 (σ : 𝕀 × 𝕀 → X) : 𝕀 → X := fun t => σ (1, t)
def sqA2 (σ : 𝕀 × 𝕀 → X) : 𝕀 → X := fun s => σ (s, 0)
def sqB2 (σ : 𝕀 × 𝕀 → X) : 𝕀 → X := fun s => σ (s, 1)

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

/-- A Coons square: a path composed with a continuous map of the square into the line. -/
theorem isBoxSq_pext_comp {γ : 𝕀 → X} (hγ : IsPath C γ) {ψ : 𝕀 × 𝕀 → ℝ} (hψ : Continuous ψ) :
    IsBoxSq C (fun p => pext γ (ψ p)) :=
  isProdSq_isBoxSq fun p => hγ.pext_comp hψ p

/-! ## Reversal -/

/-- The reversed path. -/
def rev (γ : 𝕀 → X) : 𝕀 → X := fun t => pext γ (1 - t)

theorem IsPath.rev {γ : 𝕀 → X} (hγ : IsPath C γ) : IsPath C (rev γ) :=
  fun t => hγ.pext_comp (f := fun s : 𝕀 => 1 - (s : ℝ)) (by fun_prop) t

theorem rev_zero (γ : 𝕀 → X) : rev γ 0 = γ 1 := by
  simp [rev, pext_one]

theorem rev_one (γ : 𝕀 → X) : rev γ 1 = γ 0 := by
  simp [rev, pext_zero]

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


/-! ## Concatenation -/

/-- Concatenation of paths: `α` on `[0, 1/2]`, `β` on `[1/2, 1]`. -/
def pcat (α β : 𝕀 → X) : 𝕀 → X := fun t =>
  if (t : ℝ) ≤ 1 / 2 then pext α (2 * t) else pext β (2 * t - 1)

theorem pcat_zero (α β : 𝕀 → X) : pcat α β 0 = α 0 := by
  simp [pcat, pext_zero]

theorem pcat_one (α β : 𝕀 → X) : pcat α β 1 = β 1 := by
  norm_num [pcat, pext_one]

theorem isPath_pcat {α β : 𝕀 → X} (hα : IsPath C α) (hβ : IsPath C β) (h : α 1 = β 0) :
    IsPath C (pcat α β) := by
  intro t
  have hF : ContAt C (fun s : 𝕀 => pext α (2 * (s : ℝ))) t :=
    hα.pext_comp (f := fun s : 𝕀 => 2 * (s : ℝ)) (by fun_prop) t
  have hG : ContAt C (fun s : 𝕀 => pext β (2 * (s : ℝ) - 1)) t :=
    hβ.pext_comp (f := fun s : 𝕀 => 2 * (s : ℝ) - 1) (by fun_prop) t
  have hcont : ContinuousAt (fun s : 𝕀 => (s : ℝ)) t := continuous_subtype_val.continuousAt
  rcases lt_trichotomy (t : ℝ) (1 / 2) with hlt | heq | hgt
  · refine hF.congr ?_ (by simp only [pcat]; rw [if_pos hlt.le])
    filter_upwards [hcont.eventually_lt continuousAt_const hlt] with s hs
    simp only [pcat]; rw [if_pos hs.le]
  · refine ContAt.ite hF hG ?_
    simp only [heq]
    norm_num [pext_one, pext_zero, h]
  · refine hG.congr ?_ (by simp only [pcat]; rw [if_neg (not_le.mpr hgt)])
    filter_upwards [continuousAt_const.eventually_lt hcont hgt] with s hs
    simp only [pcat]; rw [if_neg (not_le.mpr hs)]

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

/-! ## Loops bound -/

/-- Reparametrisation of the right face of the sector square. -/
def psiR (t : ℝ) : ℝ := max 0 (t - 1 / 2) / max (1 / 2) t

/-- Reparametrisation of the top face of the sector square. -/
def psiT (t : ℝ) : ℝ := 1 / (2 * max (1 / 2) t)

theorem max_half_pos (t : ℝ) : 0 < max (1 / 2 : ℝ) t :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem continuous_psiR : Continuous psiR :=
  (continuous_const.max (continuous_id.sub continuous_const)).div
    (continuous_const.max continuous_id) fun t => (max_half_pos t).ne'

theorem continuous_psiT : Continuous psiT :=
  continuous_const.div (continuous_const.mul (continuous_const.max continuous_id))
    fun t => (mul_pos two_pos (max_half_pos t)).ne'

theorem psiR_zero : psiR 0 = 0 := by norm_num [psiR]
theorem psiT_zero : psiT 0 = 1 := by norm_num [psiT]
theorem psiR_one : psiR 1 = 1 / 2 := by norm_num [psiR]
theorem psiT_one : psiT 1 = 1 / 2 := by norm_num [psiT]

/-- The sector square of a loop `ℓ`: with `u = s - 1/2` and `v = t - 1/2`, it runs `ℓ` along
the angular parameter `v / (u + v)` in the open quadrant `u, v > 0` and is constant elsewhere.
It is continuous along horizontal and vertical lines but not at the centre. -/
def sector (ℓ : 𝕀 → X) : 𝕀 × 𝕀 → X := fun p =>
  if 0 < (p.1 : ℝ) - 1 / 2 ∧ 0 < (p.2 : ℝ) - 1 / 2 then
    pext ℓ (((p.2 : ℝ) - 1 / 2) / (((p.1 : ℝ) - 1 / 2) + ((p.2 : ℝ) - 1 / 2)))
  else ℓ 0

theorem isBoxSq_sector {ℓ : 𝕀 → X} (hℓ : IsPath C ℓ) (hloop : ℓ 0 = ℓ 1) :
    IsBoxSq C (sector ℓ) := by
  intro p W hW
  have hu : Continuous fun q : 𝕀 × 𝕀 => (q.1 : ℝ) - 1 / 2 := by fun_prop
  have hv : Continuous fun q : 𝕀 × 𝕀 => (q.2 : ℝ) - 1 / 2 := by fun_prop
  by_cases hc : (p.1 : ℝ) - 1 / 2 = 0 ∧ (p.2 : ℝ) - 1 / 2 = 0
  · -- the centre: the square is constant on both lines through it
    have hσp : sector ℓ p = ℓ 0 := by
      simp only [sector]
      rw [if_neg (fun h => by linarith [h.1, hc.1])]
    have hmem : ℓ 0 ∈ W := hσp ▸ C.mem_of_isNbhd hW
    constructor
    · refine Eventually.of_forall fun s => ?_
      simp only [sector]
      rw [if_neg (fun h => by linarith [h.2, hc.2])]
      exact hmem
    · refine Eventually.of_forall fun s => ?_
      simp only [sector]
      rw [if_neg (fun h => by linarith [h.1, hc.1])]
      exact hmem
  · apply boxAt_of_contAt _ hW
    by_cases hneg : (p.1 : ℝ) - 1 / 2 < 0 ∨ (p.2 : ℝ) - 1 / 2 < 0
    · -- outside the closed quadrant the square is locally constant
      have hσp : sector ℓ p = ℓ 0 := by
        simp only [sector]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        rcases hneg with h | h <;> linarith
      refine (contAt_const (C := C) (ℓ 0) p).congr ?_ hσp.symm
      rcases hneg with h | h
      · filter_upwards [hu.continuousAt.eventually_lt continuousAt_const h] with q hq
        simp only [sector]
        rw [if_neg]
        rintro ⟨h1, _⟩
        linarith
      · filter_upwards [hv.continuousAt.eventually_lt continuousAt_const h] with q hq
        simp only [sector]
        rw [if_neg]
        rintro ⟨_, h2⟩
        linarith
    · push Not at hneg
      obtain ⟨hu0, hv0⟩ := hneg
      have hsum : 0 < ((p.1 : ℝ) - 1 / 2) + ((p.2 : ℝ) - 1 / 2) := by
        by_contra hle
        exact hc ⟨by linarith, by linarith⟩
      have hr : ContinuousAt (fun q : 𝕀 × 𝕀 =>
          ((q.2 : ℝ) - 1 / 2) / (((q.1 : ℝ) - 1 / 2) + ((q.2 : ℝ) - 1 / 2))) p :=
        hv.continuousAt.div (hu.continuousAt.add hv.continuousAt) hsum.ne'
      have hg : ContAt C (fun q : 𝕀 × 𝕀 =>
          pext ℓ (((q.2 : ℝ) - 1 / 2) / (((q.1 : ℝ) - 1 / 2) + ((q.2 : ℝ) - 1 / 2)))) p :=
        ContAt.comp (f := pext ℓ) (hℓ.contAt_pext _) hr
      by_cases hin : 0 < (p.1 : ℝ) - 1 / 2 ∧ 0 < (p.2 : ℝ) - 1 / 2
      · -- inside the open quadrant the square is the composite `pext ℓ ∘ r`
        refine hg.congr ?_ (by simp only [sector]; rw [if_pos hin])
        filter_upwards [continuousAt_const.eventually_lt hu.continuousAt hin.1,
          continuousAt_const.eventually_lt hv.continuousAt hin.2] with q hq1 hq2
        simp only [sector]
        rw [if_pos ⟨hq1, hq2⟩]
      · -- on the two positive half-axes both branches take the value `ℓ 0`
        have hgp : pext ℓ (((p.2 : ℝ) - 1 / 2) / (((p.1 : ℝ) - 1 / 2) + ((p.2 : ℝ) - 1 / 2)))
            = ℓ 0 := by
          by_cases h1 : (p.1 : ℝ) - 1 / 2 = 0
          · have h2 : 0 < (p.2 : ℝ) - 1 / 2 := by
              rcases hv0.lt_or_eq with h | h
              · exact h
              · exact absurd ⟨h1, h.symm⟩ hc
            rw [h1, zero_add, div_self h2.ne', pext_one, hloop]
          · have h2 : (p.2 : ℝ) - 1 / 2 = 0 := by
              rcases hv0.lt_or_eq with h | h
              · exact absurd ⟨lt_of_le_of_ne hu0 (Ne.symm h1), h⟩ hin
              · exact h.symm
            rw [h2, zero_div, pext_zero]
        exact ContAt.ite hg (contAt_const (ℓ 0) p) hgp

theorem sector_sqA1 (ℓ : 𝕀 → X) : sqA1 (sector ℓ) = fun _ => ℓ 0 := by
  funext t
  simp only [sqA1, sector, Set.Icc.coe_zero]
  rw [if_neg]
  rintro ⟨h, _⟩
  norm_num at h

theorem sector_sqA2 (ℓ : 𝕀 → X) : sqA2 (sector ℓ) = fun _ => ℓ 0 := by
  funext s
  simp only [sqA2, sector, Set.Icc.coe_zero]
  rw [if_neg]
  rintro ⟨_, h⟩
  norm_num at h

theorem sector_sqB1 (ℓ : 𝕀 → X) : sqB1 (sector ℓ) = fun t : 𝕀 => pext ℓ (psiR t) := by
  funext t
  simp only [sqB1, sector, Set.Icc.coe_one]
  split_ifs with h
  · have ht : (1 / 2 : ℝ) < t := by linarith [h.2]
    congr 1
    rw [psiR, max_eq_right (by linarith), max_eq_right ht.le]
    ring_nf
  · have ht : (t : ℝ) ≤ 1 / 2 := by
      by_contra ht
      exact h ⟨by norm_num, by linarith⟩
    rw [psiR, max_eq_left (by linarith), zero_div, pext_zero]

theorem sector_sqB2 (ℓ : 𝕀 → X) (hloop : ℓ 0 = ℓ 1) :
    sqB2 (sector ℓ) = fun s : 𝕀 => pext ℓ (psiT s) := by
  funext s
  simp only [sqB2, sector, Set.Icc.coe_one]
  split_ifs with h
  · have hs : (1 / 2 : ℝ) < s := by linarith [h.1]
    congr 1
    rw [psiT, max_eq_right hs.le]
    have hs0 : (s : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have e : ((s : ℝ) - 1 / 2) + (1 - 1 / 2) = s := by ring
    rw [e]
    field_simp
    norm_num
  · have hs : (s : ℝ) ≤ 1 / 2 := by
      by_contra hs
      exact h ⟨by linarith, by norm_num⟩
    rw [psiT, max_eq_left hs]
    norm_num [pext_one, hloop]

/-- **Every loop bounds** in the `(I, ⊡)` theory. -/
theorem loop_mem_null {ℓ : 𝕀 → X} (hℓ : IsPath C ℓ) (hloop : ℓ 0 = ℓ 1) :
    Finsupp.single ℓ 1 ∈ Null C := by
  set Φ : 𝕀 × 𝕀 → X :=
    fun p => pext ℓ ((1 - (p.1 : ℝ)) * psiR p.2 + (p.1 : ℝ) * psiT p.2) with hΦ
  have hboxΦ : IsBoxSq C Φ := isBoxSq_pext_comp hℓ (by
    have := continuous_psiR
    have := continuous_psiT
    fun_prop)
  have hA1 : sqA1 Φ = fun t : 𝕀 => pext ℓ (psiR t) := by funext t; simp [sqA1, Φ]
  have hB1 : sqB1 Φ = fun t : 𝕀 => pext ℓ (psiT t) := by funext t; simp [sqB1, Φ]
  have hA2 : sqA2 Φ = ℓ := by
    funext s
    simp [sqA2, Φ, psiR_zero, psiT_zero, pext_coe]
  have hB2 : sqB2 Φ = fun _ => pext ℓ (1 / 2) := by
    funext s
    simp only [sqB2, Φ, Set.Icc.coe_one, psiR_one, psiT_one]
    congr 1
    ring
  have : Finsupp.single ℓ 1 = sqBd Φ + sqBd (sector ℓ) +
      Finsupp.single (fun _ : 𝕀 => pext ℓ (1 / 2)) 1 := by
    rw [sqBd, sqBd, hA1, hB1, hA2, hB2, sector_sqA1, sector_sqA2, sector_sqB1,
      sector_sqB2 ℓ hloop]
    abel
  rw [this]
  exact add_mem (add_mem (sqBd_mem_null hboxΦ) (sqBd_mem_null (isBoxSq_sector hℓ hloop)))
    (const_mem_null _)


/-! ## Every `1`-cycle bounds -/

/-- `x` and `y` are joined by a path. -/
def Joined (C : ClosureSpace X) (x y : X) : Prop := ∃ γ, IsPath C γ ∧ γ 0 = x ∧ γ 1 = y

theorem joined_refl (x : X) : Joined C x x := ⟨fun _ => x, isPath_const x, rfl, rfl⟩

theorem Joined.symm {x y : X} (h : Joined C x y) : Joined C y x := by
  obtain ⟨γ, hγ, h0, h1⟩ := h
  exact ⟨rev γ, hγ.rev, by rw [rev_zero, h1], by rw [rev_one, h0]⟩

theorem Joined.trans {x y z : X} (h : Joined C x y) (h' : Joined C y z) : Joined C x z := by
  obtain ⟨α, hα, a0, a1⟩ := h
  obtain ⟨β, hβ, b0, b1⟩ := h'
  exact ⟨pcat α β, isPath_pcat hα hβ (a1.trans b0.symm), by rw [pcat_zero, a0],
    by rw [pcat_one, b1]⟩

/-- Path components. -/
def pathSetoid (C : ClosureSpace X) : Setoid X where
  r := Joined C
  iseqv := ⟨joined_refl, Joined.symm, Joined.trans⟩

/-- A chosen base point in the path component of `x`. -/
def basePt (C : ClosureSpace X) (x : X) : X := (Quotient.mk (pathSetoid C) x).out

theorem joined_basePt (x : X) : Joined C (basePt C x) x :=
  Quotient.mk_out (s := pathSetoid C) x

theorem basePt_eq {x y : X} (h : Joined C x y) : basePt C x = basePt C y := by
  unfold basePt
  rw [Quotient.sound (s := pathSetoid C) h]

/-- A chosen path from the base point to `x`. -/
def basePath (C : ClosureSpace X) (x : X) : 𝕀 → X := (joined_basePt (C := C) x).choose

theorem basePath_spec (x : X) :
    IsPath C (basePath C x) ∧ basePath C x 0 = basePt C x ∧ basePath C x 1 = x :=
  (joined_basePt (C := C) x).choose_spec

/-- `x ↦ basePath x`, extended linearly to `0`-chains. -/
def bpMap (C : ClosureSpace X) : PtChain X →+ PChain X :=
  Finsupp.liftAddHom fun x => zmultiplesHom (PChain X) (Finsupp.single (basePath C x) 1)

theorem bpMap_single (x : X) :
    bpMap C (Finsupp.single x 1) = Finsupp.single (basePath C x) 1 := by
  simp [bpMap]

/-- Each path is homologous to the difference of the base paths of its endpoints. -/
theorem path_sub_bp_mem_null {γ : 𝕀 → X} (hγ : IsPath C γ) :
    Finsupp.single γ 1 - bpMap C (bdPath (Finsupp.single γ 1)) ∈ Null C := by
  rw [bdPath_single, map_sub, bpMap_single, bpMap_single]
  obtain ⟨hx, hx0, hx1⟩ := basePath_spec (C := C) (γ 0)
  obtain ⟨hy, hy0, hy1⟩ := basePath_spec (C := C) (γ 1)
  have hbase : basePt C (γ 0) = basePt C (γ 1) := basePt_eq ⟨γ, hγ, rfl, rfl⟩
  set βx := basePath C (γ 0)
  set βy := basePath C (γ 1)
  have h1 : IsPath C (pcat βx γ) := isPath_pcat hx hγ hx1
  have h2 : pcat βx γ 1 = rev βy 0 := by rw [pcat_one, rev_zero, hy1]
  have hL : IsPath C (pcat (pcat βx γ) (rev βy)) := isPath_pcat h1 hy.rev h2
  have hloop : pcat (pcat βx γ) (rev βy) 0 = pcat (pcat βx γ) (rev βy) 1 := by
    rw [pcat_zero, pcat_zero, pcat_one, rev_one, hx0, hy0, hbase]
  have e1 := pcat_mem_null h1 hy.rev h2
  have e2 := pcat_mem_null hx hγ hx1
  have e3 := add_rev_mem_null hy
  have e4 := loop_mem_null hL hloop
  have key : (Finsupp.single γ 1 : PChain X) - (Finsupp.single βy 1 - Finsupp.single βx 1) =
      (Finsupp.single βx 1 + Finsupp.single γ 1 - Finsupp.single (pcat βx γ) 1) +
      (Finsupp.single (pcat βx γ) 1 + Finsupp.single (rev βy) 1 -
        Finsupp.single (pcat (pcat βx γ) (rev βy)) 1) +
      Finsupp.single (pcat (pcat βx γ) (rev βy)) 1 -
      (Finsupp.single βy 1 + Finsupp.single (rev βy) 1) := by abel
  rw [key]
  exact sub_mem (add_mem (add_mem e2 e1) e4) e3

/-- **Every `1`-cycle bounds** in the `(I, ⊡)` theory, for every closure space. -/
theorem sub_bpMap_mem_null {z : PChain X} (hz : z ∈ pathsIn C Set.univ) :
    z - bpMap C (bdPath z) ∈ Null C := by
  induction hz using AddSubgroup.closure_induction with
  | mem c hc =>
      obtain ⟨γ, hγ, _, rfl⟩ := hc
      exact path_sub_bp_mem_null hγ
  | zero => simp
  | add a b _ _ ha hb =>
      have e : a + b - bpMap C (bdPath (a + b)) =
          (a - bpMap C (bdPath a)) + (b - bpMap C (bdPath b)) := by
        simp only [map_add]; abel
      rw [e]; exact add_mem ha hb
  | neg a _ ha =>
      have e : -a - bpMap C (bdPath (-a)) = -(a - bpMap C (bdPath a)) := by
        simp only [map_neg]; abel
      rw [e]; exact neg_mem ha

/-- **Every `1`-cycle bounds** in the `(I, ⊡)` theory, for every closure space. -/
theorem box_H1_eq_zero (C : ClosureSpace X) :
    ∀ z ∈ pathsIn C Set.univ, bdPath z = 0 → z ∈ boxBnd C Set.univ ⊔ constIn Set.univ := by
  intro z hz hbd
  have key := sub_bpMap_mem_null hz
  rw [hbd, map_zero, sub_zero] at key
  exact key

theorem pathsIn_mono {S T : Set X} (h : S ⊆ T) : pathsIn C S ≤ pathsIn C T := by
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨γ, hγ, hS, rfl⟩
  exact AddSubgroup.subset_closure ⟨γ, hγ, fun t => h (hS t), rfl⟩

/-! ## Faces of box squares are paths -/

theorem IsBoxSq.isPath_sqB1 {σ : 𝕀 × 𝕀 → X} (h : IsBoxSq C σ) : IsPath C (sqB1 σ) :=
  fun t W hW => (h (1, t) W hW).2

theorem IsBoxSq.isPath_sqB2 {σ : 𝕀 × 𝕀 → X} (h : IsBoxSq C σ) : IsPath C (sqB2 σ) :=
  fun s W hW => (h (s, 1) W hW).1

/-! ## The six-cycle -/

/-- Equal or adjacent in the six-cycle. -/
def c6Rel (a b : ZMod 6) : Prop := b = a ∨ b = a + 1 ∨ a = b + 1

instance : DecidableRel c6Rel := fun a b => by unfold c6Rel; infer_instance

/-- The six-cycle as a closure space. -/
def c6 : ClosureSpace (ZMod 6) := ClosureSpace.ofRel c6Rel (fun _ => Or.inl rfl)

/-- `C₆` minus the vertex `5`. -/
def A6 : Set (ZMod 6) := {v | v ≠ 5}
/-- `C₆` minus the vertex `2`. -/
def B6 : Set (ZMod 6) := {v | v ≠ 2}

theorem c6_isNbhd {v : ZMod 6} {W : Set (ZMod 6)} :
    c6.IsNbhd v W ↔ ∀ y, c6Rel y v → y ∈ W :=
  ClosureSpace.ofRel_mem_int

theorem c6_interiorCover : c6.IsInteriorCover A6 B6 := by
  intro x
  change c6.IsNbhd x A6 ∨ c6.IsNbhd x B6
  simp only [c6_isNbhd, A6, B6, Set.mem_ofPred_eq]
  revert x
  decide

theorem contAt_c6_of {T : Type*} [TopologicalSpace T] {f : T → ZMod 6} {t : T}
    (h : ∀ᶠ s in 𝓝 t, c6Rel (f s) (f t)) : ContAt c6 f t := by
  intro W hW
  rw [c6_isNbhd] at hW
  filter_upwards [h] with s hs
  exact hW _ hs

theorem IsPath.c6Rel_eventually {γ : 𝕀 → ZMod 6} (hγ : IsPath c6 γ) (t : 𝕀) :
    ∀ᶠ s in 𝓝 t, c6Rel (γ s) (γ t) :=
  hγ t {y | c6Rel y (γ t)} (c6_isNbhd.mpr fun _ hy => hy)

/-- The hexagon loop `t ↦ ⌊6t⌋ mod 6`. -/
def hexLoop : 𝕀 → ZMod 6 := fun t => ((⌊6 * (t : ℝ)⌋ : ℤ) : ZMod 6)

theorem isPath_hexLoop : IsPath c6 hexLoop := by
  intro t
  apply contAt_c6_of
  set m := ⌊6 * (t : ℝ)⌋ with hm
  have hm1 : (m : ℝ) ≤ 6 * t := Int.floor_le _
  have hm2 : 6 * (t : ℝ) < m + 1 := Int.lt_floor_add_one _
  have hc : ContinuousAt (fun s : 𝕀 => 6 * (s : ℝ)) t :=
    (continuous_const.mul continuous_subtype_val).continuousAt
  filter_upwards [hc.eventually_lt continuousAt_const hm2,
    continuousAt_const.eventually_lt hc (show (m : ℝ) - 1 < 6 * t by linarith)] with s hs1 hs2
  have hf1 : ⌊6 * (s : ℝ)⌋ ≤ m := by
    have : ⌊6 * (s : ℝ)⌋ < m + 1 := Int.floor_lt.mpr (by exact_mod_cast hs1)
    omega
  have hf2 : m - 1 ≤ ⌊6 * (s : ℝ)⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have hcases : ⌊6 * (s : ℝ)⌋ = m ∨ ⌊6 * (s : ℝ)⌋ = m - 1 := by omega
  simp only [hexLoop, c6Rel]
  rw [← hm]
  rcases hcases with h | h
  · left; rw [h]
  · right; left; rw [h]; push_cast; ring

theorem hexLoop_zero : hexLoop 0 = 0 := by simp [hexLoop]

theorem hexLoop_one : hexLoop 1 = 0 := by
  simp only [hexLoop, Set.Icc.coe_one, mul_one]
  rw [show (6 : ℝ) = ((6 : ℤ) : ℝ) by norm_num, Int.floor_intCast]
  decide

theorem hexLoop_loop : hexLoop 0 = hexLoop 1 := by rw [hexLoop_zero, hexLoop_one]

theorem pext_hexLoop {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    pext hexLoop r = ((⌊6 * r⌋ : ℤ) : ZMod 6) := by
  rw [pext_of_mem _ h0 h1]
  rfl

theorem psiR_nonneg {t : ℝ} : 0 ≤ psiR t :=
  div_nonneg (le_max_left _ _) (max_half_pos t).le

theorem psiR_le_half {t : ℝ} (ht : t ≤ 1) : psiR t ≤ 1 / 2 := by
  unfold psiR
  rw [div_le_iff₀ (max_half_pos t)]
  rcases le_total t (1 / 2) with h | h
  · rw [max_eq_left (by linarith)]; positivity
  · rw [max_eq_right (by linarith), max_eq_right h]; linarith

theorem half_le_psiT {t : ℝ} (ht : t ≤ 1) : 1 / 2 ≤ psiT t := by
  unfold psiT
  rw [le_div_iff₀ (mul_pos two_pos (max_half_pos t))]
  have : max (1 / 2 : ℝ) t ≤ 1 := max_le (by norm_num) ht
  linarith

theorem psiT_le_one {t : ℝ} : psiT t ≤ 1 := by
  unfold psiT
  rw [div_le_iff₀ (mul_pos two_pos (max_half_pos t))]
  have : (1 / 2 : ℝ) ≤ max (1 / 2) t := le_max_left _ _
  linarith

/-- The sector square of the hexagon loop. -/
def hexSq : 𝕀 × 𝕀 → ZMod 6 := sector hexLoop

theorem isBoxSq_hexSq : IsBoxSq c6 hexSq := isBoxSq_sector isPath_hexLoop hexLoop_loop

theorem hexSq_sqB1_mem (t : 𝕀) : sqB1 hexSq t ∈ A6 := by
  rw [hexSq, sector_sqB1]
  have h0 : 0 ≤ psiR t := psiR_nonneg
  have h1 : psiR t ≤ 1 / 2 := psiR_le_half (unitInterval.le_one t)
  simp only [A6, Set.mem_ofPred_eq]
  rw [pext_hexLoop h0 (by linarith)]
  have hk0 : 0 ≤ ⌊6 * psiR t⌋ := Int.floor_nonneg.mpr (by linarith)
  have hk1 : ⌊6 * psiR t⌋ ≤ 3 := Int.floor_le_iff.mpr (by push_cast; linarith)
  generalize ⌊6 * psiR t⌋ = k at hk0 hk1
  interval_cases k <;> decide

theorem hexSq_sqB2_mem (s : 𝕀) : sqB2 hexSq s ∈ B6 := by
  rw [hexSq, sector_sqB2 _ hexLoop_loop]
  have h0 : 1 / 2 ≤ psiT s := half_le_psiT (unitInterval.le_one s)
  have h1 : psiT s ≤ 1 := psiT_le_one
  simp only [B6, Set.mem_ofPred_eq]
  rw [pext_hexLoop (by linarith) h1]
  have hk0 : 3 ≤ ⌊6 * psiT s⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have hk1 : ⌊6 * psiT s⌋ ≤ 6 := Int.floor_le_iff.mpr (by push_cast; linarith)
  generalize ⌊6 * psiT s⌋ = k at hk0 hk1
  interval_cases k <;> decide

theorem hexSq_corner_zero : sqB2 hexSq 0 = 0 := by
  rw [hexSq, sector_sqB2 _ hexLoop_loop]
  simp only [Set.Icc.coe_zero]
  rw [psiT_zero, pext_one, hexLoop_one]

theorem hexSq_corner_one : sqB2 hexSq 1 = 3 := by
  rw [hexSq, sector_sqB2 _ hexLoop_loop]
  simp only [Set.Icc.coe_one]
  rw [psiT_one, pext_hexLoop (by norm_num) (by norm_num)]
  norm_num

theorem hexSq_sqB1_zero : sqB1 hexSq 0 = 0 := by
  rw [hexSq, sector_sqB1]
  simp only [Set.Icc.coe_zero]
  rw [psiR_zero, pext_zero, hexLoop_zero]

theorem hexSq_sqB1_one : sqB1 hexSq 1 = 3 := by
  have : sqB1 hexSq 1 = sqB2 hexSq 1 := rfl
  rw [this, hexSq_corner_one]

/-- The detecting cochain: `h = 1` on `{3, 4}` and `0` elsewhere; `λ(γ) = h(γ 1) - h(γ 0)`. -/
def hval (v : ZMod 6) : ℤ := if v = 3 ∨ v = 4 then 1 else 0

/-- `λ` on `1`-chains. -/
def lam : PChain (ZMod 6) →+ ℤ :=
  Finsupp.liftAddHom fun γ => zmultiplesHom ℤ (hval (γ 1) - hval (γ 0))

theorem lam_single (γ : 𝕀 → ZMod 6) : lam (Finsupp.single γ 1) = hval (γ 1) - hval (γ 0) := by
  simp [lam]

theorem lam_sqBd (σ : 𝕀 × 𝕀 → ZMod 6) : lam (sqBd σ) = 0 := by
  simp only [sqBd, map_add, map_sub, map_neg, lam_single, sqA1, sqB1, sqA2, sqB2]
  ring

theorem lam_const (x : ZMod 6) : lam (Finsupp.single (fun _ : 𝕀 => x) 1) = 0 := by
  rw [lam_single, sub_self]

/-- Paths inside `A₆ ∩ B₆ = {0, 1} ⊔ {3, 4}` stay in one component, so `λ` vanishes on them. -/
theorem lam_path_inter {γ : 𝕀 → ZMod 6} (hγ : IsPath c6 γ) (hS : ∀ t, γ t ∈ A6 ∩ B6) :
    lam (Finsupp.single γ 1) = 0 := by
  rw [lam_single]
  have hstep : ∀ a b : ZMod 6, a ≠ 5 → a ≠ 2 → b ≠ 5 → b ≠ 2 → c6Rel a b →
      ((a = 3 ∨ a = 4) ↔ (b = 3 ∨ b = 4)) := by decide
  have hS' : ∀ t, γ t ≠ 5 ∧ γ t ≠ 2 := fun t => hS t
  set S : Set 𝕀 := {t | γ t = 3 ∨ γ t = 4}
  have hopen : IsOpen S := isOpen_iff_mem_nhds.mpr fun t ht => by
    filter_upwards [hγ.c6Rel_eventually t] with s hs
    exact (hstep _ _ (hS' s).1 (hS' s).2 (hS' t).1 (hS' t).2 hs).mpr ht
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    exact isOpen_iff_mem_nhds.mpr fun t ht => by
      filter_upwards [hγ.c6Rel_eventually t] with s hs hs'
      exact ht ((hstep _ _ (hS' s).1 (hS' s).2 (hS' t).1 (hS' t).2 hs).mp hs')
  have h01 : (0 : 𝕀) ∈ S ↔ (1 : 𝕀) ∈ S := by
    rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with h | h
    · rw [h]; simp
    · rw [h]; simp
  have e : (γ 0 = 3 ∨ γ 0 = 4) ↔ (γ 1 = 3 ∨ γ 1 = 4) := h01
  unfold hval
  by_cases h0 : γ 0 = 3 ∨ γ 0 = 4
  · rw [if_pos h0, if_pos (e.mp h0), sub_self]
  · rw [if_neg h0, if_neg (fun h1 => h0 (e.mpr h1)), sub_self]

theorem le_lam_ker_box : boxBnd c6 B6 ≤ lam.ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨σ, _, _, rfl⟩
  exact lam_sqBd σ

theorem le_lam_ker_paths : pathsIn c6 (A6 ∩ B6) ≤ lam.ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨γ, hγ, hS, rfl⟩
  exact lam_path_inter hγ hS

theorem le_lam_ker_const : constIn B6 ≤ lam.ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨x, _, rfl⟩
  exact lam_const x

theorem lam_top_face : lam (Finsupp.single (sqB2 hexSq) 1) = 1 := by
  rw [lam_single, hexSq_corner_one, hexSq_corner_zero]
  decide

theorem sqBd_hexSq : sqBd hexSq =
    Finsupp.single (sqB1 hexSq) 1 - Finsupp.single (sqB2 hexSq) 1 := by
  rw [sqBd, hexSq, sector_sqA1, sector_sqA2]
  abel

theorem top_face_mem_pathsIn : Finsupp.single (sqB2 hexSq) 1 ∈ pathsIn c6 B6 :=
  AddSubgroup.subset_closure ⟨_, isBoxSq_hexSq.isPath_sqB2, hexSq_sqB2_mem, rfl⟩

theorem right_face_mem_pathsIn : Finsupp.single (sqB1 hexSq) 1 ∈ pathsIn c6 A6 :=
  AddSubgroup.subset_closure ⟨_, isBoxSq_hexSq.isPath_sqB1, hexSq_sqB1_mem, rfl⟩

theorem bdPath_top_face :
    bdPath (Finsupp.single (sqB2 hexSq) 1) ∈ ptsIn (A6 ∩ B6) := by
  rw [bdPath_single, hexSq_corner_one, hexSq_corner_zero]
  exact sub_mem
    (AddSubgroup.subset_closure ⟨3, ⟨show (3 : ZMod 6) ≠ 5 by decide,
      show (3 : ZMod 6) ≠ 2 by decide⟩, rfl⟩)
    (AddSubgroup.subset_closure ⟨0, ⟨show (0 : ZMod 6) ≠ 5 by decide,
      show (0 : ZMod 6) ≠ 2 by decide⟩, rfl⟩)

/-- **Excision fails for `(I, ⊡)`.** The top face `η` of the sector square of the hexagon loop
is a relative cycle of `(B₆, A₆ ∩ B₆)` that is null in `(C₆, A₆)` but not in
`(B₆, A₆ ∩ B₆)`. -/
theorem c6_box_excision_not_injective :
    ∃ η : PChain (ZMod 6), η ∈ pathsIn c6 B6 ∧ bdPath η ∈ ptsIn (A6 ∩ B6) ∧
      η ∈ boxBnd c6 Set.univ ⊔ pathsIn c6 A6 ⊔ constIn Set.univ ∧
      η ∉ boxBnd c6 B6 ⊔ pathsIn c6 (A6 ∩ B6) ⊔ constIn B6 := by
  refine ⟨Finsupp.single (sqB2 hexSq) 1, top_face_mem_pathsIn, bdPath_top_face, ?_, ?_⟩
  · have e : Finsupp.single (sqB2 hexSq) 1 =
        -sqBd hexSq + Finsupp.single (sqB1 hexSq) 1 := by rw [sqBd_hexSq]; abel
    rw [e]
    exact AddSubgroup.mem_sup_left (AddSubgroup.add_mem_sup
      (neg_mem (sqBd_mem_boxBnd isBoxSq_hexSq)) right_face_mem_pathsIn)
  · intro hmem
    have hker := (sup_le (sup_le le_lam_ker_box le_lam_ker_paths) le_lam_ker_const) hmem
    rw [AddMonoidHom.mem_ker, lam_top_face] at hker
    exact one_ne_zero hker

end

end ClosureExcision
