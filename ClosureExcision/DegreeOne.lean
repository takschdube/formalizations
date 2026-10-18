import ClosureExcision.Bridge

/-!
# Excision in degree one, and the circle

In the `(I, ⊡)` theory every `1`-cycle bounds (`box_H1_eq_zero`). Hence, if two points are joined
by a path in `A` and by a path in `B` but by no path in `A ∩ B`, the path in `B` is a relative
cycle of `(B, A ∩ B)` that is null in `(X, A)` but not in `(B, A ∩ B)`.

Main results:
* `box_excision_not_injective_of_joined`: this criterion.
* `circle_interiorCover`, `circle_box_excision_not_injective`: the cover of the unit circle by
  the complements of `1` and `-1`.
-/

namespace ClosureExcision

open Topology Filter
open scoped Real

local notation "𝕀" => unitInterval

noncomputable section

variable {X : Type*} {C : ClosureSpace X}

/-! ## The criterion -/

/-- `x` and `y` are joined by a path in `S`. -/
def JoinedIn (C : ClosureSpace X) (S : Set X) (x y : X) : Prop :=
  ∃ γ, IsPath C γ ∧ (∀ t, γ t ∈ S) ∧ γ 0 = x ∧ γ 1 = y

theorem pext_mem {γ : 𝕀 → X} {S : Set X} (h : ∀ t, γ t ∈ S) (r : ℝ) : pext γ r ∈ S := by
  simp only [pext, Set.IccExtend_apply]
  exact h _

theorem JoinedIn.trans {S : Set X} {x y z : X} (h : JoinedIn C S x y) (h' : JoinedIn C S y z) :
    JoinedIn C S x z := by
  obtain ⟨α, hα, hαS, a0, a1⟩ := h
  obtain ⟨β, hβ, hβS, b0, b1⟩ := h'
  refine ⟨pcat α β, isPath_pcat hα hβ (a1.trans b0.symm), fun t => ?_, by rw [pcat_zero, a0],
    by rw [pcat_one, b1]⟩
  simp only [pcat]
  split_ifs
  · exact pext_mem hαS _
  · exact pext_mem hβS _

theorem JoinedIn.symm {S : Set X} {x y : X} (h : JoinedIn C S x y) : JoinedIn C S y x := by
  obtain ⟨γ, hγ, hS, h0, h1⟩ := h
  exact ⟨rev γ, hγ.rev, fun t => pext_mem hS _, by rw [rev_zero, h1], by rw [rev_one, h0]⟩

open Classical in
/-- `1` at the points joined to `p` by a path in `S`, and `0` elsewhere. -/
def joinInd (C : ClosureSpace X) (S : Set X) (p x : X) : ℤ := if JoinedIn C S p x then 1 else 0

/-- `λ(γ) = h(γ 1) - h(γ 0)` for the indicator `h` of the points joined to `p` in `S`. -/
def joinLam (C : ClosureSpace X) (S : Set X) (p : X) : PChain X →+ ℤ :=
  Finsupp.liftAddHom fun γ => zmultiplesHom ℤ (joinInd C S p (γ 1) - joinInd C S p (γ 0))

theorem joinLam_single (S : Set X) (p : X) (γ : 𝕀 → X) :
    joinLam C S p (Finsupp.single γ 1) = joinInd C S p (γ 1) - joinInd C S p (γ 0) := by
  simp [joinLam]

theorem joinLam_sqBd (S : Set X) (p : X) (σ : 𝕀 × 𝕀 → X) : joinLam C S p (sqBd σ) = 0 := by
  simp only [sqBd, map_add, map_sub, map_neg, joinLam_single, sqA1, sqB1, sqA2, sqB2]
  ring

/-- A path in `S` starts at a point joined to `p` in `S` exactly when it ends at one. -/
theorem joinLam_path {S : Set X} {p : X} {γ : 𝕀 → X} (hγ : IsPath C γ) (hS : ∀ t, γ t ∈ S) :
    joinLam C S p (Finsupp.single γ 1) = 0 := by
  rw [joinLam_single]
  have hj : JoinedIn C S (γ 0) (γ 1) := ⟨γ, hγ, hS, rfl, rfl⟩
  have e : JoinedIn C S p (γ 1) ↔ JoinedIn C S p (γ 0) :=
    ⟨fun h => h.trans hj.symm, fun h => h.trans hj⟩
  unfold joinInd
  by_cases h0 : JoinedIn C S p (γ 0)
  · rw [if_pos (e.mpr h0), if_pos h0, sub_self]
  · rw [if_neg (fun h1 => h0 (e.mp h1)), if_neg h0, sub_self]

/-- **Excision fails in degree one** for `(I, ⊡)` when two points are joined by a path in `A`
and by a path in `B` but by no path in `A ∩ B`. -/
theorem box_excision_not_injective_of_joined {A B : Set X} {p q : X}
    (hA : JoinedIn C A p q) (hB : JoinedIn C B p q) (hAB : ¬ JoinedIn C (A ∩ B) p q) :
    ∃ η : PChain X, η ∈ pathsIn C B ∧ bdPath η ∈ ptsIn (A ∩ B) ∧
      η ∈ boxBnd C Set.univ ⊔ pathsIn C A ⊔ constIn Set.univ ∧
      η ∉ boxBnd C B ⊔ pathsIn C (A ∩ B) ⊔ constIn B := by
  obtain ⟨α, hα, hαA, a0, a1⟩ := hA
  obtain ⟨β, hβ, hβB, b0, b1⟩ := hB
  have hp : p ∈ A ∩ B := ⟨a0 ▸ hαA 0, b0 ▸ hβB 0⟩
  have hq : q ∈ A ∩ B := ⟨a1 ▸ hαA 1, b1 ▸ hβB 1⟩
  have hαmem : Finsupp.single α 1 ∈ pathsIn C A := AddSubgroup.subset_closure ⟨α, hα, hαA, rfl⟩
  have hβmem : Finsupp.single β 1 ∈ pathsIn C B := AddSubgroup.subset_closure ⟨β, hβ, hβB, rfl⟩
  refine ⟨Finsupp.single β 1, hβmem, ?_, ?_, ?_⟩
  · rw [bdPath_single, b1, b0]
    exact sub_mem (AddSubgroup.subset_closure ⟨q, hq, rfl⟩)
      (AddSubgroup.subset_closure ⟨p, hp, rfl⟩)
  · -- `β - α` is a `1`-cycle, so it bounds by `box_H1_eq_zero`
    have hz : Finsupp.single β 1 - Finsupp.single α 1 ∈ pathsIn C Set.univ :=
      sub_mem (pathsIn_mono (Set.subset_univ _) hβmem) (pathsIn_mono (Set.subset_univ _) hαmem)
    have hbd : bdPath (Finsupp.single β 1 - Finsupp.single α 1) = 0 := by
      rw [map_sub, bdPath_single, bdPath_single, a0, a1, b0, b1, sub_self]
    obtain ⟨b, hb, d, hd, hbd'⟩ := AddSubgroup.mem_sup.mp (box_H1_eq_zero C _ hz hbd)
    have e : Finsupp.single β 1 = (b + Finsupp.single α 1) + d := by
      rw [show (b + Finsupp.single α 1) + d = (b + d) + Finsupp.single α 1 by abel, hbd']
      abel
    rw [e]
    exact AddSubgroup.add_mem_sup (AddSubgroup.add_mem_sup hb hαmem) hd
  · intro hmem
    have hle : boxBnd C B ⊔ pathsIn C (A ∩ B) ⊔ constIn B ≤ (joinLam C (A ∩ B) p).ker := by
      refine sup_le (sup_le ?_ ?_) ?_
      · apply (AddSubgroup.closure_le _).mpr
        rintro c ⟨σ, _, _, rfl⟩
        exact joinLam_sqBd _ _ σ
      · apply (AddSubgroup.closure_le _).mpr
        rintro c ⟨γ, hγ, hS, rfl⟩
        exact joinLam_path hγ hS
      · apply (AddSubgroup.closure_le _).mpr
        rintro c ⟨x, _, rfl⟩
        show joinLam C (A ∩ B) p _ = 0
        simp only [joinLam_single, sub_self]
    have hker := hle hmem
    rw [AddMonoidHom.mem_ker, joinLam_single, b1, b0] at hker
    have hpp : JoinedIn C (A ∩ B) p p := ⟨fun _ => p, isPath_const p, fun _ => hp, rfl, rfl⟩
    simp only [joinInd, if_pos hpp, if_neg hAB] at hker
    norm_num at hker

/-! ## Topological spaces -/

theorem isPath_ofTop {Y : Type*} [TopologicalSpace Y] {γ : 𝕀 → Y} (h : Continuous γ) :
    IsPath (ClosureSpace.ofTop Y) γ :=
  fun _ W hW => continuousAt_def.mp h.continuousAt W (ClosureSpace.ofTop_isNbhd.mp hW)

theorem IsPath.continuous_ofTop {Y : Type*} [TopologicalSpace Y] {γ : 𝕀 → Y}
    (h : IsPath (ClosureSpace.ofTop Y) γ) : Continuous γ :=
  continuous_iff_continuousAt.mpr fun t =>
    continuousAt_def.mpr fun W hW => h t W (ClosureSpace.ofTop_isNbhd.mpr hW)

/-! ## The circle -/

/-- The unit circle in `ℂ`. -/
abbrev Circ : Type := Metric.sphere (0 : ℂ) 1

/-- The circle minus `-1`. -/
def circA : Set Circ := {z | (z : ℂ) ≠ -1}

/-- The circle minus `1`. -/
def circB : Set Circ := {z | (z : ℂ) ≠ 1}

theorem circle_interiorCover : (ClosureSpace.ofTop Circ).IsInteriorCover circA circB := by
  have hA : IsOpen circA := isOpen_ne_fun continuous_subtype_val continuous_const
  have hB : IsOpen circB := isOpen_ne_fun continuous_subtype_val continuous_const
  intro z
  by_cases h : (z : ℂ) = 1
  · left
    have hz : z ∈ circA := by
      show (z : ℂ) ≠ -1
      rw [h]
      norm_num
    exact ClosureSpace.ofTop_isNbhd.mpr (hA.mem_nhds hz)
  · right
    exact ClosureSpace.ofTop_isNbhd.mpr (hB.mem_nhds h)

/-- The arc `t ↦ exp((a + (b - a) t) i)`. -/
def arc (a b : ℝ) : 𝕀 → Circ := fun t =>
  ⟨Complex.exp (((a + (b - a) * t : ℝ) : ℂ) * Complex.I), by
    rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]⟩

theorem continuous_arc (a b : ℝ) : Continuous (arc a b) := by
  unfold arc
  exact Continuous.subtype_mk (by fun_prop) _

theorem arc_re (a b : ℝ) (t : 𝕀) : ((arc a b t : Circ) : ℂ).re = Real.cos (a + (b - a) * t) :=
  Complex.exp_ofReal_mul_I_re _

theorem arc_im (a b : ℝ) (t : 𝕀) : ((arc a b t : Circ) : ℂ).im = Real.sin (a + (b - a) * t) :=
  Complex.exp_ofReal_mul_I_im _

/-- The arc from `i` through `1` to `-i` avoids `-1`. -/
theorem arcA_mem (t : 𝕀) : arc (π / 2) (-(π / 2)) t ∈ circA := by
  show ((arc _ _ t : Circ) : ℂ) ≠ -1
  intro h
  have hre := arc_re (π / 2) (-(π / 2)) t
  rw [h] at hre
  have ht0 := unitInterval.nonneg t
  have ht1 := unitInterval.le_one t
  have h1 := mul_nonneg Real.pi_pos.le ht0
  have h2 := mul_nonneg Real.pi_pos.le (sub_nonneg.mpr ht1)
  have hcos : 0 ≤ Real.cos (π / 2 + (-(π / 2) - π / 2) * t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  rw [Complex.neg_re, Complex.one_re] at hre
  linarith

/-- The arc from `i` through `-1` to `-i` avoids `1`. -/
theorem arcB_mem (t : 𝕀) : arc (π / 2) (π + π / 2) t ∈ circB := by
  show ((arc _ _ t : Circ) : ℂ) ≠ 1
  intro h
  have hre := arc_re (π / 2) (π + π / 2) t
  rw [h] at hre
  have ht0 := unitInterval.nonneg t
  have ht1 := unitInterval.le_one t
  have h1 := mul_nonneg Real.pi_pos.le ht0
  have h2 := mul_nonneg Real.pi_pos.le (sub_nonneg.mpr ht1)
  have hcos : Real.cos (π / 2 + (π + π / 2 - π / 2) * t) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith) (by nlinarith)
  rw [Complex.one_re] at hre
  linarith

theorem arcB_zero : arc (π / 2) (π + π / 2) 0 = arc (π / 2) (-(π / 2)) 0 := by
  apply Subtype.ext
  simp [arc]

theorem arcB_one : arc (π / 2) (π + π / 2) 1 = arc (π / 2) (-(π / 2)) 1 := by
  apply Subtype.ext
  apply Complex.ext
  · rw [arc_re, arc_re, Set.Icc.coe_one, mul_one, mul_one,
      show π / 2 + (π + π / 2 - π / 2) = π / 2 + π by ring,
      show π / 2 + (-(π / 2) - π / 2) = -(π / 2) by ring,
      Real.cos_add_pi, Real.cos_neg, Real.cos_pi_div_two, neg_zero]
  · rw [arc_im, arc_im, Set.Icc.coe_one, mul_one, mul_one,
      show π / 2 + (π + π / 2 - π / 2) = π / 2 + π by ring,
      show π / 2 + (-(π / 2) - π / 2) = -(π / 2) by ring,
      Real.sin_add_pi, Real.sin_neg]

theorem eq_one_or_neg_one_of_im_eq_zero {z : ℂ} (hz : ‖z‖ = 1) (him : z.im = 0) :
    z = 1 ∨ z = -1 := by
  have h2 : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hz, one_pow]
  rw [him, mul_zero, add_zero] at h2
  have hre : (z.re - 1) * (z.re + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp hre with h | h
  · left
    exact Complex.ext (by simp; linarith) (by simp [him])
  · right
    exact Complex.ext (by simp; linarith) (by simp [him])

/-- `i` and `-i` are not joined in the circle minus `±1`: the imaginary part would vanish. -/
theorem circle_not_joined : ¬ JoinedIn (ClosureSpace.ofTop Circ) (circA ∩ circB)
    (arc (π / 2) (-(π / 2)) 0) (arc (π / 2) (-(π / 2)) 1) := by
  rintro ⟨γ, hγ, hS, h0, h1⟩
  have hc : Continuous fun t => ((γ t : Circ) : ℂ).im :=
    Complex.continuous_im.comp (continuous_subtype_val.comp hγ.continuous_ofTop)
  have him0 : ((γ 0 : Circ) : ℂ).im = 1 := by
    rw [h0, arc_im]
    simp
  have him1 : ((γ 1 : Circ) : ℂ).im = -1 := by
    rw [h1, arc_im, Set.Icc.coe_one, mul_one,
      show π / 2 + (-(π / 2) - π / 2) = -(π / 2) by ring, Real.sin_neg, Real.sin_pi_div_two]
  have hmem : (0 : ℝ) ∈ Set.Icc ((γ 1 : ℂ).im) ((γ 0 : ℂ).im) := by
    rw [him0, him1]
    norm_num
  obtain ⟨t, ht⟩ := intermediate_value_univ (1 : 𝕀) 0 hc hmem
  have hnorm : ‖((γ t : Circ) : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp (γ t).2
  rcases eq_one_or_neg_one_of_im_eq_zero hnorm ht with h | h
  · exact (hS t).2 h
  · exact (hS t).1 h

/-- **Excision fails for `(I, ⊡)` on the circle**, for the cover by the complements of `1` and
`-1`: the arc from `i` through `-1` to `-i` is a relative cycle that is null in
`(S¹, S¹ \ {-1})` but not in `(S¹ \ {1}, S¹ \ {±1})`. -/
theorem circle_box_excision_not_injective :
    ∃ η : PChain Circ, η ∈ pathsIn (ClosureSpace.ofTop Circ) circB ∧
      bdPath η ∈ ptsIn (circA ∩ circB) ∧
      η ∈ boxBnd (ClosureSpace.ofTop Circ) Set.univ ⊔ pathsIn (ClosureSpace.ofTop Circ) circA ⊔
        constIn Set.univ ∧
      η ∉ boxBnd (ClosureSpace.ofTop Circ) circB ⊔
        pathsIn (ClosureSpace.ofTop Circ) (circA ∩ circB) ⊔ constIn circB :=
  box_excision_not_injective_of_joined
    ⟨_, isPath_ofTop (continuous_arc _ _), arcA_mem, rfl, rfl⟩
    ⟨_, isPath_ofTop (continuous_arc _ _), arcB_mem, arcB_zero, arcB_one⟩
    circle_not_joined

end

end ClosureExcision
