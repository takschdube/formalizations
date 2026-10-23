import Formalizations.AlgebraicTopology.CubicalHomology.UnitInterval.Homology

/-!
# The circle: excision fails for `(I, ⊡)`

The unit circle `S¹` in `ℂ`, with the closure of its topology, is covered by the interiors of
`S¹ ∖ {-1}` and `S¹ ∖ {1}`. The points `i` and `-i` are joined by the arc through `1` in the first
set and by the arc through `-1` in the second, but by no path in the intersection, since a path
from `i` to `-i` crosses the real axis. By the degree-one criterion
`ClosureSpace.box_excision_not_injective_of_joined`, the excision map is not injective.

## Main statements

* `ClosureExcision.circle_interiorCover`: the cover of the circle.
* `ClosureExcision.circle_box_excision_not_injective`: [DT], Theorem 3 (a) for the circle.

## References

* [DT] T. Dube and A. Tregub, *Excision fails for inductive-product cubical homology of closure
  spaces*.
-/

namespace ClosureExcision

open Topology Filter ClosureSpace
open scoped Real

local notation "𝕀" => unitInterval

noncomputable section

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
theorem circle_not_joined : ¬ ClosureSpace.JoinedIn (ClosureSpace.ofTop Circ) (circA ∩ circB)
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

/-- **Excision fails for `(I, ⊡)` on the circle** ([DT], Theorem 3 (a)), for the cover by the
complements of `1` and `-1`: the arc from `i` through `-1` to `-i` is a relative cycle that is null
in `(S¹, S¹ \ {-1})` but not in `(S¹ \ {1}, S¹ \ {±1})`. -/
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
