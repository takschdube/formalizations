import Formalizations.AlgebraicTopology.CubicalHomology.UnitInterval.Homology

/-!
# The six-cycle: excision fails for `(I, ⊡)`

`C₆` is the six-cycle on `ZMod 6` as a closure space, with the interior cover by
`A₆ = C₆ ∖ {5}` and `B₆ = C₆ ∖ {2}`. The hexagon loop `t ↦ ⌊6t⌋ mod 6` is a path, and the top
face `η` of its sector square runs from `0` to `3` inside `B₆`. It is a relative cycle of
`(B₆, A₆ ∩ B₆)` that is null in `(C₆, A₆)`, because it differs from the right face, which lies in
`A₆`, by the boundary of the sector square. It is not null in `(B₆, A₆ ∩ B₆)`: the cochain
`λ(γ) = h(γ 1) - h(γ 0)`, with `h` the indicator of `{3, 4}`, vanishes on boundaries of squares, on
paths in `A₆ ∩ B₆` and on constant paths, and takes the value `1` on `η`.

## Main statements

* `ClosureExcision.c6_interiorCover`: `A₆` and `B₆` form an interior cover of `C₆`.
* `ClosureExcision.c6_box_excision_not_injective`: [DT], Theorem 3 (a) for the six-cycle.

## References

* [DT] T. Dube and A. Tregub, *Excision fails for inductive-product cubical homology of closure
  spaces*.
-/

namespace ClosureExcision

open Topology Filter ClosureSpace

local notation "𝕀" => unitInterval

noncomputable section

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

/-! ## The hexagon loop and its sector square -/

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

/-! ## The detecting cochain -/

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
    filter_upwards [IsPath.c6Rel_eventually hγ t] with s hs
    exact (hstep _ _ (hS' s).1 (hS' s).2 (hS' t).1 (hS' t).2 hs).mpr ht
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    exact isOpen_iff_mem_nhds.mpr fun t ht => by
      filter_upwards [IsPath.c6Rel_eventually hγ t] with s hs hs'
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

/-- **Excision fails for `(I, ⊡)`** ([DT], Theorem 3 (a)). The top face `η` of the sector square
of the hexagon loop is a relative cycle of `(B₆, A₆ ∩ B₆)` that is null in `(C₆, A₆)` but not in
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
