import Formalizations.AlgebraicTopology.CubicalHomology.UnitInterval.Chain

/-!
# Paths and squares in degree one

In the `(I, ⊡)` theory every `1`-cycle of every closure space bounds. A loop `ℓ` bounds by the
sector square, which runs `ℓ` along an angular parameter in one quadrant of `𝕀 × 𝕀` and is
constant elsewhere: it is continuous along every horizontal and every vertical line, so it is a
box square. A `1`-cycle then bounds after each point is joined to a base point of its path
component. Hence excision fails in degree one whenever two points are joined by a path in `A` and
by a path in `B` but by no path in `A ∩ B`.

## Main statements

* `ClosureSpace.isBoxSq_sector`: the sector square of a loop is a box square ([DT], Lemma 3).
* `ClosureSpace.loop_mem_null`: every loop bounds.
* `ClosureSpace.box_H1_eq_zero`: every `1`-cycle bounds ([DT], Theorem 3 (b)).
* `ClosureSpace.box_excision_not_injective_of_joined`: the excision map in degree one is not
  injective when two points are joined in `A` and in `B` but not in `A ∩ B` ([DT],
  Proposition 2).

## References

* [DT] T. Dube and A. Tregub, *Excision fails for inductive-product cubical homology of closure
  spaces*.
-/

namespace ClosureSpace

open Topology Filter

local notation "𝕀" => unitInterval

noncomputable section

variable {X : Type*} {C : ClosureSpace X}

/-! ## The sector square -/

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

/-! ## Loops bound -/

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

/-! ## Excision in degree one -/

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

end

end ClosureSpace
