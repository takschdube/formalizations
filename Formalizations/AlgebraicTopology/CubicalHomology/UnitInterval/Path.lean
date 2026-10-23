import Formalizations.Topology.ClosureSpace.Product

/-!
# Paths and squares

Singular `1`-cubes for the unit interval `𝕀` are paths `γ : 𝕀 → X`, continuous from the topology
of `𝕀` to the closure of `X` (`IsPath`), and singular `2`-cubes are maps `σ : 𝕀 × 𝕀 → X`. For the
inductive product `𝕀 ⊡ 𝕀` the canonical neighbourhoods are crosses, so a square is continuous when
it is continuous along every horizontal and every vertical line (`IsBoxSq`); for the product it is
continuous for the product topology (`IsProdSq`). Every product square is a box square.

## Main definitions

* `ClosureSpace.IsPath`, `ClosureSpace.IsBoxSq`, `ClosureSpace.IsProdSq`: paths, and squares for
  the inductive product and for the product.
* `ClosureSpace.pext γ`: the path `γ` extended to `ℝ` by clamping, for reparametrizations.
* `ClosureSpace.rev`, `ClosureSpace.pcat`: reversal and concatenation of paths.
* `ClosureSpace.Joined`, `ClosureSpace.JoinedIn`: points joined by a path, and by a path in `S`.

## Main statements

* `ClosureSpace.isPath_iff_continuous`, `ClosureSpace.isBoxSq_iff_continuous`,
  `ClosureSpace.isProdSq_iff_continuous`: the definitions are continuity on `𝕀`, on `𝕀 ⊡ 𝕀` and
  on `𝕀 × 𝕀` ([DT], (1)).
* `ClosureSpace.isProdSq_isBoxSq`: product squares are box squares.
* `ClosureSpace.IsPath.pext_comp`: a path composed with a continuous real function is continuous.
* `ClosureSpace.isPath_ofTop`, `ClosureSpace.IsPath.continuous_ofTop`: in a topological space the
  paths are the continuous paths.

## References

* [DT] T. Dube and A. Tregub, *Excision fails for inductive-product cubical homology of closure
  spaces*.
-/

namespace ClosureSpace

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

/-! ## Continuity on `𝕀`, `𝕀 ⊡ 𝕀` and `𝕀 × 𝕀` -/

theorem isPath_iff_continuous (C : ClosureSpace X) (γ : 𝕀 → X) :
    IsPath C γ ↔ (ofTop 𝕀).ContinuousMap C γ := by
  rw [continuousMap_iff_forall_continuousAtPt]
  simp only [ContinuousAtPt, ofTop_isNbhd]
  exact Iff.rfl

theorem isProdSq_iff_continuous (C : ClosureSpace X) (σ : 𝕀 × 𝕀 → X) :
    IsProdSq C σ ↔ (prodSp (ofTop 𝕀) (ofTop 𝕀)).ContinuousMap C σ := by
  rw [continuousMap_iff_forall_continuousAtPt]
  simp only [ContinuousAtPt, prodSp_ofTop]
  exact Iff.rfl

theorem isBoxSq_iff_continuous (C : ClosureSpace X) (σ : 𝕀 × 𝕀 → X) :
    IsBoxSq C σ ↔ (indProd (ofTop 𝕀) (ofTop 𝕀)).ContinuousMap C σ := by
  rw [continuousMap_iff_forall_continuousAtPt]
  constructor
  · intro h p W hW
    obtain ⟨h1, h2⟩ := h p W hW
    refine indProd_isNbhd.mpr ⟨{s | σ (s, p.2) ∈ W}, {t | σ (p.1, t) ∈ W},
      ofTop_isNbhd.mpr h1, ofTop_isNbhd.mpr h2, ?_⟩
    rintro ⟨a, b⟩ (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · simp only at h1 h2
      subst h1
      exact h2
    · simp only at h1 h2
      subst h1
      exact h2
  · intro h p W hW
    obtain ⟨U, V, hU, hV, hsub⟩ := indProd_isNbhd.mp (h p W hW)
    rw [ofTop_isNbhd] at hU hV
    constructor
    · filter_upwards [hU] with s hs
      exact hsub (show (s, p.2) ∈ cross p U V from Or.inr ⟨rfl, hs⟩)
    · filter_upwards [hV] with t ht
      exact hsub (show (p.1, t) ∈ cross p U V from Or.inl ⟨rfl, ht⟩)

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

theorem pext_mem {γ : 𝕀 → X} {S : Set X} (h : ∀ t, γ t ∈ S) (r : ℝ) : pext γ r ∈ S := by
  simp only [pext, Set.IccExtend_apply]
  exact h _

theorem IsPath.contAt_pext {γ : 𝕀 → X} (hγ : IsPath C γ) (r : ℝ) : ContAt C (pext γ) r :=
  ContAt.comp (g := Set.projIcc (0 : ℝ) 1 zero_le_one) (hγ _)
    (continuous_projIcc).continuousAt

/-- Composing the extension of a path with a continuous real function gives a continuous map. -/
theorem IsPath.pext_comp {T : Type*} [TopologicalSpace T] {γ : 𝕀 → X} (hγ : IsPath C γ)
    {f : T → ℝ} (hf : Continuous f) (t : T) : ContAt C (fun s => pext γ (f s)) t :=
  ContAt.comp (f := pext γ) (g := f) (hγ.contAt_pext (f t)) hf.continuousAt

/-! ## Faces of squares -/

/-- Faces of a square: `A₁, B₁` fix the first coordinate to `0, 1`; `A₂, B₂` the second. -/
def sqA1 (σ : 𝕀 × 𝕀 → X) : 𝕀 → X := fun t => σ (0, t)
def sqB1 (σ : 𝕀 × 𝕀 → X) : 𝕀 → X := fun t => σ (1, t)
def sqA2 (σ : 𝕀 × 𝕀 → X) : 𝕀 → X := fun s => σ (s, 0)
def sqB2 (σ : 𝕀 × 𝕀 → X) : 𝕀 → X := fun s => σ (s, 1)

theorem IsBoxSq.isPath_sqB1 {σ : 𝕀 × 𝕀 → X} (h : IsBoxSq C σ) : IsPath C (sqB1 σ) :=
  fun t W hW => (h (1, t) W hW).2

theorem IsBoxSq.isPath_sqB2 {σ : 𝕀 × 𝕀 → X} (h : IsBoxSq C σ) : IsPath C (sqB2 σ) :=
  fun s W hW => (h (s, 1) W hW).1

/-! ## Reversal and concatenation -/

/-- The reversed path. -/
def rev (γ : 𝕀 → X) : 𝕀 → X := fun t => pext γ (1 - t)

theorem IsPath.rev {γ : 𝕀 → X} (hγ : IsPath C γ) : IsPath C (rev γ) :=
  fun t => hγ.pext_comp (f := fun s : 𝕀 => 1 - (s : ℝ)) (by fun_prop) t

theorem rev_zero (γ : 𝕀 → X) : rev γ 0 = γ 1 := by
  simp [rev, pext_one]

theorem rev_one (γ : 𝕀 → X) : rev γ 1 = γ 0 := by
  simp [rev, pext_zero]

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

/-! ## Joined points -/

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

/-- `x` and `y` are joined by a path in `S`. -/
def JoinedIn (C : ClosureSpace X) (S : Set X) (x y : X) : Prop :=
  ∃ γ, IsPath C γ ∧ (∀ t, γ t ∈ S) ∧ γ 0 = x ∧ γ 1 = y

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

/-! ## Topological spaces -/

theorem isPath_ofTop {Y : Type*} [TopologicalSpace Y] {γ : 𝕀 → Y} (h : Continuous γ) :
    IsPath (ClosureSpace.ofTop Y) γ :=
  fun _ W hW => continuousAt_def.mp h.continuousAt W (ClosureSpace.ofTop_isNbhd.mp hW)

theorem IsPath.continuous_ofTop {Y : Type*} [TopologicalSpace Y] {γ : 𝕀 → Y}
    (h : IsPath (ClosureSpace.ofTop Y) γ) : Continuous γ :=
  continuous_iff_continuousAt.mpr fun t =>
    continuousAt_def.mpr fun W hW => h t W (ClosureSpace.ofTop_isNbhd.mpr hW)

end

end ClosureSpace
