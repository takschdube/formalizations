import ClosureExcision.Cubes
import ClosureExcision.Interval

/-!
# Bridge to the Bubenik–Milićević cubes

`Cubes.lean` and `Interval.lean` define singular cubes by explicit conditions. This file proves
those conditions equivalent to continuity, in Čech's sense (`f (cl s) ⊆ cl (f s)`), of maps out of
the cubes that Bubenik and Milićević build from the product and the inductive product:

* `isPath_iff_continuous`, `isBoxSq_iff_continuous`, `isProdSq_iff_continuous`: paths and squares
  for the unit interval, fact (1) of the paper;
* `isCube_iff_continuous`, `isPlusCube_iff_continuous`: cubes for the two-point intervals,
  facts (2) and (3).
-/

namespace ClosureExcision

open Topology Filter Set

local notation "𝕀" => unitInterval

namespace ClosureSpace

variable {X Y : Type*}

/-! ## Neighborhoods and continuity -/

theorem isNbhd_iff {C : ClosureSpace X} {x : X} {W : Set X} : C.IsNbhd x W ↔ x ∉ C.cl Wᶜ :=
  Iff.rfl

theorem isNbhd_univ (C : ClosureSpace X) (x : X) : C.IsNbhd x Set.univ := by
  rw [isNbhd_iff, compl_univ, C.cl_empty]
  exact Set.notMem_empty x

theorem IsNbhd.inter {C : ClosureSpace X} {x : X} {U V : Set X} (hU : C.IsNbhd x U)
    (hV : C.IsNbhd x V) : C.IsNbhd x (U ∩ V) := by
  rw [isNbhd_iff, compl_inter, C.cl_union]
  rintro (hx | hx)
  · exact hU hx
  · exact hV hx

/-- A point lies in the closure of `s` iff every neighborhood of it meets `s`. -/
theorem mem_cl_iff (C : ClosureSpace X) {s : Set X} {x : X} :
    x ∈ C.cl s ↔ ∀ W, C.IsNbhd x W → (W ∩ s).Nonempty := by
  constructor
  · intro hx W hW
    by_contra h
    exact hW (C.cl_mono (fun y hy hyW => h ⟨y, hyW, hy⟩) hx)
  · intro h
    by_contra hx
    obtain ⟨y, hy1, hy2⟩ := h sᶜ (by rw [isNbhd_iff, compl_compl]; exact hx)
    exact hy1 hy2

theorem ofRel_isNbhd {R : X → X → Prop} {hR : ∀ x, R x x} {x : X} {W : Set X} :
    (ofRel R hR).IsNbhd x W ↔ ∀ y, R y x → y ∈ W :=
  ofRel_mem_int

/-- Čech continuity. -/
def ContinuousMap (C : ClosureSpace X) (D : ClosureSpace Y) (f : X → Y) : Prop :=
  ∀ s, f '' C.cl s ⊆ D.cl (f '' s)

/-- Continuity at a point: preimages of neighborhoods of `f x` are neighborhoods of `x`. -/
def ContinuousAtPt (C : ClosureSpace X) (D : ClosureSpace Y) (f : X → Y) (x : X) : Prop :=
  ∀ W, D.IsNbhd (f x) W → C.IsNbhd x (f ⁻¹' W)

/-- Čech 16.A.4: a map is continuous iff it is continuous at every point. -/
theorem continuousMap_iff_forall_continuousAtPt (C : ClosureSpace X) (D : ClosureSpace Y)
    (f : X → Y) : C.ContinuousMap D f ↔ ∀ x, C.ContinuousAtPt D f x := by
  constructor
  · intro hf x W hW hx
    apply hW
    refine D.cl_mono ?_ (hf _ ⟨x, hx, rfl⟩)
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  · rintro hf s _ ⟨x, hx, rfl⟩
    rw [mem_cl_iff] at hx ⊢
    intro W hW
    obtain ⟨y, hyW, hys⟩ := hx _ (hf x W hW)
    exact ⟨f y, hyW, y, hys, rfl⟩

theorem continuousMap_ofRel {R : X → X → Prop} {hR : ∀ x, R x x} (D : ClosureSpace Y)
    (f : X → Y) : (ofRel R hR).ContinuousMap D f ↔ ∀ x y, R x y → f y ∈ D.cl {f x} := by
  constructor
  · intro hf x y hxy
    have h := hf {x} (Set.mem_image_of_mem f (ofRel_mem_cl_singleton.mpr hxy))
    simpa using h
  · rintro hf s _ ⟨y, ⟨x, hx, hxy⟩, rfl⟩
    exact D.cl_mono (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem f hx)) (hf x y hxy)

theorem ext' {C D : ClosureSpace X} (h : ∀ s, C.cl s = D.cl s) : C = D := by
  cases C
  cases D
  congr
  funext s
  exact h s

theorem ofRel_congr {R R' : X → X → Prop} {hR : ∀ x, R x x} {hR' : ∀ x, R' x x}
    (h : ∀ x y, R x y ↔ R' x y) : ofRel R hR = ofRel R' hR' :=
  ext' fun s => by ext y; simp [ofRel, h]

/-! ## Topological spaces, induced closures and closures from a neighborhood base -/

/-- A topological space as a closure space. -/
def ofTop (X : Type*) [TopologicalSpace X] : ClosureSpace X where
  cl := closure
  cl_empty := closure_empty
  subset_cl _ := subset_closure
  cl_union _ _ := closure_union

theorem ofTop_isNbhd {X : Type*} [TopologicalSpace X] {x : X} {W : Set X} :
    (ofTop X).IsNbhd x W ↔ W ∈ 𝓝 x := by
  show x ∉ closure Wᶜ ↔ _
  rw [closure_compl, Set.mem_compl_iff, not_not, mem_interior_iff_mem_nhds]

/-- The closure induced by a map `g`: `a ∈ cl s` iff `g a ∈ cl (g '' s)`. For a bijection this
transports the closure of the target. -/
def comap {α β : Type*} (g : α → β) (D : ClosureSpace β) : ClosureSpace α where
  cl s := g ⁻¹' D.cl (g '' s)
  cl_empty := by simp [D.cl_empty]
  subset_cl s a ha := D.subset_cl _ ⟨a, ha, rfl⟩
  cl_union s t := by simp [Set.image_union, D.cl_union, Set.preimage_union]

theorem comap_ofRel {α β : Type*} (g : α → β) {R : β → β → Prop} {hR : ∀ x, R x x} :
    comap g (ofRel R hR) = ofRel (fun a b => R (g a) (g b)) (by intro a; exact hR (g a)) :=
  ext' fun s => by ext b; simp [comap, ofRel]

/-- The closure with a given base of neighborhoods `B a` at each point. -/
def ofBase {α : Type*} (B : α → Set (Set α)) (hne : ∀ a, (B a).Nonempty)
    (hmem : ∀ a, ∀ s ∈ B a, a ∈ s)
    (hinter : ∀ a, ∀ s ∈ B a, ∀ t ∈ B a, ∃ u ∈ B a, u ⊆ s ∩ t) : ClosureSpace α where
  cl S := {a | ∀ s ∈ B a, (s ∩ S).Nonempty}
  cl_empty := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.inter_empty, Set.not_nonempty_empty, imp_false,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    exact hne a
  subset_cl S a ha s hs := ⟨a, hmem a s hs, ha⟩
  cl_union S T := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      by_contra hc
      simp only [not_or, not_forall, Set.not_nonempty_iff_eq_empty] at hc
      obtain ⟨⟨s, hs, h1⟩, ⟨t, ht, h2⟩⟩ := hc
      obtain ⟨u, hu, hut⟩ := hinter a s hs t ht
      obtain ⟨y, hyu, hyST⟩ := h u hu
      rcases hyST with hy | hy
      · have : y ∈ s ∩ S := ⟨(hut hyu).1, hy⟩
        rw [h1] at this
        exact this
      · have : y ∈ t ∩ T := ⟨(hut hyu).2, hy⟩
        rw [h2] at this
        exact this
    · rintro (h | h) s hs
      · obtain ⟨y, hys, hy⟩ := h s hs
        exact ⟨y, hys, Or.inl hy⟩
      · obtain ⟨y, hys, hy⟩ := h s hs
        exact ⟨y, hys, Or.inr hy⟩

theorem ofBase_isNbhd {α : Type*} {B : α → Set (Set α)} {hne : ∀ a, (B a).Nonempty}
    {hmem : ∀ a, ∀ s ∈ B a, a ∈ s} {hinter : ∀ a, ∀ s ∈ B a, ∀ t ∈ B a, ∃ u ∈ B a, u ⊆ s ∩ t}
    {a : α} {W : Set α} : (ofBase B hne hmem hinter).IsNbhd a W ↔ ∃ s ∈ B a, s ⊆ W := by
  rw [isNbhd_iff]
  show ¬ (∀ s ∈ B a, (s ∩ Wᶜ).Nonempty) ↔ _
  simp only [not_forall, Set.not_nonempty_iff_eq_empty, ← Set.sdiff_eq, Set.sdiff_eq_empty,
    exists_prop]

/-! ## The inductive product and the product -/

/-- The cross at `p` with arms `U` and `V`. -/
def cross (p : X × Y) (U : Set X) (V : Set Y) : Set (X × Y) :=
  {q | (q.1 = p.1 ∧ q.2 ∈ V) ∨ (q.2 = p.2 ∧ q.1 ∈ U)}

/-- The inductive product: crosses of neighborhoods form a base of neighborhoods. -/
def indProd (C : ClosureSpace X) (D : ClosureSpace Y) : ClosureSpace (X × Y) :=
  ofBase (fun p => {c | ∃ U V, C.IsNbhd p.1 U ∧ D.IsNbhd p.2 V ∧ c = cross p U V})
    (by
      intro p
      exact ⟨cross p univ univ, univ, univ, C.isNbhd_univ p.1, D.isNbhd_univ p.2, rfl⟩)
    (by
      rintro p _ ⟨U, V, -, hV, rfl⟩
      exact Or.inl ⟨rfl, D.mem_of_isNbhd hV⟩)
    (by
      rintro p _ ⟨U, V, hU, hV, rfl⟩ _ ⟨U', V', hU', hV', rfl⟩
      refine ⟨_, ⟨U ∩ U', V ∩ V', hU.inter hU', hV.inter hV', rfl⟩, ?_⟩
      rintro q (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl ⟨h1, h2.1⟩, Or.inl ⟨h1, h2.2⟩⟩
      · exact ⟨Or.inr ⟨h1, h2.1⟩, Or.inr ⟨h1, h2.2⟩⟩)

theorem indProd_isNbhd {C : ClosureSpace X} {D : ClosureSpace Y} {p : X × Y}
    {W : Set (X × Y)} :
    (indProd C D).IsNbhd p W ↔ ∃ U V, C.IsNbhd p.1 U ∧ D.IsNbhd p.2 V ∧ cross p U V ⊆ W := by
  refine ofBase_isNbhd.trans ?_
  constructor
  · rintro ⟨_, ⟨U, V, hU, hV, rfl⟩, h⟩
    exact ⟨U, V, hU, hV, h⟩
  · rintro ⟨U, V, hU, hV, h⟩
    exact ⟨_, ⟨U, V, hU, hV, rfl⟩, h⟩

/-- The product: boxes of neighborhoods form a base of neighborhoods. -/
def prodSp (C : ClosureSpace X) (D : ClosureSpace Y) : ClosureSpace (X × Y) :=
  ofBase (fun p => {c | ∃ U V, C.IsNbhd p.1 U ∧ D.IsNbhd p.2 V ∧ c = U ×ˢ V})
    (by
      intro p
      exact ⟨univ ×ˢ univ, univ, univ, C.isNbhd_univ p.1, D.isNbhd_univ p.2, rfl⟩)
    (by
      rintro p _ ⟨U, V, hU, hV, rfl⟩
      exact ⟨C.mem_of_isNbhd hU, D.mem_of_isNbhd hV⟩)
    (by
      rintro p _ ⟨U, V, hU, hV, rfl⟩ _ ⟨U', V', hU', hV', rfl⟩
      refine ⟨_, ⟨U ∩ U', V ∩ V', hU.inter hU', hV.inter hV', rfl⟩, ?_⟩
      rintro q ⟨h1, h2⟩
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩)

theorem prodSp_isNbhd {C : ClosureSpace X} {D : ClosureSpace Y} {p : X × Y}
    {W : Set (X × Y)} :
    (prodSp C D).IsNbhd p W ↔ ∃ U V, C.IsNbhd p.1 U ∧ D.IsNbhd p.2 V ∧ U ×ˢ V ⊆ W := by
  refine ofBase_isNbhd.trans ?_
  constructor
  · rintro ⟨_, ⟨U, V, hU, hV, rfl⟩, h⟩
    exact ⟨U, V, hU, hV, h⟩
  · rintro ⟨U, V, hU, hV, h⟩
    exact ⟨_, ⟨U, V, hU, hV, rfl⟩, h⟩

/-- For topological spaces the product closure is the product topology. -/
theorem prodSp_ofTop {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {p : X × Y}
    {W : Set (X × Y)} : (prodSp (ofTop X) (ofTop Y)).IsNbhd p W ↔ W ∈ 𝓝 p := by
  rw [prodSp_isNbhd]
  obtain ⟨a, b⟩ := p
  simp only [ofTop_isNbhd]
  rw [mem_nhds_prod_iff]
  constructor
  · rintro ⟨U, V, hU, hV, h⟩
    exact ⟨U, hU, V, hV, h⟩
  · rintro ⟨U, hU, V, hV, h⟩
    exact ⟨U, V, hU, hV, h⟩

/-- On closures of relations the inductive product is the box product. -/
theorem indProd_ofRel {R : X → X → Prop} {S : Y → Y → Prop} {hR : ∀ x, R x x}
    {hS : ∀ y, S y y} :
    indProd (ofRel R hR) (ofRel S hS) =
      ofRel (fun p q => (p.1 = q.1 ∧ S p.2 q.2) ∨ (p.2 = q.2 ∧ R p.1 q.1))
        (by intro p; exact Or.inl ⟨rfl, hS p.2⟩) := by
  refine ext' fun T => ?_
  ext q
  rw [mem_cl_iff]
  constructor
  · intro h
    have hU : (ofRel R hR).IsNbhd q.1 {y | R y q.1} := ofRel_isNbhd.mpr fun _ hy => hy
    have hV : (ofRel S hS).IsNbhd q.2 {y | S y q.2} := ofRel_isNbhd.mpr fun _ hy => hy
    obtain ⟨p, hp, hpT⟩ := h _ (indProd_isNbhd.mpr ⟨_, _, hU, hV, subset_rfl⟩)
    exact ⟨p, hpT, hp⟩
  · rintro ⟨p, hpT, hpq⟩ W hW
    obtain ⟨U, V, hU, hV, hsub⟩ := indProd_isNbhd.mp hW
    rw [ofRel_isNbhd] at hU hV
    refine ⟨p, hsub ?_, hpT⟩
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, hV _ h2⟩
    · exact Or.inr ⟨h1, hU _ h2⟩

end ClosureSpace

open ClosureSpace

variable {X : Type*}

/-! ## Fact (2.1): paths and squares of the unit interval -/

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

/-! ## Facts (2.2) and (2.3): cubes of the two-point intervals -/

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

/-- Fact (2.2): the `(J₁, ⊡)` singular cubes are the maps satisfying `IsCube`. -/
theorem isCube_iff_continuous (C : ClosureSpace X) {n : ℕ} (σ : (Fin n → Bool) → X) :
    C.IsCube σ ↔ (cubeSp J1 n).ContinuousMap C σ := by
  rw [cubeSp_J1, continuousMap_ofRel]
  constructor
  · rintro h x y (rfl | ⟨i, rfl⟩)
    · exact C.subset_cl _ rfl
    · exact h x i
  · intro h x i
    exact h x _ (Or.inr ⟨i, rfl⟩)

/-- Fact (2.3): the `(J₊, ⊡)` singular cubes are the maps satisfying `IsPlusCube`. -/
theorem isPlusCube_iff_continuous (C : ClosureSpace X) {n : ℕ} (σ : (Fin n → Bool) → X) :
    C.IsPlusCube σ ↔ (cubeSp Jplus n).ContinuousMap C σ := by
  rw [cubeSp_Jplus, continuousMap_ofRel]
  constructor
  · rintro h x y (rfl | ⟨i, hi, rfl⟩)
    · exact C.subset_cl _ rfl
    · exact h x i hi
  · intro h x i hi
    exact h x _ (Or.inr ⟨i, hi, rfl⟩)

end ClosureExcision
