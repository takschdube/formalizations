import Formalizations.Topology.ClosureSpace.Basic

/-!
# Constructions of closure spaces

On a finite set a closure is determined by the closures of points, so a reflexive relation `R`
gives a closure space with `cl s = {y | ∃ x ∈ s, R x y}`; graphs are the symmetric case. A
topological space is a closure space with its topological closure, and the neighbourhoods are the
same (`ofTop_isNbhd`).

## Main definitions

* `ClosureSpace.ofRel R`: the closure space of a reflexive relation `R`.
* `ClosureSpace.ofTop X`: a topological space as a closure space.
* `ClosureSpace.comap g D`: the closure induced by a map `g`.
* `ClosureSpace.ofBase B`: the closure with a given base `B a` of neighbourhoods at each point.

## Main statements

* `ClosureSpace.continuousMap_ofRel`: a map out of the closure space of `R` is continuous iff it
  maps each `R`-related pair `x, y` to a point `f y` in the closure of `f x`.
* `ClosureSpace.ofTop_isNbhd`: the neighbourhoods of `ofTop X` are those of the topology.
-/

namespace ClosureSpace

open Topology Filter Set

variable {X Y : Type*}

/-! ## Closure spaces of relations -/

/-- The closure space of a reflexive relation: `y ∈ cl s` iff `R x y` for some `x ∈ s`. -/
def ofRel (R : X → X → Prop) (hR : ∀ x, R x x) : ClosureSpace X where
  cl s := {y | ∃ x ∈ s, R x y}
  cl_empty := by ext; simp
  subset_cl s x hx := ⟨x, hx, hR x⟩
  cl_union s t := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨x, hx | hx, h⟩
      · exact Or.inl ⟨x, hx, h⟩
      · exact Or.inr ⟨x, hx, h⟩
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, Or.inl hx, h⟩
      · exact ⟨x, Or.inr hx, h⟩

section

variable {R : X → X → Prop} {hR : ∀ x, R x x}

theorem ofRel_mem_cl_singleton {x y : X} : y ∈ (ofRel R hR).cl {x} ↔ R x y := by
  simp [ofRel]

theorem ofRel_mem_int {s : Set X} {x : X} :
    x ∈ (ofRel R hR).int s ↔ ∀ y, R y x → y ∈ s := by
  simp only [int, ofRel, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and]
  constructor
  · intro h y hyx
    by_contra hy
    exact h y hy hyx
  · intro h y hy hyx
    exact hy (h y hyx)

end

theorem ofRel_isNbhd {R : X → X → Prop} {hR : ∀ x, R x x} {x : X} {W : Set X} :
    (ofRel R hR).IsNbhd x W ↔ ∀ y, R y x → y ∈ W :=
  ofRel_mem_int

theorem continuousMap_ofRel {R : X → X → Prop} {hR : ∀ x, R x x} (D : ClosureSpace Y)
    (f : X → Y) : (ofRel R hR).ContinuousMap D f ↔ ∀ x y, R x y → f y ∈ D.cl {f x} := by
  constructor
  · intro hf x y hxy
    have h := hf {x} (Set.mem_image_of_mem f (ofRel_mem_cl_singleton.mpr hxy))
    simpa using h
  · rintro hf s _ ⟨y, ⟨x, hx, hxy⟩, rfl⟩
    exact D.cl_mono (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem f hx)) (hf x y hxy)

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

end ClosureSpace
