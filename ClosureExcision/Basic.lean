import Mathlib

/-!
# Closure spaces

A Čech closure space is a set with an operator `cl` that preserves the empty set and binary unions
and is extensive. The interior of `s` is the complement of the closure of the complement. On a
finite set a closure is determined by the closures of points, so a reflexive relation `R` gives a
closure space with `cl s = {y | ∃ x ∈ s, R x y}`; graphs are the symmetric case.
-/

namespace ClosureExcision

/-- A Čech closure space on `X`. -/
structure ClosureSpace (X : Type*) where
  cl : Set X → Set X
  cl_empty : cl ∅ = ∅
  subset_cl : ∀ s, s ⊆ cl s
  cl_union : ∀ s t, cl (s ∪ t) = cl s ∪ cl t

namespace ClosureSpace

variable {X : Type*} (C : ClosureSpace X)

theorem cl_mono {s t : Set X} (h : s ⊆ t) : C.cl s ⊆ C.cl t := by
  have h' := C.cl_union s t
  rw [Set.union_eq_right.mpr h] at h'
  rw [h']
  exact Set.subset_union_left

/-- The interior of `s`: the complement of the closure of the complement. -/
def int (s : Set X) : Set X := (C.cl sᶜ)ᶜ

theorem int_subset (s : Set X) : C.int s ⊆ s := by
  intro x hx
  by_contra h
  exact hx (C.subset_cl _ h)

theorem iterate_int_subset (s : Set X) : ∀ m : ℕ, C.int^[m] s ⊆ s
  | 0 => le_rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      exact (C.int_subset _).trans (iterate_int_subset s m)

/-- If `x` lies in the interior of `s` and in the closure of the point `y`, then `y ∈ s`. -/
theorem mem_of_mem_int_of_mem_cl {s : Set X} {x y : X} (hx : x ∈ C.int s)
    (hxy : x ∈ C.cl {y}) : y ∈ s := by
  by_contra hy
  exact hx (C.cl_mono (Set.singleton_subset_iff.mpr hy) hxy)

/-- `W` is a neighbourhood of `x`. -/
def IsNbhd (x : X) (W : Set X) : Prop := x ∈ C.int W

theorem mem_of_isNbhd {x : X} {W : Set X} (h : C.IsNbhd x W) : x ∈ W :=
  C.int_subset W h

/-- `{A, B}` is an interior cover: the interiors of `A` and `B` cover the space. -/
def IsInteriorCover (A B : Set X) : Prop := ∀ x, x ∈ C.int A ∨ x ∈ C.int B

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

end ClosureSpace

end ClosureExcision
