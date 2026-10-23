import Mathlib

/-!
# Closure spaces

A Čech closure space is a type with an operator `cl` on its subsets that preserves the empty set
and binary unions and is extensive. The closure of a topology is one, and so is the closure of a
reflexive relation (`ClosureSpace.ofRel`), but `cl` need not be idempotent. The interior of `s` is
the complement of the closure of the complement, and a map is continuous, in Čech's sense, when it
maps the closure of every set into the closure of its image.

## Main definitions

* `ClosureSpace X`: a Čech closure operator on `X`.
* `ClosureSpace.int`, `ClosureSpace.IsNbhd`: interiors and neighbourhoods.
* `ClosureSpace.IsInteriorCover`: the interiors of `A` and `B` cover the space.
* `ClosureSpace.ContinuousMap`, `ClosureSpace.ContinuousAtPt`: continuity, and continuity at a
  point.

## Main statements

* `ClosureSpace.mem_cl_iff`: a point lies in the closure of `s` iff every neighbourhood of it
  meets `s`.
* `ClosureSpace.continuousMap_iff_forall_continuousAtPt`: a map is continuous iff it is continuous
  at every point (Čech 16.A.4).

## References

* E. Čech, *Topological Spaces*, Academia and Interscience, 1966.
-/

/-- A Čech closure space on `X`. -/
structure ClosureSpace (X : Type*) where
  cl : Set X → Set X
  cl_empty : cl ∅ = ∅
  subset_cl : ∀ s, s ⊆ cl s
  cl_union : ∀ s t, cl (s ∪ t) = cl s ∪ cl t

namespace ClosureSpace

section

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

end

open Topology Filter Set

variable {X Y : Type*}

/-! ## Neighbourhoods -/

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

theorem ext' {C D : ClosureSpace X} (h : ∀ s, C.cl s = D.cl s) : C = D := by
  cases C
  cases D
  congr
  funext s
  exact h s

/-! ## Continuity -/

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

end ClosureSpace
