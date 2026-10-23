import Formalizations.Topology.ClosureSpace.Constructions

/-!
# Products of closure spaces

Two closure spaces have two products on `X × Y`. In the product, boxes `U ×ˢ V` of neighbourhoods
form a base of neighbourhoods; for topological spaces this is the product topology
(`prodSp_ofTop`). In the inductive product, crosses `{x} ×ˢ V ∪ U ×ˢ {y}` form the base; for
closure spaces of relations it is the closure space of the box product of the relations
(`indProd_ofRel`), the product of graphs in which two pairs are adjacent when they agree in one
coordinate and are adjacent in the other. Bubenik and Milićević build cubes from both products.

## Main definitions

* `ClosureSpace.prodSp C D`: the product.
* `ClosureSpace.indProd C D`: the inductive product.

## Main statements

* `ClosureSpace.prodSp_ofTop`: the product of topological spaces is the product topology.
* `ClosureSpace.indProd_ofRel`: the inductive product of closure spaces of relations.

## References

* P. Bubenik and N. Milićević, *Homotopy, homology, and persistent homology using closure
  spaces*, J. Appl. Comput. Topol. 8 (2024), 579-641.
-/

namespace ClosureSpace

open Topology Filter Set

variable {X Y : Type*}

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
