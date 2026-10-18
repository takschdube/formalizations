import ClosureExcision.Cubes

/-!
# The 3-cube: excision fails in degree 2

`Q₃` is the graph on `Fin 3 → Bool` in which corners are adjacent when they differ in one
coordinate, viewed as a closure space. With `A = Q₃ ∖ {111}` and `B = Q₃ ∖ {000}` the interiors
of `A` and `B` cover `Q₃`, but the excision map `H₂(B, A ∩ B) → H₂(Q₃, A)` is not injective.

The witness is the chain `z` of the three faces through `111`, oriented as in the boundary of the
identity cube `ι`. Its boundary is the hexagon `A ∩ B`, so `z` is a relative cycle of `(B, A ∩ B)`.
In `(Q₃, A)` it is null because `∂ι` differs from `z` by the three faces through `000`, which lie in
`A`. In `(B, A ∩ B)` it is not null: the winding number around the hexagon, composed with the
boundary, vanishes on boundaries, on chains in the hexagon and on degenerate chains, and takes the
value `6` on `z`.
-/

namespace ClosureExcision

open Finset

noncomputable section

/-! ## The closure space `Q₃` -/

/-- Corners of the 3-cube are adjacent or equal when they differ in at most one coordinate. -/
abbrev r3 (x y : Fin 3 → Bool) : Prop := (univ.filter fun i => x i ≠ y i).card ≤ 1

theorem r3_refl (x : Fin 3 → Bool) : r3 x x := by simp

/-- The 3-cube graph as a closure space. -/
def q3 : ClosureSpace (Fin 3 → Bool) := ClosureSpace.ofRel r3 r3_refl

/-- `Q₃` without the corner `111`. -/
abbrev A3 : Set (Fin 3 → Bool) := {v | v ≠ fun _ => true}

/-- `Q₃` without the corner `000`. -/
abbrev B3 : Set (Fin 3 → Bool) := {v | v ≠ fun _ => false}

theorem q3_mem_cl_singleton {x y : Fin 3 → Bool} : y ∈ q3.cl {x} ↔ r3 x y :=
  ClosureSpace.ofRel_mem_cl_singleton

theorem q3_mem_int {s : Set (Fin 3 → Bool)} {x : Fin 3 → Bool} :
    x ∈ q3.int s ↔ ∀ y, r3 y x → y ∈ s :=
  ClosureSpace.ofRel_mem_int

/-- The interiors of `A3` and `B3` cover `Q₃`. -/
theorem q3_interiorCover : q3.IsInteriorCover A3 B3 := by
  intro x
  rw [q3_mem_int, q3_mem_int]
  revert x
  decide

/-- The closure of `Q₃` is symmetric. -/
theorem q3_symm : ∀ x y, y ∈ q3.cl {x} → x ∈ q3.cl {y} := by
  intro x y
  rw [q3_mem_cl_singleton, q3_mem_cl_singleton]
  revert x y
  decide

/-- On `Q₃` the directed interval `J₊` and the undirected interval `J₁` give the same cubes. -/
theorem q3_isCube_iff_isPlusCube {n : ℕ} (σ : (Fin n → Bool) → (Fin 3 → Bool)) :
    q3.IsCube σ ↔ q3.IsPlusCube σ :=
  isCube_iff_isPlusCube q3_symm σ

/-! ## `∂∂ = 0` on 3-cubes -/

theorem face_face_01 {X : Type*} (τ : (Fin 3 → Bool) → X) (b c : Bool) :
    face 0 c (face 0 b τ) = face 0 b (face 1 c τ) := by
  funext y
  simp only [face]
  congr 1
  revert b c y
  decide

theorem face_face_02 {X : Type*} (τ : (Fin 3 → Bool) → X) (b c : Bool) :
    face 1 c (face 0 b τ) = face 0 b (face 2 c τ) := by
  funext y
  simp only [face]
  congr 1
  revert b c y
  decide

theorem face_face_12 {X : Type*} (τ : (Fin 3 → Bool) → X) (b c : Bool) :
    face 1 c (face 1 b τ) = face 1 b (face 2 c τ) := by
  funext y
  simp only [face]
  congr 1
  revert b c y
  decide

/-- `∂∂ = 0` on a single 3-cube, for any target. -/
theorem bd_bd_three {X : Type*} (τ : (Fin 3 → Bool) → X) :
    bd 1 (bd 2 (Finsupp.single τ 1)) = 0 := by
  rw [bd_single]
  simp only [bdCube, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, map_add, map_zsmul,
    map_sub, bd_single]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [face_face_01, face_face_02, face_face_12]
  simp only [sgn, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  abel

/-- `∂∂ = 0` on all 3-chains. -/
theorem bd_bd_three' {X : Type*} (w : Chain X 3) : bd 1 (bd 2 w) = 0 := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single τ k =>
      have h : Finsupp.single τ k = k • Finsupp.single τ 1 := by simp
      rw [h, map_zsmul, map_zsmul, bd_bd_three, smul_zero]

/-! ## The winding number around the hexagon `A3 ∩ B3` -/

/-- Position on the hexagon `100 → 110 → 010 → 011 → 001 → 101`; `6` off the hexagon. -/
def hexIdx (v : Fin 3 → Bool) : ℕ :=
  if v = ![true, false, false] then 0
  else if v = ![true, true, false] then 1
  else if v = ![false, true, false] then 2
  else if v = ![false, true, true] then 3
  else if v = ![false, false, true] then 4
  else if v = ![true, false, true] then 5
  else 6

/-- `+1` for a step forward along the hexagon, `-1` for a step back, `0` otherwise. -/
def wind (a b : Fin 3 → Bool) : ℤ :=
  if hexIdx a < 6 ∧ hexIdx b < 6 then
    if hexIdx b = (hexIdx a + 1) % 6 then 1
    else if hexIdx a = (hexIdx b + 1) % 6 then -1 else 0
  else 0

theorem wind_self (a : Fin 3 → Bool) : wind a a = 0 := by
  revert a
  decide

/-- The winding cochain on 1-chains, read from the two corners of each edge. -/
def W : Chain (Fin 3 → Bool) 1 →+ ℤ :=
  Finsupp.liftAddHom fun e => zmultiplesHom ℤ (wind (e fun _ => false) (e fun _ => true))

theorem W_single (e : (Fin 1 → Bool) → (Fin 3 → Bool)) :
    W (Finsupp.single e 1) = wind (e fun _ => false) (e fun _ => true) := by
  simp [W]

/-- Circulation of the winding cochain around a square with corners `a = ρ 00`, `b = ρ 10`,
`c = ρ 01`, `d = ρ 11` (first coordinate written first). -/
def circ (a b c d : Fin 3 → Bool) : ℤ := -wind a c + wind b d + wind a b - wind c d

theorem W_bdCube (ρ : (Fin 2 → Bool) → (Fin 3 → Bool)) :
    W (bdCube ρ) = circ (ρ ![false, false]) (ρ ![true, false]) (ρ ![false, true])
      (ρ ![true, true]) := by
  have e1 : Fin.insertNth (0 : Fin 2) false (fun _ : Fin 1 => false) = ![false, false] := by
    decide
  have e2 : Fin.insertNth (0 : Fin 2) false (fun _ : Fin 1 => true) = ![false, true] := by
    decide
  have e3 : Fin.insertNth (0 : Fin 2) true (fun _ : Fin 1 => false) = ![true, false] := by
    decide
  have e4 : Fin.insertNth (0 : Fin 2) true (fun _ : Fin 1 => true) = ![true, true] := by
    decide
  have e5 : Fin.insertNth (1 : Fin 2) false (fun _ : Fin 1 => false) = ![false, false] := by
    decide
  have e6 : Fin.insertNth (1 : Fin 2) false (fun _ : Fin 1 => true) = ![true, false] := by
    decide
  have e7 : Fin.insertNth (1 : Fin 2) true (fun _ : Fin 1 => false) = ![false, true] := by
    decide
  have e8 : Fin.insertNth (1 : Fin 2) true (fun _ : Fin 1 => true) = ![true, true] := by
    decide
  simp only [bdCube, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, map_add, map_zsmul,
    map_sub, W_single]
  simp only [Fin.succ_zero_eq_one]
  simp only [face]
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  simp only [sgn, circ, Fin.val_zero, Fin.val_one]
  norm_num
  ring

/-- Hexagon vertices: the corners other than `000` and `111`. -/
abbrev L3 : Set (Fin 3 → Bool) := {v | v ≠ (fun _ => true) ∧ v ≠ (fun _ => false)}

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
set_option maxRecDepth 100000 in
/-- A closed walk of length four on the hexagon does not wind around it. -/
theorem circ_zero : ∀ a b c d : Fin 3 → Bool, a ∈ L3 → b ∈ L3 → c ∈ L3 → d ∈ L3 →
    r3 a b → r3 a c → r3 b d → r3 c d → circ a b c d = 0 := by
  decide

theorem L3_eq : A3 ∩ B3 = L3 := by
  ext v
  simp

/-- The cochain `Φ = W ∘ ∂` on 2-chains. -/
def Φ : Chain (Fin 3 → Bool) 2 →+ ℤ := W.comp (bd 1)

theorem Φ_single (ρ : (Fin 2 → Bool) → (Fin 3 → Bool)) :
    Φ (Finsupp.single ρ 1) = circ (ρ ![false, false]) (ρ ![true, false]) (ρ ![false, true])
      (ρ ![true, true]) := by
  simp only [Φ, AddMonoidHom.coe_comp, Function.comp_apply, bd_single, W_bdCube]

theorem flip_00_0 : flipAt (![false, false] : Fin 2 → Bool) 0 = ![true, false] := by decide
theorem flip_00_1 : flipAt (![false, false] : Fin 2 → Bool) 1 = ![false, true] := by decide
theorem flip_10_1 : flipAt (![true, false] : Fin 2 → Bool) 1 = ![true, true] := by decide
theorem flip_01_0 : flipAt (![false, true] : Fin 2 → Bool) 0 = ![true, true] := by decide

theorem Φ_cube_L3 {ρ : (Fin 2 → Bool) → (Fin 3 → Bool)} (hρ : q3.IsCube ρ)
    (hL : InSet (A3 ∩ B3) ρ) : Φ (Finsupp.single ρ 1) = 0 := by
  rw [Φ_single]
  rw [L3_eq] at hL
  have h1 := hρ ![false, false] 0
  have h2 := hρ ![false, false] 1
  have h3 := hρ ![true, false] 1
  have h4 := hρ ![false, true] 0
  rw [flip_00_0, q3_mem_cl_singleton] at h1
  rw [flip_00_1, q3_mem_cl_singleton] at h2
  rw [flip_10_1, q3_mem_cl_singleton] at h3
  rw [flip_01_0, q3_mem_cl_singleton] at h4
  exact circ_zero _ _ _ _ (hL _) (hL _) (hL _) (hL _) h1 h2 h3 h4

theorem Φ_degenerate {ρ : (Fin 2 → Bool) → (Fin 3 → Bool)} (hdeg : IsDegenerate ρ) :
    Φ (Finsupp.single ρ 1) = 0 := by
  rw [Φ_single]
  obtain ⟨i, hi⟩ := hdeg
  fin_cases i
  · have k1 := hi ![false, false]
    have k2 := hi ![false, true]
    have u1 : Function.update (![false, false] : Fin 2 → Bool) 0 false = ![false, false] := by
      decide
    have u2 : Function.update (![false, false] : Fin 2 → Bool) 0 true = ![true, false] := by
      decide
    have u3 : Function.update (![false, true] : Fin 2 → Bool) 0 false = ![false, true] := by
      decide
    have u4 : Function.update (![false, true] : Fin 2 → Bool) 0 true = ![true, true] := by
      decide
    simp only [Fin.zero_eta, Fin.isValue] at k1 k2
    rw [u1, u2] at k1
    rw [u3, u4] at k2
    rw [← k1, ← k2]
    simp [circ, wind_self]
  · have k1 := hi ![false, false]
    have k2 := hi ![true, false]
    have u1 : Function.update (![false, false] : Fin 2 → Bool) 1 false = ![false, false] := by
      decide
    have u2 : Function.update (![false, false] : Fin 2 → Bool) 1 true = ![false, true] := by
      decide
    have u3 : Function.update (![true, false] : Fin 2 → Bool) 1 false = ![true, false] := by
      decide
    have u4 : Function.update (![true, false] : Fin 2 → Bool) 1 true = ![true, true] := by
      decide
    simp only [Fin.mk_one, Fin.isValue] at k1 k2
    rw [u1, u2] at k1
    rw [u3, u4] at k2
    rw [← k1, ← k2]
    simp [circ, wind_self]

/-- `Φ` vanishes on everything that is null in `(B3, A3 ∩ B3)` in degree 2. -/
theorem Φ_eq_zero_of_null {z : Chain (Fin 3 → Bool) 2} (hz : NullRel q3 B3 (A3 ∩ B3) 2 z) :
    Φ z = 0 := by
  have hb : bndIn q3 B3 2 ≤ Φ.ker := by
    rintro _ ⟨w, _, rfl⟩
    simp only [AddMonoidHom.mem_ker, Φ, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [bd_bd_three', map_zero]
  have hc : cubesIn q3 (A3 ∩ B3) 2 ≤ Φ.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro c ⟨ρ, hρ, hL, rfl⟩
    exact Φ_cube_L3 hρ hL
  have hd : degIn q3 B3 2 ≤ Φ.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro c ⟨ρ, _, _, hdeg, rfl⟩
    exact Φ_degenerate hdeg
  exact (sup_le (sup_le hb hc) hd) hz

/-! ## The witness -/

/-- The identity 3-cube of `Q₃`. -/
def ι3 : (Fin 3 → Bool) → (Fin 3 → Bool) := id

theorem ι3_isCube : q3.IsCube ι3 := by
  intro x i
  rw [q3_mem_cl_singleton]
  simp only [ι3, id]
  revert x i
  decide

/-- The three faces through `000`, with the signs they carry in `∂ι`. -/
def u3 : Chain (Fin 3 → Bool) 2 :=
  ∑ i : Fin 3, sgn i • Finsupp.single (face i false ι3) 1

/-- The three faces through `111`, with the signs they carry in `∂ι`. -/
def z3 : Chain (Fin 3 → Bool) 2 :=
  -∑ i : Fin 3, sgn i • Finsupp.single (face i true ι3) 1

theorem bd_ι3 : bd 2 (Finsupp.single ι3 1) = u3 + z3 := by
  rw [bd_single, bdCube, u3, z3]
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

theorem face_false_mem_A3 (i : Fin 3) : InSet A3 (face i false ι3) := by
  intro y h
  have := congrFun h i
  simp [face, ι3] at this

theorem face_true_mem_B3 (i : Fin 3) : InSet B3 (face i true ι3) := by
  intro y h
  have := congrFun h i
  simp [face, ι3] at this

theorem u3_mem : u3 ∈ cubesIn q3 A3 2 := by
  apply AddSubgroup.sum_mem
  intro i _
  exact AddSubgroup.zsmul_mem _ (single_mem_cubesIn (ι3_isCube.face i false)
    (face_false_mem_A3 i)) _

theorem z3_mem : z3 ∈ cubesIn q3 B3 2 := by
  apply neg_mem
  apply AddSubgroup.sum_mem
  intro i _
  exact AddSubgroup.zsmul_mem _ (single_mem_cubesIn (ι3_isCube.face i true)
    (face_true_mem_B3 i)) _

theorem Φ_z3 : Φ z3 = 6 := by
  simp only [z3, Fin.sum_univ_three, map_neg, map_add, map_zsmul, Φ_single, sgn,
    Fin.val_zero, Fin.val_one, Fin.val_two]
  simp only [face, ι3, id]
  decide

/-- **Theorem B.** For the interior cover `{A3, B3}` of `Q₃`, the chain `z3` is a relative
2-cycle of `(B3, A3 ∩ B3)` that is null in `(Q₃, A3)` but not in `(B3, A3 ∩ B3)`: the excision
map `H₂(B3, A3 ∩ B3) → H₂(Q₃, A3)` is not injective. -/
theorem q3_excision_not_injective :
    ∃ z : Chain (Fin 3 → Bool) 2, IsRelCycle q3 B3 (A3 ∩ B3) 1 z ∧
      NullRel q3 Set.univ A3 2 z ∧ ¬ NullRel q3 B3 (A3 ∩ B3) 2 z := by
  refine ⟨z3, ⟨z3_mem, ?_⟩, ?_, ?_⟩
  · -- the boundary of `z3` lies in `A3` (it is `-∂u3`) and in `B3`, hence in `A3 ∩ B3`
    apply AddSubgroup.mem_sup_left
    have hA : bd 1 z3 ∈ cubesIn q3 A3 1 := by
      have h : bd 1 z3 = -bd 1 u3 := by
        have := congrArg (bd 1) bd_ι3
        rw [bd_bd_three, map_add] at this
        rw [eq_neg_iff_add_eq_zero, add_comm, ← this]
      rw [h]
      exact neg_mem (bd_mem_cubesIn u3_mem)
    have hB : bd 1 z3 ∈ cubesIn q3 B3 1 := bd_mem_cubesIn z3_mem
    rw [← proj_eq_self hB]
    exact proj_mem_inter hA
  · -- `z3 = ∂ι3 - u3`
    have h : z3 = bd 2 (Finsupp.single ι3 1) + -u3 := by rw [bd_ι3]; abel
    rw [NullRel, h]
    refine AddSubgroup.mem_sup_left (AddSubgroup.add_mem_sup ?_ (neg_mem u3_mem))
    exact ⟨Finsupp.single ι3 1, single_mem_cubesIn ι3_isCube (fun _ => Set.mem_univ _), rfl⟩
  · intro hnull
    have := Φ_eq_zero_of_null hnull
    rw [Φ_z3] at this
    norm_num at this

end

end ClosureExcision
