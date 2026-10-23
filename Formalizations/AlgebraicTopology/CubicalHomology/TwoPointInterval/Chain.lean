import Formalizations.AlgebraicTopology.CubicalHomology.TwoPointInterval.Cube

/-!
# Cubical chains and normalized relative homology

Chains are finitely supported integer combinations of maps from the corners of the `n`-cube, the
boundary is `∂σ = ∑ᵢ (-1)^(i+1) (σ|xᵢ=0 - σ|xᵢ=1)` (coordinates counted from `0`), and a cube is
degenerate when it does not depend on some coordinate. Relative homology is normalized: a chain
`z` of cubes in `S` is a relative cycle of `(S, T)` when `∂z` lies in the span of the cubes in `T`
and the degenerate cubes in `S`, and it is null when it lies in the span of the boundaries of
cubes in `S`, the cubes in `T` and the degenerate cubes in `S`.

## Main definitions

* `ClosureSpace.Chain X n`, `ClosureSpace.bd n`: chains and the boundary.
* `ClosureSpace.cubesIn C S n`, `ClosureSpace.degIn C S n`, `ClosureSpace.bndIn C S n`: chains
  of cubes, of degenerate cubes and of boundaries in `S`.
* `ClosureSpace.IsRelCycle`, `ClosureSpace.NullRel`: relative cycles and null chains of `(S, T)`.
* `ClosureSpace.proj S n`: the part of a chain made of cubes with image in `S`.

## Main statements

* `ClosureSpace.bd_bd_three'`: `∂∂ = 0` on `3`-chains.
-/

namespace ClosureSpace

open Finset

noncomputable section

variable {X : Type*}

/-! ## Chains -/

/-- Integer chains on maps from the corners of the `n`-cube. -/
abbrev Chain (X : Type*) (n : ℕ) := ((Fin n → Bool) → X) →₀ ℤ

/-- The face of `σ` obtained by fixing coordinate `i` to `b`. -/
def face {n : ℕ} (i : Fin (n + 1)) (b : Bool) (σ : (Fin (n + 1) → Bool) → X) :
    (Fin n → Bool) → X :=
  fun y => σ (Fin.insertNth i b y)

/-- The sign `(-1)^(i+1)` of the `i`-th pair of faces (coordinates counted from `0`). -/
def sgn {m : ℕ} (i : Fin m) : ℤ := (-1) ^ ((i : ℕ) + 1)

/-- The boundary of a single cube. -/
def bdCube {n : ℕ} (σ : (Fin (n + 1) → Bool) → X) : Chain X n :=
  ∑ i : Fin (n + 1),
    sgn i • (Finsupp.single (face i false σ) 1 - Finsupp.single (face i true σ) 1)

/-- The boundary homomorphism. -/
def bd (n : ℕ) : Chain X (n + 1) →+ Chain X n :=
  Finsupp.liftAddHom fun σ => zmultiplesHom (Chain X n) (bdCube σ)

theorem bd_single {n : ℕ} (σ : (Fin (n + 1) → Bool) → X) :
    bd n (Finsupp.single σ 1) = bdCube σ := by
  simp [bd]

/-- `σ` is degenerate when it does not depend on some coordinate. -/
def IsDegenerate {n : ℕ} (σ : (Fin n → Bool) → X) : Prop :=
  ∃ i : Fin n, ∀ x, σ (Function.update x i false) = σ (Function.update x i true)

/-- `σ` has its image in `S`. -/
def InSet (S : Set X) {n : ℕ} (σ : (Fin n → Bool) → X) : Prop := ∀ x, σ x ∈ S

theorem IsCube.face {C : ClosureSpace X} {n : ℕ} {σ : (Fin (n + 1) → Bool) → X}
    (hσ : C.IsCube σ) (i : Fin (n + 1)) (b : Bool) : C.IsCube (ClosureSpace.face i b σ) := by
  intro y j
  have key : Fin.insertNth i b (flipAt y j) = flipAt (Fin.insertNth i b y) (i.succAbove j) := by
    simp only [flipAt]
    rw [Fin.insertNth_update, Fin.insertNth_apply_succAbove]
  simp only [ClosureSpace.face, key]
  exact hσ _ _

theorem InSet.face {S : Set X} {n : ℕ} {σ : (Fin (n + 1) → Bool) → X} (h : InSet S σ)
    (i : Fin (n + 1)) (b : Bool) : InSet S (face i b σ) := fun _ => h _

/-- Chains supported on cubes with image in `S`. -/
def cubesIn (C : ClosureSpace X) (S : Set X) (n : ℕ) : AddSubgroup (Chain X n) :=
  AddSubgroup.closure {c | ∃ σ, C.IsCube σ ∧ InSet S σ ∧ c = Finsupp.single σ 1}

/-- Chains supported on degenerate cubes with image in `S`. -/
def degIn (C : ClosureSpace X) (S : Set X) (n : ℕ) : AddSubgroup (Chain X n) :=
  AddSubgroup.closure
    {c | ∃ σ, C.IsCube σ ∧ InSet S σ ∧ IsDegenerate σ ∧ c = Finsupp.single σ 1}

/-- Boundaries of chains in `S`. -/
def bndIn (C : ClosureSpace X) (S : Set X) (n : ℕ) : AddSubgroup (Chain X n) :=
  (cubesIn C S (n + 1)).map (bd n)

/-- A chain `z` represents zero in the normalized relative homology `H_n(S, T)`:
`z ∈ ∂C_{n+1}(S) + C_n(T) + D_n(S)`. -/
def NullRel (C : ClosureSpace X) (S T : Set X) (n : ℕ) (z : Chain X n) : Prop :=
  z ∈ bndIn C S n ⊔ cubesIn C T n ⊔ degIn C S n

/-- `z` is a relative cycle of `(S, T)` in degree `n + 1`. -/
def IsRelCycle (C : ClosureSpace X) (S T : Set X) (n : ℕ) (z : Chain X (n + 1)) : Prop :=
  z ∈ cubesIn C S (n + 1) ∧ bd n z ∈ cubesIn C T n ⊔ degIn C S n

theorem single_mem_cubesIn {C : ClosureSpace X} {S : Set X} {n : ℕ} {σ : (Fin n → Bool) → X}
    (hσ : C.IsCube σ) (hS : InSet S σ) : Finsupp.single σ 1 ∈ cubesIn C S n :=
  AddSubgroup.subset_closure ⟨σ, hσ, hS, rfl⟩

theorem bdCube_mem_cubesIn {C : ClosureSpace X} {S : Set X} {n : ℕ}
    {σ : (Fin (n + 1) → Bool) → X} (hσ : C.IsCube σ) (hS : InSet S σ) :
    bdCube σ ∈ cubesIn C S n := by
  apply AddSubgroup.sum_mem
  intro i _
  apply AddSubgroup.zsmul_mem
  exact AddSubgroup.sub_mem _ (single_mem_cubesIn (hσ.face i false) (hS.face i false))
    (single_mem_cubesIn (hσ.face i true) (hS.face i true))

theorem bd_mem_cubesIn {C : ClosureSpace X} {S : Set X} {n : ℕ} {z : Chain X (n + 1)}
    (hz : z ∈ cubesIn C S (n + 1)) : bd n z ∈ cubesIn C S n := by
  have : cubesIn C S (n + 1) ≤ (cubesIn C S n).comap (bd n) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro c ⟨σ, hσ, hS, rfl⟩
    simp only [SetLike.mem_coe, AddSubgroup.mem_comap, bd_single]
    exact bdCube_mem_cubesIn hσ hS
  exact this hz

theorem bndIn_le_cubesIn (C : ClosureSpace X) (S : Set X) (n : ℕ) :
    bndIn C S n ≤ cubesIn C S n := by
  rintro _ ⟨z, hz, rfl⟩
  exact bd_mem_cubesIn hz

/-! ## Restriction of chains to a subset -/

open Classical in
/-- Keep the cubes with image in `S`, discard the others. -/
noncomputable def proj (S : Set X) (n : ℕ) : Chain X n →+ Chain X n :=
  Finsupp.filterAddHom (InSet S)

theorem proj_single_pos {S : Set X} {n : ℕ} {σ : (Fin n → Bool) → X} (h : InSet S σ) :
    proj S n (Finsupp.single σ 1) = Finsupp.single σ 1 := by
  classical
  exact Finsupp.filter_single_of_pos _ h

theorem proj_single_neg {S : Set X} {n : ℕ} {σ : (Fin n → Bool) → X} (h : ¬ InSet S σ) :
    proj S n (Finsupp.single σ 1) = 0 := by
  classical
  exact Finsupp.filter_single_of_neg _ h

/-- Induction principle for the subgroups generated by single cubes. -/
theorem closure_single_induction {n : ℕ} {P : ((Fin n → Bool) → X) → Prop}
    {Q : Chain X n → Prop} (h0 : Q 0)
    (hadd : ∀ a b, Q a → Q b → Q (a + b)) (hneg : ∀ a, Q a → Q (-a))
    (hgen : ∀ σ, P σ → Q (Finsupp.single σ 1)) {z : Chain X n}
    (hz : z ∈ AddSubgroup.closure {c | ∃ σ, P σ ∧ c = Finsupp.single σ 1}) : Q z := by
  induction hz using AddSubgroup.closure_induction with
  | mem c hc =>
      obtain ⟨σ, hσ, rfl⟩ := hc
      exact hgen σ hσ
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | neg a _ ha => exact hneg a ha

theorem cubesIn_eq (C : ClosureSpace X) (S : Set X) (n : ℕ) :
    cubesIn C S n =
      AddSubgroup.closure {c | ∃ σ, (C.IsCube σ ∧ InSet S σ) ∧ c = Finsupp.single σ 1} := by
  unfold cubesIn
  congr 1
  ext c
  simp [and_assoc]

theorem degIn_eq (C : ClosureSpace X) (S : Set X) (n : ℕ) :
    degIn C S n = AddSubgroup.closure
      {c | ∃ σ, (C.IsCube σ ∧ InSet S σ ∧ IsDegenerate σ) ∧ c = Finsupp.single σ 1} := by
  unfold degIn
  congr 1
  ext c
  simp [and_assoc]

theorem proj_eq_self {C : ClosureSpace X} {S : Set X} {n : ℕ} {z : Chain X n}
    (hz : z ∈ cubesIn C S n) : proj S n z = z := by
  rw [cubesIn_eq] at hz
  refine closure_single_induction (Q := fun z => proj S n z = z) (by simp)
    (fun a b ha hb => by simp [ha, hb]) (fun a ha => by simp [ha]) ?_ hz
  rintro σ ⟨_, hS⟩
  exact proj_single_pos hS

theorem proj_mem_inter {C : ClosureSpace X} {A B : Set X} {n : ℕ} {z : Chain X n}
    (hz : z ∈ cubesIn C A n) : proj B n z ∈ cubesIn C (A ∩ B) n := by
  rw [cubesIn_eq] at hz
  refine closure_single_induction (Q := fun z => proj B n z ∈ cubesIn C (A ∩ B) n)
    (by simp) (fun a b ha hb => by simpa using add_mem ha hb)
    (fun a ha => by simpa using neg_mem ha) ?_ hz
  rintro σ ⟨hσ, hA⟩
  by_cases hB : InSet B σ
  · rw [proj_single_pos hB]
    exact single_mem_cubesIn hσ (fun x => ⟨hA x, hB x⟩)
  · rw [proj_single_neg hB]
    exact zero_mem _

theorem proj_mem_degIn {C : ClosureSpace X} {S B : Set X} {n : ℕ} {z : Chain X n}
    (hz : z ∈ degIn C S n) : proj B n z ∈ degIn C B n := by
  rw [degIn_eq] at hz
  refine closure_single_induction (Q := fun z => proj B n z ∈ degIn C B n)
    (by simp) (fun a b ha hb => by simpa using add_mem ha hb)
    (fun a ha => by simpa using neg_mem ha) ?_ hz
  rintro σ ⟨hσ, _, hdeg⟩
  by_cases hB : InSet B σ
  · rw [proj_single_pos hB]
    exact AddSubgroup.subset_closure ⟨σ, hσ, hB, hdeg, rfl⟩
  · rw [proj_single_neg hB]
    exact zero_mem _

theorem cubesIn_mono {C : ClosureSpace X} {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    cubesIn C S n ≤ cubesIn C T n := by
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨σ, hσ, hS, rfl⟩
  exact single_mem_cubesIn hσ (fun x => h (hS x))

theorem degIn_mono {C : ClosureSpace X} {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    degIn C S n ≤ degIn C T n := by
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨σ, hσ, hS, hdeg, rfl⟩
  exact AddSubgroup.subset_closure ⟨σ, hσ, fun x => h (hS x), hdeg, rfl⟩

/-! ## `∂∂ = 0` on 3-cubes -/

theorem face_face_01 (τ : (Fin 3 → Bool) → X) (b c : Bool) :
    face 0 c (face 0 b τ) = face 0 b (face 1 c τ) := by
  funext y
  simp only [face]
  congr 1
  revert b c y
  decide

theorem face_face_02 (τ : (Fin 3 → Bool) → X) (b c : Bool) :
    face 1 c (face 0 b τ) = face 0 b (face 2 c τ) := by
  funext y
  simp only [face]
  congr 1
  revert b c y
  decide

theorem face_face_12 (τ : (Fin 3 → Bool) → X) (b c : Bool) :
    face 1 c (face 1 b τ) = face 1 b (face 2 c τ) := by
  funext y
  simp only [face]
  congr 1
  revert b c y
  decide

/-- `∂∂ = 0` on a single 3-cube, for any target. -/
theorem bd_bd_three (τ : (Fin 3 → Bool) → X) :
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
theorem bd_bd_three' (w : Chain X 3) : bd 1 (bd 2 w) = 0 := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single τ k =>
      have h : Finsupp.single τ k = k • Finsupp.single τ 1 := by simp
      rw [h, map_zsmul, map_zsmul, bd_bd_three, smul_zero]

end

end ClosureSpace
