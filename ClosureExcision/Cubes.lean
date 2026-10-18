import ClosureExcision.Basic

/-!
# Combinatorial cubes and excision in low degrees

A singular `n`-cube for the undirected interval `J₁` with the inductive product is a map
`σ : (Fin n → Bool) → X` such that corners differing in one coordinate have images that lie in
each other's closures. Chains are finitely supported integer combinations of maps, the
boundary is `∂σ = ∑ᵢ (-1)^(i+1) (σ|xᵢ=0 - σ|xᵢ=1)` (coordinates counted from `0`), and a chain
is degenerate when it is a combination of cubes that do not depend on some coordinate.

The main result, `excision_iso_of_iterate_int`, says: if the `k`-fold interiors of `A` and `B`
cover `X`, every cube of dimension at most `2k` lies in `A` or in `B`, and the excision map
`H_d(B, A ∩ B) → H_d(X, A)` is bijective for `d ≤ 2k - 1`.
-/

namespace ClosureExcision

open Finset

noncomputable section

variable {X : Type*}

/-! ## Cubes -/

/-- Change coordinate `i` of a corner. -/
def flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

@[simp] theorem flipAt_apply_self {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipAt x i i = !x i := by
  simp [flipAt]

theorem flipAt_apply_ne {n : ℕ} (x : Fin n → Bool) {i j : Fin n} (h : j ≠ i) :
    flipAt x i j = x j := by
  simp [flipAt, Function.update_of_ne h]

@[simp] theorem flipAt_flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipAt (flipAt x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · rw [flipAt_apply_ne _ h, flipAt_apply_ne _ h]

/-- A `(J₁, ⊡)` singular cube: neighbouring corners go to points in each other's closures.
Since `flipAt` is an involution, the condition holds in both directions along every edge. -/
def ClosureSpace.IsCube (C : ClosureSpace X) {n : ℕ} (σ : (Fin n → Bool) → X) : Prop :=
  ∀ x i, σ (flipAt x i) ∈ C.cl {σ x}

/-- A `(J₊, ⊡)` singular cube: the condition is required only along edges oriented from `0` to `1`. -/
def ClosureSpace.IsPlusCube (C : ClosureSpace X) {n : ℕ} (σ : (Fin n → Bool) → X) : Prop :=
  ∀ x i, x i = false → σ (flipAt x i) ∈ C.cl {σ x}

/-- On a symmetric closure space the directed and undirected intervals give the same cubes. -/
theorem isCube_iff_isPlusCube {C : ClosureSpace X}
    (hsymm : ∀ x y, y ∈ C.cl {x} → x ∈ C.cl {y}) {n : ℕ} (σ : (Fin n → Bool) → X) :
    C.IsCube σ ↔ C.IsPlusCube σ := by
  constructor
  · intro h x i _
    exact h x i
  · intro h x i
    cases hx : x i
    · exact h x i hx
    · have h' := h (flipAt x i) i (by simp [hx])
      rw [flipAt_flipAt] at h'
      exact hsymm _ _ h'

/-! ## Small cubes -/

/-- Walking from corner `x` to corner `y` along a cube: if `σ x` lies in the `m`-fold interior of
`S` and `x, y` differ in at most `m` coordinates, then `σ y ∈ S`. -/
theorem mem_of_iterate_int {C : ClosureSpace X} {n : ℕ} {σ : (Fin n → Bool) → X}
    (hσ : C.IsCube σ) {S : Set X} :
    ∀ (m : ℕ) (x y : Fin n → Bool),
      (univ.filter fun i => x i ≠ y i).card ≤ m → σ x ∈ C.int^[m] S → σ y ∈ S
  | 0, x, y, h, hx => by
      have hxy : x = y := by
        funext i
        by_contra hne
        have hi : i ∈ univ.filter (fun i => x i ≠ y i) := by simp [hne]
        have := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      subst hxy
      simpa using hx
  | m + 1, x, y, h, hx => by
      by_cases hxy : x = y
      · subst hxy
        exact C.iterate_int_subset S (m + 1) hx
      · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
          by_contra h'
          push Not at h'
          exact hxy (funext h')
        have hcl : σ x ∈ C.cl {σ (flipAt x i)} := by
          have := hσ (flipAt x i) i
          rwa [flipAt_flipAt] at this
        rw [Function.iterate_succ_apply'] at hx
        have hm : σ (flipAt x i) ∈ C.int^[m] S := C.mem_of_mem_int_of_mem_cl hx hcl
        refine mem_of_iterate_int hσ m (flipAt x i) y ?_ hm
        have hset : (univ.filter fun j => flipAt x i j ≠ y j) =
            (univ.filter fun j => x j ≠ y j).erase i := by
          ext j
          simp only [mem_filter, mem_univ, true_and, mem_erase]
          by_cases hj : j = i
          · subst hj
            simp only [flipAt_apply_self, ne_eq, not_true_eq_false, false_and, iff_false,
              not_not]
            revert hi
            cases x j <;> cases y j <;> simp
          · rw [flipAt_apply_ne _ hj]
            simp [hj]
        rw [hset, Finset.card_erase_of_mem (by simp [hi])]
        omega

/-- **Small cubes.** If the `k`-fold interiors of `A` and `B` cover `X`, every cube of dimension
at most `2k` has its image in `A` or in `B`. -/
theorem cube_small {C : ClosureSpace X} {n k : ℕ} {σ : (Fin n → Bool) → X} (hσ : C.IsCube σ)
    (hn : n ≤ 2 * k) {A B : Set X} (hcov : ∀ x, x ∈ C.int^[k] A ∨ x ∈ C.int^[k] B) :
    (∀ x, σ x ∈ A) ∨ (∀ x, σ x ∈ B) := by
  by_contra h
  push Not at h
  obtain ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩ := h
  let y : Fin n → Bool := fun i => if (i : ℕ) < k then z' i else z i
  have h1 : (univ.filter fun i => y i ≠ z i).card ≤ k := by
    calc (univ.filter fun i => y i ≠ z i).card
        ≤ (Finset.range k).card := by
          refine Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ)) ?_ ?_
          · intro i hi
            simp only [mem_coe, mem_filter, mem_univ, true_and, y] at hi
            simp only [mem_coe, Finset.mem_range]
            by_contra hk
            simp [hk] at hi
          · intro i _ j _ hij
            exact Fin.ext hij
      _ = k := Finset.card_range k
  have h2 : (univ.filter fun i => y i ≠ z' i).card ≤ k := by
    calc (univ.filter fun i => y i ≠ z' i).card
        ≤ (Finset.range (n - k)).card := by
          refine Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ) - k) ?_ ?_
          · intro i hi
            simp only [mem_coe, mem_filter, mem_univ, true_and, y] at hi
            simp only [mem_coe, Finset.mem_range]
            by_cases hk : (i : ℕ) < k
            · simp [hk] at hi
            · have := i.isLt
              omega
          · intro i hi j hj hij
            simp only [mem_coe, mem_filter, mem_univ, true_and, y] at hi hj
            by_cases hik : (i : ℕ) < k
            · simp [hik] at hi
            by_cases hjk : (j : ℕ) < k
            · simp [hjk] at hj
            apply Fin.ext
            simp only at hij
            omega
      _ = n - k := Finset.card_range _
      _ ≤ k := by omega
  rcases hcov (σ y) with hA | hB
  · exact hz (mem_of_iterate_int hσ k y z h1 hA)
  · exact hz' (mem_of_iterate_int hσ k y z' h2 hB)

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

theorem ClosureSpace.IsCube.face {C : ClosureSpace X} {n : ℕ} {σ : (Fin (n + 1) → Bool) → X}
    (hσ : C.IsCube σ) (i : Fin (n + 1)) (b : Bool) : C.IsCube (ClosureExcision.face i b σ) := by
  intro y j
  have key : Fin.insertNth i b (flipAt y j) = flipAt (Fin.insertNth i b y) (i.succAbove j) := by
    simp only [flipAt]
    rw [Fin.insertNth_update, Fin.insertNth_apply_succAbove]
  simp only [ClosureExcision.face, key]
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

/-! ## Excision when cubes are small -/

/-- If every cube of dimension `n + 1` lies in `A` or in `B`, boundaries in `X` split. -/
theorem bndIn_univ_le {C : ClosureSpace X} {A B : Set X} {n : ℕ}
    (hsmall : ∀ σ : (Fin (n + 1) → Bool) → X, C.IsCube σ → InSet A σ ∨ InSet B σ) :
    bndIn C Set.univ n ≤ bndIn C A n ⊔ bndIn C B n := by
  unfold bndIn
  rw [AddSubgroup.map_le_iff_le_comap]
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨σ, hσ, _, rfl⟩
  simp only [SetLike.mem_coe, AddSubgroup.mem_comap]
  rcases hsmall σ hσ with hA | hB
  · exact AddSubgroup.mem_sup_left ⟨_, single_mem_cubesIn hσ hA, rfl⟩
  · exact AddSubgroup.mem_sup_right ⟨_, single_mem_cubesIn hσ hB, rfl⟩

/-- **Injectivity of excision in degree `n`** when all `(n+1)`-cubes are small: a chain in `B`
that is null in `(X, A)` is null in `(B, A ∩ B)`. -/
theorem excision_injective {C : ClosureSpace X} {A B : Set X} {n : ℕ}
    (hsmall : ∀ σ : (Fin (n + 1) → Bool) → X, C.IsCube σ → InSet A σ ∨ InSet B σ)
    {z : Chain X n} (hz : z ∈ cubesIn C B n) (hnull : NullRel C Set.univ A n z) :
    NullRel C B (A ∩ B) n z := by
  unfold NullRel at hnull ⊢
  obtain ⟨u, hu, d, hd, rfl⟩ := AddSubgroup.mem_sup.mp hnull
  obtain ⟨b, hb, a, ha, rfl⟩ := AddSubgroup.mem_sup.mp hu
  obtain ⟨bA, hbA, bB, hbB, rfl⟩ := AddSubgroup.mem_sup.mp (bndIn_univ_le hsmall hb)
  have hfix : proj B n (bA + bB + a + d) = bA + bB + a + d := proj_eq_self hz
  rw [← hfix]
  simp only [map_add]
  have h1 : proj B n bA ∈ cubesIn C (A ∩ B) n :=
    proj_mem_inter (bndIn_le_cubesIn C A n hbA)
  have h2 : proj B n bB = bB := proj_eq_self (bndIn_le_cubesIn C B n hbB)
  have h3 : proj B n a ∈ cubesIn C (A ∩ B) n := proj_mem_inter ha
  have h4 : proj B n d ∈ degIn C B n := proj_mem_degIn hd
  rw [h2]
  have : proj B n bA + bB + proj B n a + proj B n d =
      bB + (proj B n bA + proj B n a) + proj B n d := by abel
  rw [this]
  exact AddSubgroup.add_mem_sup
    (AddSubgroup.add_mem_sup hbB (add_mem h1 h3)) h4

/-- Splitting a chain of small cubes: the part outside `A` lies in `B`. -/
theorem split_mem {C : ClosureSpace X} {A B : Set X} {n : ℕ}
    (hsmall : ∀ σ : (Fin n → Bool) → X, C.IsCube σ → InSet A σ ∨ InSet B σ)
    {z : Chain X n} (hz : z ∈ cubesIn C Set.univ n) : z - proj A n z ∈ cubesIn C B n := by
  rw [cubesIn_eq] at hz
  refine closure_single_induction (Q := fun z => z - proj A n z ∈ cubesIn C B n)
    (by simp) (fun a b ha hb => by simpa [add_sub_add_comm] using add_mem ha hb)
    (fun a ha => by simpa [neg_sub, sub_neg_eq_add, neg_add_eq_sub] using neg_mem ha) ?_ hz
  rintro σ ⟨hσ, _⟩
  by_cases hA : InSet A σ
  · rw [proj_single_pos hA, sub_self]
    exact zero_mem _
  · rw [proj_single_neg hA, sub_zero]
    rcases hsmall σ hσ with h | h
    · exact absurd h hA
    · exact single_mem_cubesIn hσ h

theorem proj_mem_cubesIn {C : ClosureSpace X} {S A : Set X} {n : ℕ} {z : Chain X n}
    (hz : z ∈ cubesIn C S n) : proj A n z ∈ cubesIn C A n :=
  cubesIn_mono Set.inter_subset_right n (proj_mem_inter (B := A) hz)

/-- **Surjectivity of excision in degree `n + 1`** when all `(n+1)`-cubes are small. -/
theorem excision_surjective {C : ClosureSpace X} {A B : Set X} {n : ℕ}
    (hsmall : ∀ σ : (Fin (n + 1) → Bool) → X, C.IsCube σ → InSet A σ ∨ InSet B σ)
    {z : Chain X (n + 1)} (hz : IsRelCycle C Set.univ A n z) :
    ∃ z', IsRelCycle C B (A ∩ B) n z' ∧ NullRel C Set.univ A (n + 1) (z - z') := by
  obtain ⟨hzX, hbd⟩ := hz
  refine ⟨z - proj A (n + 1) z, ⟨split_mem hsmall hzX, ?_⟩, ?_⟩
  · have hB : bd n (z - proj A (n + 1) z) ∈ cubesIn C B n :=
      bd_mem_cubesIn (split_mem hsmall hzX)
    have hA : bd n (z - proj A (n + 1) z) ∈ cubesIn C A n ⊔ degIn C Set.univ n := by
      rw [map_sub]
      exact sub_mem hbd (AddSubgroup.mem_sup_left
        (bd_mem_cubesIn (proj_mem_cubesIn hzX)))
    obtain ⟨a, ha, d, hd, hsum⟩ := AddSubgroup.mem_sup.mp hA
    rw [← proj_eq_self hB, ← hsum, map_add]
    exact AddSubgroup.add_mem_sup (proj_mem_inter ha) (proj_mem_degIn hd)
  · have : z - (z - proj A (n + 1) z) = proj A (n + 1) z := by abel
    rw [this]
    exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_right (proj_mem_cubesIn hzX))

/-- Surjectivity of excision in degree `0`: every `0`-chain is homologous to one in `B`. -/
theorem excision_surjective_zero {C : ClosureSpace X} {A B : Set X}
    (hsmall : ∀ σ : (Fin 0 → Bool) → X, C.IsCube σ → InSet A σ ∨ InSet B σ)
    {z : Chain X 0} (hz : z ∈ cubesIn C Set.univ 0) :
    ∃ z' ∈ cubesIn C B 0, NullRel C Set.univ A 0 (z - z') := by
  refine ⟨z - proj A 0 z, split_mem hsmall hz, ?_⟩
  have : z - (z - proj A 0 z) = proj A 0 z := by abel
  rw [this]
  exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_right (proj_mem_cubesIn hz))

/-- **Theorem 1.** If the `k`-fold interiors of `A` and `B` cover `X`, then every cube of
dimension at most `2k` lies in `A` or in `B`, and for every `d ≤ 2k - 1` the excision map
`H_d(B, A ∩ B) → H_d(X, A)` is injective and surjective. -/
theorem excision_of_iterate_int_cover {C : ClosureSpace X} {A B : Set X} {k : ℕ}
    (hcov : ∀ x, x ∈ C.int^[k] A ∨ x ∈ C.int^[k] B) (d : ℕ) (hd : d + 1 ≤ 2 * k) :
    (∀ z ∈ cubesIn C B d, NullRel C Set.univ A d z → NullRel C B (A ∩ B) d z) ∧
    (∀ z ∈ cubesIn C Set.univ d, ∃ z' ∈ cubesIn C B d, NullRel C Set.univ A d (z - z')) ∧
    (∀ m (z : Chain X (m + 1)), m + 1 = d → IsRelCycle C Set.univ A m z →
      ∃ z', IsRelCycle C B (A ∩ B) m z' ∧ NullRel C Set.univ A (m + 1) (z - z')) := by
  have hsmall : ∀ m ≤ 2 * k, ∀ σ : (Fin m → Bool) → X, C.IsCube σ →
      InSet A σ ∨ InSet B σ := fun m hm σ hσ => cube_small hσ hm hcov
  refine ⟨fun z hz hnull => excision_injective (hsmall (d + 1) hd) hz hnull,
    fun z hz => ⟨z - proj A d z, split_mem (hsmall d (by omega)) hz, ?_⟩,
    fun m z hm hz => excision_surjective (hsmall (m + 1) (by omega)) hz⟩
  have : z - (z - proj A d z) = proj A d z := by abel
  rw [this]
  exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_right (proj_mem_cubesIn hz))

end

end ClosureExcision
