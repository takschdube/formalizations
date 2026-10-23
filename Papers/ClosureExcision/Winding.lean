import ClosureExcision.SixCycle

/-!
# A winding number for the six-cycle in the `(I, ×)` theory

A map `γ : 𝕀 → C₆` is *fine* at `n` if each piece `[i/n, (i+1)/n]` of the partition of `𝕀` into
`n` equal pieces maps into one closed neighbourhood `N[v] = {v - 1, v, v + 1}`. On `N[v]` the signed
step between two values is the difference of their lifts to `{-1, 0, 1}` around `v`, so refining a
fine partition does not change the sum of the steps between consecutive partition points. The
winding number `wnum γ` is this sum for any fine `n`, and `0` if there is none.

For a jointly continuous square, a Lebesgue number of the cover of `𝕀 × 𝕀` by the preimages of
the `N[v]` gives a grid whose cells map into closed neighbourhoods. The steps around each cell
cancel, so the winding numbers of the four faces cancel. The hexagon loop has winding number `6`.

## Main statements

* `ClosureExcision.c6_prod_H1_ne_zero`: the hexagon loop is a `1`-cycle of `C₆` that does not
  bound in `(I, ×)` ([DT], Theorem 3 (c)).

## References

* [DT] T. Dube and A. Tregub, *Excision fails for inductive-product cubical homology of closure
  spaces*.
-/

namespace ClosureExcision

open Topology Filter Metric Finset ClosureSpace

local notation "𝕀" => unitInterval

noncomputable section

/-! ## Steps in the six-cycle -/

/-- The signed step from `a` to `b`: `±1` along an edge, `±2` across two edges, `0` otherwise. -/
def c6Step (a b : ZMod 6) : ℤ :=
  if b = a + 1 then 1 else if a = b + 1 then -1 else if b = a + 2 then 2
  else if a = b + 2 then -2 else 0

/-- The lift of `x` to `{-1, 0, 1}` around `v`. -/
def liftAt (v x : ZMod 6) : ℤ := if x = v + 1 then 1 else if v = x + 1 then -1 else 0

/-- On a closed neighbourhood `N[v]` the step is the difference of the lifts. -/
theorem c6Step_eq_liftAt : ∀ v a b : ZMod 6, c6Rel a v → c6Rel b v →
    c6Step a b = liftAt v b - liftAt v a := by decide

theorem c6Step_self : ∀ a : ZMod 6, c6Step a a = 0 := by decide

theorem c6Step_add_one : ∀ a : ZMod 6, c6Step a (a + 1) = 1 := by decide

/-! ## Partitions of the interval -/

/-- The point `i / n` of `𝕀`. -/
def ppt (n i : ℕ) : 𝕀 := Set.projIcc 0 1 zero_le_one ((i : ℝ) / n)

theorem ppt_val {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) : (ppt n i : ℝ) = i / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (i : ℝ) / n ≤ 1 := by
    rw [div_le_iff₀ hn', one_mul]
    exact_mod_cast hi
  rw [ppt, Set.projIcc_of_mem zero_le_one ⟨by positivity, h1⟩]

theorem ppt_zero (n : ℕ) : ppt n 0 = 0 := by
  rw [ppt, Nat.cast_zero, zero_div, Set.projIcc_left]
  rfl

theorem ppt_self {n : ℕ} (hn : 0 < n) : ppt n n = 1 := by
  apply Subtype.ext
  rw [ppt_val hn le_rfl, div_self (by exact_mod_cast hn.ne')]
  rfl

/-- The points `i / n` and `(i + 1) / n` lie in the piece `[i/n, (i+1)/n]`. -/
theorem ppt_mem_piece {n i a : ℕ} (hn : 0 < n) (hi : i < n) (ha : a = i ∨ a = i + 1) :
    (i : ℝ) / n ≤ ppt n a ∧ (ppt n a : ℝ) ≤ ((i : ℝ) + 1) / n := by
  rcases ha with rfl | rfl
  · rw [ppt_val hn hi.le]
    exact ⟨le_rfl, by gcongr; linarith⟩
  · rw [ppt_val hn hi]
    push_cast
    exact ⟨by gcongr; linarith, le_rfl⟩

theorem cast_pred_add_one {n : ℕ} (hn : 0 < n) : ((n - 1 : ℕ) : ℝ) + 1 = n := by
  rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]

/-! ## The winding number of a path -/

/-- The sum of the steps of `γ` between consecutive points of the partition into `n` pieces. -/
def stepSum (n : ℕ) (γ : 𝕀 → ZMod 6) : ℤ :=
  ∑ i ∈ range n, c6Step (γ (ppt n i)) (γ (ppt n (i + 1)))

/-- `γ` is fine at `n`: each piece `[i/n, (i+1)/n]` maps into a closed neighbourhood. -/
def IsFine (γ : 𝕀 → ZMod 6) (n : ℕ) : Prop :=
  ∀ i < n, ∃ v, ∀ t : 𝕀, (i : ℝ) / n ≤ t → (t : ℝ) ≤ ((i : ℝ) + 1) / n → c6Rel (γ t) v

theorem sum_range_mul_eq (f : ℕ → ℤ) (n m : ℕ) :
    ∑ k ∈ range (n * m), f k = ∑ i ∈ range n, ∑ j ∈ range m, f (i * m + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [add_mul, one_mul, sum_range_add, ih, sum_range_succ]

/-- Steps inside one closed neighbourhood telescope. -/
theorem sum_c6Step_eq {v : ZMod 6} (f : ℕ → ZMod 6) (m : ℕ) (hf : ∀ j ≤ m, c6Rel (f j) v) :
    ∑ j ∈ range m, c6Step (f j) (f (j + 1)) = c6Step (f 0) (f m) := by
  rw [c6Step_eq_liftAt v _ _ (hf 0 (Nat.zero_le _)) (hf m le_rfl),
    ← sum_range_sub (fun j => liftAt v (f j))]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  exact c6Step_eq_liftAt v _ _ (hf j hj.le) (hf (j + 1) (by omega))

/-- Refining a fine partition does not change the step sum. -/
theorem stepSum_mul {γ : 𝕀 → ZMod 6} {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : IsFine γ n) :
    stepSum (n * m) γ = stepSum n γ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  unfold stepSum
  rw [sum_range_mul_eq (fun k => c6Step (γ (ppt (n * m) k)) (γ (ppt (n * m) (k + 1))))]
  refine sum_congr rfl fun i hi => ?_
  have hi := mem_range.mp hi
  obtain ⟨v, hv⟩ := h i hi
  have hle : ∀ j ≤ m, i * m + j ≤ n * m := fun j hj => by
    have := Nat.mul_le_mul_right m (show i + 1 ≤ n from hi)
    nlinarith
  have hpt : ∀ j ≤ m, c6Rel (γ (ppt (n * m) (i * m + j))) v := by
    intro j hj
    have hval := ppt_val hnm (hle j hj)
    push_cast at hval
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj
    have hi0 : (0 : ℝ) ≤ i := by positivity
    apply hv
    · rw [hval, div_le_div_iff₀ hn' (by positivity)]
      nlinarith
    · rw [hval, div_le_div_iff₀ (by positivity) hn']
      nlinarith
  have key := sum_c6Step_eq (fun j => γ (ppt (n * m) (i * m + j))) m hpt
  simp only [← add_assoc] at key
  rw [key]
  have e0 : ppt (n * m) (i * m + 0) = ppt n i := by
    apply Subtype.ext
    rw [add_zero, ppt_val hnm (by nlinarith), ppt_val hn hi.le]
    push_cast
    rw [mul_div_mul_right _ _ hm'.ne']
  have e1 : ppt (n * m) (i * m + m) = ppt n (i + 1) := by
    apply Subtype.ext
    rw [ppt_val hnm (hle m le_rfl), ppt_val hn hi]
    push_cast
    rw [show (i : ℝ) * m + m = (i + 1) * m by ring, mul_div_mul_right _ _ hm'.ne']
  rw [e0, e1]

theorem stepSum_eq_of_isFine {γ : 𝕀 → ZMod 6} {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n')
    (h : IsFine γ n) (h' : IsFine γ n') : stepSum n γ = stepSum n' γ := by
  rw [← stepSum_mul hn hn' h, ← stepSum_mul hn' hn h', mul_comm]

open Classical in
/-- The winding number: the step sum over any fine partition, and `0` if there is none. -/
def wnum (γ : 𝕀 → ZMod 6) : ℤ :=
  if h : ∃ n, 0 < n ∧ IsFine γ n then stepSum h.choose γ else 0

theorem wnum_eq {γ : 𝕀 → ZMod 6} {n : ℕ} (hn : 0 < n) (h : IsFine γ n) :
    wnum γ = stepSum n γ := by
  have hex : ∃ n, 0 < n ∧ IsFine γ n := ⟨n, hn, h⟩
  rw [wnum, dif_pos hex]
  exact stepSum_eq_of_isFine hex.choose_spec.1 hn hex.choose_spec.2 h

theorem wnum_const (x : ZMod 6) : wnum (fun _ => x) = 0 := by
  unfold wnum
  split_ifs
  · simp [stepSum, c6Step_self]
  · rfl

/-- The winding number on `1`-chains. -/
def pathWind : PChain (ZMod 6) →+ ℤ :=
  Finsupp.liftAddHom fun γ => zmultiplesHom ℤ (wnum γ)

theorem pathWind_single (γ : 𝕀 → ZMod 6) : pathWind (Finsupp.single γ 1) = wnum γ := by
  simp [pathWind]

/-! ## Jointly continuous squares -/

/-- Each cell of the `n × n` grid maps into a closed neighbourhood. -/
def CellFine (σ : 𝕀 × 𝕀 → ZMod 6) (n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∃ v, ∀ q : 𝕀 × 𝕀, (i : ℝ) / n ≤ q.1 → (q.1 : ℝ) ≤ ((i : ℝ) + 1) / n →
    (j : ℝ) / n ≤ q.2 → (q.2 : ℝ) ≤ ((j : ℝ) + 1) / n → c6Rel (σ q) v

/-- A Lebesgue number gives a fine grid for every jointly continuous square. -/
theorem IsProdSq.cellFine {σ : 𝕀 × 𝕀 → ZMod 6} (hσ : IsProdSq c6 σ) :
    ∃ n, 0 < n ∧ CellFine σ n := by
  have hcover : (Set.univ : Set (𝕀 × 𝕀)) ⊆ ⋃ v, interior {q | c6Rel (σ q) v} := fun p _ =>
    Set.mem_iUnion.mpr ⟨σ p, mem_interior_iff_mem_nhds.mpr
      (hσ p {y | c6Rel y (σ p)} (c6_isNbhd.mpr fun _ hy => hy))⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ (fun _ => isOpen_interior) hcover
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N + 1, N.succ_pos, fun i hi j hj => ?_⟩
  obtain ⟨v, hv⟩ := hball (ppt (N + 1) i, ppt (N + 1) j) (Set.mem_univ _)
  refine ⟨v, fun q h1 h2 h3 h4 => ?_⟩
  have e : ∀ k : ℕ, ∀ x : ℝ, (k : ℝ) / ((N + 1 : ℕ) : ℝ) ≤ x →
      x ≤ ((k : ℝ) + 1) / ((N + 1 : ℕ) : ℝ) → |x - k / ((N + 1 : ℕ) : ℝ)| < δ := by
    intro k x hk1 hk2
    have hsplit : ((k : ℝ) + 1) / ((N + 1 : ℕ) : ℝ) =
        k / ((N + 1 : ℕ) : ℝ) + 1 / ((N : ℝ) + 1) := by
      push_cast
      ring
    rw [abs_lt]
    constructor <;> linarith
  have hq : q ∈ ball (ppt (N + 1) i, ppt (N + 1) j) δ := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq,
      Real.dist_eq]
    dsimp only
    rw [ppt_val N.succ_pos hi.le, ppt_val N.succ_pos hj.le]
    exact ⟨e i _ h1 h2, e j _ h3 h4⟩
  have hmem : q ∈ {q | c6Rel (σ q) v} := interior_subset (hv hq)
  exact hmem

theorem CellFine.isFine_sqA1 {σ : 𝕀 × 𝕀 → ZMod 6} {n : ℕ} (hn : 0 < n) (h : CellFine σ n) :
    IsFine (sqA1 σ) n := fun i hi => by
  obtain ⟨v, hv⟩ := h 0 hn i hi
  refine ⟨v, fun t h1 h2 => hv (0, t) ?_ ?_ h1 h2⟩
  · show ((0 : ℕ) : ℝ) / n ≤ ((0 : 𝕀) : ℝ)
    simp
  · show ((0 : 𝕀) : ℝ) ≤ (((0 : ℕ) : ℝ) + 1) / n
    simp only [Set.Icc.coe_zero, Nat.cast_zero, zero_add]
    positivity

theorem CellFine.isFine_sqB1 {σ : 𝕀 × 𝕀 → ZMod 6} {n : ℕ} (hn : 0 < n) (h : CellFine σ n) :
    IsFine (sqB1 σ) n := fun i hi => by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨v, hv⟩ := h (n - 1) (by omega) i hi
  refine ⟨v, fun t h1 h2 => hv (1, t) ?_ ?_ h1 h2⟩
  · show ((n - 1 : ℕ) : ℝ) / n ≤ ((1 : 𝕀) : ℝ)
    rw [Set.Icc.coe_one, div_le_one hn']
    linarith [cast_pred_add_one hn]
  · show ((1 : 𝕀) : ℝ) ≤ (((n - 1 : ℕ) : ℝ) + 1) / n
    rw [Set.Icc.coe_one, cast_pred_add_one hn, div_self hn'.ne']

theorem CellFine.isFine_sqA2 {σ : 𝕀 × 𝕀 → ZMod 6} {n : ℕ} (hn : 0 < n) (h : CellFine σ n) :
    IsFine (sqA2 σ) n := fun i hi => by
  obtain ⟨v, hv⟩ := h i hi 0 hn
  refine ⟨v, fun s h1 h2 => hv (s, 0) h1 h2 ?_ ?_⟩
  · show ((0 : ℕ) : ℝ) / n ≤ ((0 : 𝕀) : ℝ)
    simp
  · show ((0 : 𝕀) : ℝ) ≤ (((0 : ℕ) : ℝ) + 1) / n
    simp only [Set.Icc.coe_zero, Nat.cast_zero, zero_add]
    positivity

theorem CellFine.isFine_sqB2 {σ : 𝕀 × 𝕀 → ZMod 6} {n : ℕ} (hn : 0 < n) (h : CellFine σ n) :
    IsFine (sqB2 σ) n := fun i hi => by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨v, hv⟩ := h i hi (n - 1) (by omega)
  refine ⟨v, fun s h1 h2 => hv (s, 1) h1 h2 ?_ ?_⟩
  · show ((n - 1 : ℕ) : ℝ) / n ≤ ((1 : 𝕀) : ℝ)
    rw [Set.Icc.coe_one, div_le_one hn']
    linarith [cast_pred_add_one hn]
  · show ((1 : 𝕀) : ℝ) ≤ (((n - 1 : ℕ) : ℝ) + 1) / n
    rw [Set.Icc.coe_one, cast_pred_add_one hn, div_self hn'.ne']

/-- Summing the cell identities over the grid: the four edge sums cancel. -/
theorem grid_sum (H V : ℕ → ℕ → ℤ) (n : ℕ)
    (hcell : ∀ i < n, ∀ j < n, H i j + V (i + 1) j = V i j + H i (j + 1)) :
    ∑ i ∈ range n, H i 0 - ∑ i ∈ range n, H i n =
      ∑ j ∈ range n, V 0 j - ∑ j ∈ range n, V n j := by
  have key : ∑ i ∈ range n, ∑ j ∈ range n, (H i j - H i (j + 1)) =
      ∑ i ∈ range n, ∑ j ∈ range n, (V i j - V (i + 1) j) :=
    sum_congr rfl fun i hi => sum_congr rfl fun j hj => by
      have := hcell i (mem_range.mp hi) j (mem_range.mp hj)
      linarith
  rw [sum_comm (f := fun i j => V i j - V (i + 1) j)] at key
  simp only [sum_range_sub'] at key
  simpa only [sum_sub_distrib] using key

/-- **The winding number vanishes on boundaries of jointly continuous squares.** -/
theorem pathWind_sqBd {σ : 𝕀 × 𝕀 → ZMod 6} (hσ : IsProdSq c6 σ) : pathWind (sqBd σ) = 0 := by
  obtain ⟨n, hn, h⟩ := IsProdSq.cellFine hσ
  set g : ℕ → ℕ → ZMod 6 := fun i j => σ (ppt n i, ppt n j) with hg
  set H : ℕ → ℕ → ℤ := fun i j => c6Step (g i j) (g (i + 1) j) with hH
  set V : ℕ → ℕ → ℤ := fun i j => c6Step (g i j) (g i (j + 1)) with hV
  have hcell : ∀ i < n, ∀ j < n, H i j + V (i + 1) j = V i j + H i (j + 1) := by
    intro i hi j hj
    obtain ⟨v, hv⟩ := h i hi j hj
    have hc : ∀ a b, (a = i ∨ a = i + 1) → (b = j ∨ b = j + 1) → c6Rel (g a b) v :=
      fun a b ha hb => hv _ (ppt_mem_piece hn hi ha).1 (ppt_mem_piece hn hi ha).2
        (ppt_mem_piece hn hj hb).1 (ppt_mem_piece hn hj hb).2
    simp only [hH, hV]
    rw [c6Step_eq_liftAt v _ _ (hc i j (.inl rfl) (.inl rfl)) (hc (i + 1) j (.inr rfl) (.inl rfl)),
      c6Step_eq_liftAt v _ _ (hc (i + 1) j (.inr rfl) (.inl rfl))
        (hc (i + 1) (j + 1) (.inr rfl) (.inr rfl)),
      c6Step_eq_liftAt v _ _ (hc i j (.inl rfl) (.inl rfl)) (hc i (j + 1) (.inl rfl) (.inr rfl)),
      c6Step_eq_liftAt v _ _ (hc i (j + 1) (.inl rfl) (.inr rfl))
        (hc (i + 1) (j + 1) (.inr rfl) (.inr rfl))]
    ring
  have hA1 : wnum (sqA1 σ) = ∑ j ∈ range n, V 0 j := by
    rw [wnum_eq hn (h.isFine_sqA1 hn), stepSum]
    simp only [hV, hg, sqA1, ppt_zero]
  have hB1 : wnum (sqB1 σ) = ∑ j ∈ range n, V n j := by
    rw [wnum_eq hn (h.isFine_sqB1 hn), stepSum]
    simp only [hV, hg, sqB1, ppt_self hn]
  have hA2 : wnum (sqA2 σ) = ∑ i ∈ range n, H i 0 := by
    rw [wnum_eq hn (h.isFine_sqA2 hn), stepSum]
    simp only [hH, hg, sqA2, ppt_zero]
  have hB2 : wnum (sqB2 σ) = ∑ i ∈ range n, H i n := by
    rw [wnum_eq hn (h.isFine_sqB2 hn), stepSum]
    simp only [hH, hg, sqB2, ppt_self hn]
  have hgrid := grid_sum H V n hcell
  simp only [sqBd, map_add, map_sub, map_neg, pathWind_single]
  rw [hA1, hB1, hA2, hB2]
  linarith

/-! ## The hexagon loop -/

theorem hexLoop_ppt {k : ℕ} (hk : k ≤ 6) : hexLoop (ppt 6 k) = (k : ZMod 6) := by
  have e : 6 * (ppt 6 k : ℝ) = k := by
    rw [ppt_val (by norm_num) hk]
    push_cast
    ring
  simp only [hexLoop, e, Int.floor_natCast, Int.cast_natCast]

theorem isFine_hexLoop : IsFine hexLoop 6 := by
  intro i hi
  refine ⟨(i : ZMod 6), fun t h1 h2 => ?_⟩
  push_cast at h1 h2
  have h1' : (i : ℝ) ≤ 6 * t := by
    rw [div_le_iff₀ (by norm_num)] at h1
    linarith
  have h2' : 6 * (t : ℝ) ≤ i + 1 := by
    rw [le_div_iff₀ (by norm_num)] at h2
    linarith
  have hf1 : (i : ℤ) ≤ ⌊6 * (t : ℝ)⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have hf2 : ⌊6 * (t : ℝ)⌋ ≤ (i : ℤ) + 1 := Int.floor_le_iff.mpr (by push_cast; linarith)
  have hcases : ⌊6 * (t : ℝ)⌋ = i ∨ ⌊6 * (t : ℝ)⌋ = (i : ℤ) + 1 := by omega
  simp only [hexLoop, c6Rel]
  rcases hcases with h | h
  · left
    rw [h]
    push_cast
    rfl
  · right; right
    rw [h]
    push_cast
    rfl

theorem stepSum_hexLoop : stepSum 6 hexLoop = 6 := by
  have h : ∀ i ∈ range 6, c6Step (hexLoop (ppt 6 i)) (hexLoop (ppt 6 (i + 1))) = 1 := by
    intro i hi
    have hi := mem_range.mp hi
    rw [hexLoop_ppt hi.le, hexLoop_ppt (k := i + 1) (by omega), Nat.cast_succ, c6Step_add_one]
  rw [stepSum, sum_congr rfl h]
  simp

/-- The hexagon loop winds `6` steps around `C₆`. -/
theorem wnum_hexLoop : wnum hexLoop = 6 := by
  rw [wnum_eq (by norm_num) isFine_hexLoop, stepSum_hexLoop]

theorem prodBnd_le_ker_pathWind : prodBnd c6 Set.univ ≤ pathWind.ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨σ, hσ, _, rfl⟩
  exact pathWind_sqBd hσ

theorem constIn_le_ker_pathWind : constIn (Set.univ : Set (ZMod 6)) ≤ pathWind.ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro c ⟨x, _, rfl⟩
  show pathWind _ = 0
  rw [pathWind_single, wnum_const]

/-- **`H₁` of `C₆` does not vanish in `(I, ×)`** ([DT], Theorem 3 (c)). The hexagon loop is a `1`-cycle of winding
number `6`, and the winding number vanishes on boundaries of jointly continuous squares and on
constant paths. -/
theorem c6_prod_H1_ne_zero :
    ∃ c ∈ pathsIn c6 Set.univ, bdPath c = 0 ∧ c ∉ prodBnd c6 Set.univ ⊔ constIn Set.univ := by
  refine ⟨Finsupp.single hexLoop 1,
    AddSubgroup.subset_closure ⟨hexLoop, isPath_hexLoop, fun _ => trivial, rfl⟩, ?_, ?_⟩
  · rw [bdPath_single, hexLoop_one, hexLoop_zero, sub_self]
  · intro hc
    have hker := (sup_le prodBnd_le_ker_pathWind constIn_le_ker_pathWind) hc
    rw [AddMonoidHom.mem_ker, pathWind_single, wnum_hexLoop] at hker
    norm_num at hker

end

end ClosureExcision
