-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TFloorGaps
import Mathlib.Tactic.LinearCombination

/-!
  The row lengths of the triangle by records (OEIS draft A900014, C90 (c)).

  A split of n is a list of Orders m ≥ 1 with sum n and Σ p2(m) = p2(n) (`RowSplit`); the row
  length R(n) is the largest length of a split. For d ≥ 1 let f_d(m) = d p2(m) - m (p2(d) - 1)
  (`fd`). Then f_d(m) ≥ 1 for every m ≥ 1 (`one_le_fd`:
  2^(d p2(m)) > 3^(dm) ≥ 2^(m (p2(d) - 1)); also for m = 0),
  and f_d adds up over a split, so every split of n has at most f_d(n) parts (`length_le_fd`).
  The bound is reached (`exists_split_eq_fd`): for every n ≥ 1 there are d ≥ 1 and a split of n
  into parts m with f_d(m) = 1. So R(n) = min_{d ≥ 1} f_d(n).

  The split is built along the record walk of `TFloorGaps`: with θ(a), θ(b) the lowest and
  highest of θ(1), ..., θ(N), a p2(b) + b = b p2(a) + 1 (the invariant, kept at each new record
  a + b); b has the least slope p2(k)/k up to N (`slope_le_of_max`); at a new upper record
  b' = a + b, each n with slope between those of b' and b is x b + y b' with x, y ≥ 0, and
  f_a(b) = f_a(b') = 1.
-/

namespace AcceleratedCollatz

/-- f_d(m) = d p2(m) - m (p2(d) - 1). -/
def fd (d m : ℕ) : ℤ := d * p2_of m - m * ((p2_of d : ℤ) - 1)

/-- A split of n: Orders m ≥ 1 with sum n and Σ p2(m) = p2(n). -/
def RowSplit (n : ℕ) (os : List ℕ) : Prop :=
  (∀ m ∈ os, 1 ≤ m) ∧ os.sum = n ∧ (os.map p2_of).sum = p2_of n

theorem one_le_fd {d : ℕ} (hd : 1 ≤ d) (m : ℕ) : 1 ≤ fd d m := by
  have h1 : 3 ^ m < 2 ^ p2_of m := p2_of_spec m
  have h2 : 2 ^ (p2_of d - 1) ≤ 3 ^ d := p2_of_spec_lower d
  have hlt : 2 ^ (m * (p2_of d - 1)) < 2 ^ (d * p2_of m) := by
    calc 2 ^ (m * (p2_of d - 1)) = (2 ^ (p2_of d - 1)) ^ m := by rw [← pow_mul, mul_comm]
      _ ≤ (3 ^ d) ^ m := Nat.pow_le_pow_left h2 m
      _ = (3 ^ m) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ < (2 ^ p2_of m) ^ d := Nat.pow_lt_pow_left h1 (by omega)
      _ = 2 ^ (d * p2_of m) := by rw [← pow_mul, mul_comm]
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have hp := one_le_p2_of d
  unfold fd
  have : ((m * (p2_of d - 1) : ℕ) : ℤ) = (m : ℤ) * ((p2_of d : ℤ) - 1) := by
    push_cast [Nat.cast_sub hp]; ring
  omega

/-- f_d adds up over a list. -/
theorem fd_sum (d : ℕ) (os : List ℕ) :
    (d : ℤ) * ((os.map p2_of).sum : ℕ) - ((os.sum : ℕ) : ℤ) * ((p2_of d : ℤ) - 1) =
      (os.map (fd d)).sum := by
  induction os with
  | nil => simp
  | cons m os ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add] at *
    rw [← ih]; unfold fd; ring

/-- Every split of n has at most f_d(n) parts. -/
theorem length_le_fd {d n : ℕ} (hd : 1 ≤ d) {os : List ℕ} (h : RowSplit n os) :
    (os.length : ℤ) ≤ fd d n := by
  obtain ⟨hpos, hs, hp⟩ := h
  have e := fd_sum d os
  rw [hs, hp] at e
  have : fd d n = (os.map (fd d)).sum := by rw [← e]; rfl
  rw [this]
  have key : ∀ l : List ℕ, (∀ m ∈ l, 1 ≤ m) → (l.length : ℤ) ≤ (l.map (fd d)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons m l ih =>
      intro hl
      simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
      have := one_le_fd hd m
      have := ih (fun x hx => hl x (by simp [hx]))
      linarith
  exact key os hpos

/-- A split whose parts all have f_d = 1 has exactly f_d(n) parts. -/
theorem length_eq_fd {d n : ℕ} {os : List ℕ} (h : RowSplit n os) (h1 : ∀ m ∈ os, fd d m = 1) :
    (os.length : ℤ) = fd d n := by
  obtain ⟨_, hs, hp⟩ := h
  have e := fd_sum d os
  rw [hs, hp] at e
  have : fd d n = (os.map (fd d)).sum := by rw [← e]; rfl
  rw [this]
  have key : ∀ l : List ℕ, (∀ m ∈ l, fd d m = 1) → (l.length : ℤ) = (l.map (fd d)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons m l ih =>
      intro hl
      simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
      rw [hl m (by simp), ih (fun x hx => hl x (by simp [hx]))]; ring
  exact key os h1

theorem p2_le_double {n : ℕ} (hn1 : 1 ≤ n) : p2_of n ≤ 2 * n := by
  have h := p2_of_spec_lower n
  have h4 : 3 ^ n ≤ 2 ^ (2 * n) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) n
  have h4' : 3 ^ n < 2 ^ (2 * n) := by
    rw [pow_mul]; exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h h4')
  omega

/-- p2(x + y) = p2(x) + p2(y) iff θ(x + y) = θ(x) θ(y), else p2(x + y) + 1 = p2(x) + p2(y)
    and θ(x + y) = 2 θ(x) θ(y). -/
theorem blockFactor_add_p2 (x y : ℕ) :
    (blockFactor (x + y) = blockFactor x * blockFactor y ∧ p2_of (x + y) = p2_of x + p2_of y) ∨
      (blockFactor (x + y) = 2 * blockFactor x * blockFactor y ∧
        p2_of (x + y) + 1 = p2_of x + p2_of y) := by
  simp only [blockFactor_eq]
  rcases p2_of_add x y with h | h
  · left; refine ⟨?_, h⟩; rw [h, pow_add, pow_add]; field_simp
  · right; refine ⟨?_, h⟩
    have hq : (2 : ℚ) ^ p2_of (x + y) = 2 ^ p2_of x * 2 ^ p2_of y / 2 := by
      rw [← pow_add, ← h, pow_succ]; ring
    rw [hq, pow_add]; field_simp

/-- The highest floor up to N has the least slope p2(k)/k up to N. -/
theorem slope_le_of_max {N b : ℕ} (hb1 : 1 ≤ b)
    (hmax : ∀ k, 1 ≤ k → k ≤ N → blockFactor k ≤ blockFactor b) :
    ∀ k, 1 ≤ k → k ≤ N → k * p2_of b ≤ b * p2_of k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkN
    by_contra hc
    rw [not_le] at hc
    -- k > b: else k p2(b) < b p2(k) by k p2(b) ≤ ... (p2 is monotone in the slope sense)
    by_cases hkb : k ≤ b
    · rcases Nat.eq_or_lt_of_le hkb with rfl | hlt
      · exact lt_irrefl _ hc
      obtain ⟨j, hj⟩ : ∃ j, b = k + j := ⟨b - k, by omega⟩
      have hj1 : 1 ≤ j := by omega
      rcases blockFactor_add_p2 k j with ⟨h, hp⟩ | ⟨h, hp⟩
      · exfalso
        have := hmax k hk1 hkN
        rw [← hj] at h; rw [h] at this
        nlinarith [blockFactor_lt_one j, blockFactor_pos k, blockFactor_pos j]
      · -- p2(b) + 1 = p2(k) + p2(j): then f_j(k) < 1
        rw [← hj] at hp
        have hf := one_le_fd hj1 k
        unfold fd at hf
        have hpj := one_le_p2_of j
        subst hj
        zify at hc hp
        nlinarith
    · rw [not_le] at hkb
      obtain ⟨j, hj⟩ : ∃ j, k = j + b := ⟨k - b, by omega⟩
      have hj1 : 1 ≤ j := by omega
      rcases blockFactor_add_p2 j b with ⟨h, hp⟩ | ⟨h, hp⟩
      · rw [← hj] at hp
        have := ih j (by omega) hj1 (by omega)
        subst hj
        nlinarith
      · exfalso
        have := hmax k hk1 hkN
        rw [← hj] at h; rw [h] at this
        nlinarith [half_lt_blockFactor hj1, blockFactor_pos b]

/-- The record walk with its invariant and the splits reached so far. -/
def FloorWalk (N : ℕ) : Prop :=
  ∃ a b, 1 ≤ a ∧ a ≤ N ∧ 1 ≤ b ∧ b ≤ N ∧
    (∀ k, 1 ≤ k → k ≤ N → blockFactor a ≤ blockFactor k) ∧
    (∀ k, 1 ≤ k → k ≤ N → blockFactor k ≤ blockFactor b) ∧
    a * p2_of b + b = b * p2_of a + 1 ∧
    ∀ n, 1 ≤ n → n * p2_of b ≤ b * p2_of n →
      ∃ d os, 1 ≤ d ∧ RowSplit n os ∧ ∀ m ∈ os, fd d m = 1

theorem isSplit_replicate_append {n x y u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hs : x * u + y * v = n) (hp : x * p2_of u + y * p2_of v = p2_of n) :
    RowSplit n (List.replicate x u ++ List.replicate y v) := by
  refine ⟨fun m hm => ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hm with h | h
    · rw [List.eq_of_mem_replicate h]; exact hu
    · rw [List.eq_of_mem_replicate h]; exact hv
  · simp [List.sum_replicate, hs]
  · simp [List.map_replicate, List.sum_replicate, hp]

theorem floorWalk_one : FloorWalk 1 := by
  have h1 : p2_of 1 = 2 := by
    have : Nat.log 2 3 = 1 := by rw [Nat.log_eq_iff (by norm_num)]; norm_num
    simp [p2_of, this]
  refine ⟨1, 1, le_rfl, le_rfl, le_rfl, le_rfl, fun k hk1 hk => ?_, fun k hk1 hk => ?_, by omega,
    fun n hn hs => ?_⟩
  · rw [show k = 1 by omega]
  · rw [show k = 1 by omega]
  · have hp : p2_of n = 2 * n := by
      have := p2_le_double hn; rw [h1] at hs; omega
    refine ⟨1, List.replicate n 1, le_rfl, ?_, fun m hm => ?_⟩
    · have := isSplit_replicate_append (x := n) (y := 0) (u := 1) (v := 1) le_rfl le_rfl
        (by ring) (by rw [h1, hp]; ring)
      simpa using this
    · rw [List.eq_of_mem_replicate hm]; unfold fd; rw [h1]; norm_num

theorem floorWalk_succ {N : ℕ} (hN : 1 ≤ N) (hW : FloorWalk N) : FloorWalk (N + 1) := by
  obtain ⟨a, b, ha1, haN, hb1, hbN, hmin, hmax, hinv, hB⟩ := hW
  have hge := add_ge_of_extremes ha1 hb1 hmin hmax
  rcases Nat.lt_or_ge (N + 1) (a + b) with hlt | hge'
  · -- no new record
    refine ⟨a, b, ha1, by omega, hb1, by omega, fun k hk1 hk => ?_, fun k hk1 hk => ?_, hinv, hB⟩
    · exact (extremes_until ha1 haN hb1 hbN hmin hmax hk1 (by omega)).1
    · exact (extremes_until ha1 haN hb1 hbN hmin hmax hk1 (by omega)).2
  · have hab : a + b = N + 1 := by omega
    have hall : ∀ k, 1 ≤ k → k < a + b →
        blockFactor a ≤ blockFactor k ∧ blockFactor k ≤ blockFactor b :=
      fun k hk1 hk => extremes_until ha1 haN hb1 hbN hmin hmax hk1 hk
    have ha0 := blockFactor_pos a
    have hb0 := blockFactor_pos b
    have ha2 := half_lt_blockFactor ha1
    have hb2 := half_lt_blockFactor hb1
    rcases blockFactor_add_p2 a b with ⟨h, hp⟩ | ⟨h, hp⟩
    · -- a new lower record a + b
      refine ⟨a + b, b, by omega, by omega, hb1, by omega, fun k hk1 hk => ?_,
        fun k hk1 hk => ?_, ?_, hB⟩
      · rcases Nat.lt_or_ge k (a + b) with hk' | hk'
        · have := (hall k hk1 hk').1; rw [h]; nlinarith [blockFactor_lt_one b]
        · rw [show k = a + b by omega]
      · rcases Nat.lt_or_ge k (a + b) with hk' | hk'
        · exact (hall k hk1 hk').2
        · rw [show k = a + b by omega, h]; nlinarith [blockFactor_lt_one a]
      · rw [hp]
        have : 1 ≤ p2_of a := one_le_p2_of a
        have : 1 ≤ p2_of b := one_le_p2_of b
        nlinarith
    · -- a new upper record b' = a + b
      have hinv' : a * p2_of (a + b) + (a + b) = (a + b) * p2_of a + 1 := by
        have : 1 ≤ p2_of a := one_le_p2_of a
        zify at hinv hp ⊢
        nlinarith
      refine ⟨a, a + b, ha1, by omega, by omega, by omega, fun k hk1 hk => ?_,
        fun k hk1 hk => ?_, hinv', fun n hn hs => ?_⟩
      · rcases Nat.lt_or_ge k (a + b) with hk' | hk'
        · exact (hall k hk1 hk').1
        · rw [show k = a + b by omega, h]; nlinarith [blockFactor_lt_one b]
      · rcases Nat.lt_or_ge k (a + b) with hk' | hk'
        · have := (hall k hk1 hk').2; rw [h]; nlinarith
        · rw [show k = a + b by omega]
      · by_cases hold : n * p2_of b ≤ b * p2_of n
        · exact hB n hn hold
        · rw [not_le] at hold
          -- (n, p2 n) = x (b, p2 b) + y (b', p2 b')
          set b' := a + b with hb'
          set P := p2_of n
          have hdet : (b' : ℤ) * p2_of b - b * p2_of b' = 1 := by
            zify at hinv hp; rw [hb']; push_cast; nlinarith
          set x : ℤ := b' * P - n * p2_of b' with hx
          set y : ℤ := n * p2_of b - b * P with hy
          have hx0 : 0 ≤ x := by rw [hx]; zify at hs; linarith
          have hy0 : 0 < y := by rw [hy]; zify at hold; linarith
          have hsz : x * b + y * b' = n := by
            rw [hx, hy]; linear_combination (n : ℤ) * hdet
          have hpz : x * p2_of b + y * p2_of b' = P := by
            rw [hx, hy]; linear_combination (P : ℤ) * hdet
          refine ⟨a, List.replicate x.toNat b ++ List.replicate y.toNat b', ha1, ?_, fun m hm => ?_⟩
          · apply isSplit_replicate_append hb1 (by omega)
            · zify; rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0.le]; exact hsz
            · zify; rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0.le]; exact hpz
          · have hfa : fd a b = 1 := by
              unfold fd; zify at hinv; linarith
            have hfb : fd a b' = 1 := by
              unfold fd; zify at hinv' ; linarith
            rcases List.mem_append.mp hm with h' | h'
            · rw [List.eq_of_mem_replicate h']; exact hfa
            · rw [List.eq_of_mem_replicate h']; exact hfb

theorem floorWalk {N : ℕ} (hN : 1 ≤ N) : FloorWalk N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN'
    · exact floorWalk_one
    · exact floorWalk_succ hN' (ih hN')

/-- The bound is reached: some split of n has f_d(n) parts. So the row length is
    R(n) = min_{d ≥ 1} f_d(n). -/
theorem exists_split_eq_fd {n : ℕ} (hn : 1 ≤ n) :
    ∃ d os, 1 ≤ d ∧ RowSplit n os ∧ (os.length : ℤ) = fd d n := by
  obtain ⟨a, b, ha1, haN, hb1, hbN, hmin, hmax, hinv, hB⟩ := floorWalk hn
  have hs := slope_le_of_max hb1 hmax n hn le_rfl
  obtain ⟨d, os, hd, hsplit, h1⟩ := hB n hn hs
  exact ⟨d, os, hd, hsplit, length_eq_fd hsplit h1⟩

/-- The row length of row n of A900014: some split of n has f_d(n) parts, and no split of n has
    more than f_d'(n) parts for any d' ≥ 1; so R(n) = min_{d ≥ 1} f_d(n). -/
theorem rowLength_eq_min {n : ℕ} (hn : 1 ≤ n) :
    ∃ d os, 1 ≤ d ∧ RowSplit n os ∧ (os.length : ℤ) = fd d n ∧
      ∀ d', 1 ≤ d' → ∀ os', RowSplit n os' → (os'.length : ℤ) ≤ fd d n ∧ fd d n ≤ fd d' n := by
  obtain ⟨d, os, hd, hs, hl⟩ := exists_split_eq_fd hn
  refine ⟨d, os, hd, hs, hl, fun d' hd' os' hs' => ⟨?_, ?_⟩⟩
  · exact length_le_fd hd hs'
  · rw [← hl]; exact length_le_fd hd' hs

end AcceleratedCollatz
