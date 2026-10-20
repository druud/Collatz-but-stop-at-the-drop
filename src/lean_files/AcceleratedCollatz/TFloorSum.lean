-- SPDX-License-Identifier: MIT
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
  The floor sum floorsum(n, m, a, b) = ∑_{i < n} ⌊(a i + b)/m⌋, computed by the classical
  Euclid-like recursion (`floorSum`): take out ⌊a/m⌋ and ⌊b/m⌋, then count the lattice
  points under the line the other way round, with m and a exchanged. This is the PARI
  function `floorsum` of the A003586 program. `floorSum_eq`: the recursion gives the sum. The
  counting steps: `card_filter_le_mul` (the i < n with c ≤ a i), `card_filter_succ_mul_le`
  (the k < K with (k + 1) m ≤ v), `sum_div_swap` (the lattice points both ways).
-/

namespace AcceleratedCollatz

open Finset

/-- ∑_{i < n} ⌊(a i + b)/m⌋ by the Euclid-like recursion (m = 0 gives 0). -/
def floorSum (n m a b : ℕ) : ℕ :=
  if hm : m = 0 then 0
  else
    n * (n - 1) / 2 * (a / m) + n * (b / m) +
      if a % m * n + b % m < m then 0
      else floorSum ((a % m * n + b % m) / m) (a % m) m ((a % m * n + b % m) % m)
termination_by m
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero hm)

/-- The i < n with c ≤ a i number ⌊(a n - c)/a⌋. -/
theorem card_filter_le_mul {a : ℕ} (ha : 0 < a) (c n : ℕ) :
    ((range n).filter (fun i => c ≤ a * i)).card = (a * n - c) / a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_add_one, filter_insert]
    by_cases hc : c ≤ a * n
    · have hnot : n ∉ (range n).filter (fun i => c ≤ a * i) := by
        simp
      simp only [hc, ↓reduceIte]
      rw [card_insert_of_notMem hnot, ih]
      have heq : a * (n + 1) - c = (a * n - c) + a := by
        rw [Nat.mul_succ]
        omega
      rw [heq, Nat.add_div_right _ ha]
    · simp only [hc, ↓reduceIte]
      rw [ih]
      have h1 : a * n - c = 0 := by omega
      have h2 : a * (n + 1) - c < a := by
        rw [Nat.mul_succ]
        omega
      rw [h1, Nat.zero_div, Nat.div_eq_of_lt h2]

/-- The k < K with (k + 1) m ≤ v number ⌊v/m⌋ when that is at most K. -/
theorem card_filter_succ_mul_le {m : ℕ} (hm : 0 < m) {v K : ℕ} (hv : v / m ≤ K) :
    ((range K).filter (fun k => (k + 1) * m ≤ v)).card = v / m := by
  have hset : (range K).filter (fun k => (k + 1) * m ≤ v) = range (v / m) := by
    ext k
    rw [mem_filter, mem_range, mem_range, ← Nat.le_div_iff_mul_le hm]
    omega
  rw [hset, card_range]

/-- The lattice points under the line, counted by columns and by rows: for 0 < a, b < m
    and y = a n + b, ∑_{i < n} ⌊(a i + b)/m⌋ = ∑_{j < ⌊y/m⌋} ⌊(m j + y mod m)/a⌋. -/
theorem sum_div_swap {n m a b : ℕ} (hm : 0 < m) (ha : 0 < a) (hb : b < m) :
    ∑ i ∈ range n, (a * i + b) / m =
      ∑ j ∈ range ((a * n + b) / m), (m * j + (a * n + b) % m) / a := by
  obtain ⟨K, hK⟩ : ∃ K, (a * n + b) / m = K := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, (a * n + b) % m = r := ⟨_, rfl⟩
  have hy : a * n + b = m * K + r := by
    rw [← hK, ← hr]
    exact (Nat.div_add_mod (a * n + b) m).symm
  rw [hK, hr]
  have hcol : ∀ i ∈ range n,
      (a * i + b) / m = ((range K).filter (fun k => (k + 1) * m ≤ a * i + b)).card := by
    intro i hi
    rw [mem_range] at hi
    have hle : a * i + b ≤ a * n + b := by
      have := Nat.mul_le_mul_left a hi.le
      omega
    have hdiv : (a * i + b) / m ≤ K := hK ▸ Nat.div_le_div_right hle
    exact (card_filter_succ_mul_le hm hdiv).symm
  have hrow : ∀ k ∈ range K,
      ((range n).filter (fun i => (k + 1) * m ≤ a * i + b)).card =
        (m * (K - 1 - k) + r) / a := by
    intro k hk
    rw [mem_range] at hk
    have hfil : (range n).filter (fun i => (k + 1) * m ≤ a * i + b) =
        (range n).filter (fun i => (k + 1) * m - b ≤ a * i) := by
      apply filter_congr
      intro i _
      omega
    rw [hfil, card_filter_le_mul ha]
    congr 1
    have hkm : (k + 1) * m + m * (K - 1 - k) = m * K := by
      rw [← Nat.mul_comm m (k + 1), ← Nat.mul_add]
      congr 1
      omega
    have e1 : a * n + b = (k + 1) * m + (m * (K - 1 - k) + r) := by
      rw [hy, ← hkm, Nat.add_assoc]
    have hmk : m ≤ (k + 1) * m := Nat.le_mul_of_pos_left m (Nat.succ_pos k)
    omega
  rw [sum_congr rfl hcol]
  simp_rw [card_filter]
  rw [sum_comm]
  have hrow' : ∀ k ∈ range K,
      (∑ i ∈ range n, if (k + 1) * m ≤ a * i + b then 1 else 0) =
        (m * (K - 1 - k) + r) / a := by
    intro k hk
    rw [← card_filter]
    exact hrow k hk
  rw [sum_congr rfl hrow']
  exact sum_range_reflect (fun j => (m * j + r) / a) K

/-- `floorSum` is the floor sum ∑_{i < n} ⌊(a i + b)/m⌋. -/
theorem floorSum_eq {m : ℕ} (hm : 0 < m) (n a b : ℕ) :
    floorSum n m a b = ∑ i ∈ range n, (a * i + b) / m := by
  induction m using Nat.strong_induction_on generalizing n a b with
  | _ m ih =>
    have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
    rw [floorSum]
    simp only [hm0, ↓reduceDIte]
    have hsplit : ∀ i ∈ range n, (a * i + b) / m =
        a / m * i + b / m + (a % m * i + b % m) / m := by
      intro i _
      have hai : a * i + b = m * (a / m * i + b / m) + (a % m * i + b % m) := by
        have h1 := Nat.div_add_mod a m
        have h2 := Nat.div_add_mod b m
        nth_rewrite 1 [← h1, ← h2]
        ring
      rw [hai, Nat.mul_add_div hm]
    rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, sum_const,
      card_range, Nat.nsmul_eq_mul]
    have hgauss : (∑ i ∈ range n, a / m * i) = n * (n - 1) / 2 * (a / m) := by
      rw [← mul_sum, Nat.mul_comm]
      congr 1
      rw [← sum_range_id_mul_two n, Nat.mul_div_cancel _ (by norm_num)]
    rw [← hgauss]
    congr 1
    by_cases hy : a % m * n + b % m < m
    · simp only [hy, ↓reduceIte]
      symm
      apply sum_eq_zero
      intro i hi
      rw [mem_range] at hi
      apply Nat.div_eq_of_lt
      have := Nat.mul_le_mul_left (a % m) hi.le
      omega
    · simp only [hy, ↓reduceIte]
      have ha : 0 < a % m := by
        by_contra h0
        have : a % m = 0 := by omega
        rw [this, Nat.zero_mul, Nat.zero_add] at hy
        exact hy (Nat.mod_lt b hm)
      rw [ih (a % m) (Nat.mod_lt a hm) ha, sum_div_swap hm ha (Nat.mod_lt b hm)]

end AcceleratedCollatz
