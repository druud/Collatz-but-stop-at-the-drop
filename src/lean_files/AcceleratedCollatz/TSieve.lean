-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TWidth

/-!
  Collatz-primes: the class ids 1, 2, 3, 7, 11, 15, 23, 27, 31, ... (2 and 1
  followed by OEIS A243115). Each is the least positive member of its class;
  all larger members x + i 2^p2 share its parity sequence. Sieve form
  (`isCollatzPrime_iff`): x is a Collatz-prime iff x ≤ 2^n, n its coefficient
  stopping time. For odd x and y = T^k x, 1 ≤ k ≤ n, the first m ≤ n - k bits of y
  have lower order than the first n bits of x (`order_lt_of_trajectory`), e.g.
  31 = T^3(27): order 35 < 37.
-/

namespace AcceleratedCollatz

/-- x is the class id of some admissible parity sequence. -/
def IsCollatzPrime (x : ℕ) : Prop := ∃ s, Admissible s ∧ classId s = x

/-- Sieve form: with tBits x n admissible, x is a Collatz-prime iff x ≤ 2^n. -/
theorem isCollatzPrime_iff (x n : ℕ) (hx0 : 0 < x) (hA : Admissible (tBits x n)) :
    IsCollatzPrime x ↔ x ≤ 2 ^ n := by
  have hsx : tBits x (tBits x n).length = tBits x n := by
    rw [length_tBits]
  constructor
  · rintro ⟨s, hA', hc⟩
    have hs' : tBits x s.length = s := by
      rw [← hc]
      exact tBits_classId s
    have heq := class_injective s (tBits x n) x hA' hA hs' hsx
    have hle := classId_le (tBits x n)
    rw [length_tBits] at hle
    rw [← hc, heq]
    exact hle
  · intro h
    refine ⟨tBits x n, hA, ?_⟩
    symm
    apply classId_unique _ x hx0
    · rw [length_tBits]
      exact h
    · rw [length_tBits]

/-- Order is additive under concatenation. -/
theorem order_append (a b : List Bool) : order (a ++ b) = order a + order b := by
  simp [order, List.filter_append]

theorem order_tBits_mono (x m n : ℕ) (h : m ≤ n) : order (tBits x m) ≤ order (tBits x n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [tBits_add, order_append]
  omega

/-- Order along a trajectory: y = T^k(x), 1 ≤ k ≤ n, x odd; y's first m ≤ n - k
    bits have lower order than x's first n bits. -/
theorem order_lt_of_trajectory (x n k m : ℕ) (hodd : x % 2 = 1) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hm : m ≤ n - k) : order (tBits (tStep^[k] x) m) < order (tBits x n) := by
  have hsplit : tBits x n = tBits x k ++ tBits (tStep^[k] x) (n - k) := by
    rw [← tBits_add]
    congr 1
    omega
  have hk : 1 ≤ order (tBits x k) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [tBits, order_cons, hodd]
  have hmono := order_tBits_mono (tStep^[k] x) m (n - k) hm
  rw [hsplit, order_append]
  omega

/-- Along an admissible drop at n, y = T^k(x) (1 ≤ k < n) drops within n - k steps. -/
theorem drop_along_trajectory (x n k : ℕ) (hx0 : 0 < x) (hA : Admissible (tBits x n))
    (hdrop : tStep^[n] x < x) (hk1 : 1 ≤ k) (hkn : k < n) :
    tStep^[n - k] (tStep^[k] x) < tStep^[k] x := by
  have hs : tBits x (tBits x n).length = tBits x n := by
    rw [length_tBits]
  have hkn' : k < (tBits x n).length := by
    rw [length_tBits]
    exact hkn
  have hlt := no_drop_before (tBits x n) x hA hs hx0 k hk1 hkn'
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hkn.le]
  omega

/-- Admissible, with natural-number powers instead of rational products. -/
theorem admissible_iff_pow (s : List Bool) :
    Admissible s ↔
      (∀ m < s.length, 1 ≤ m → 2 ^ m < 3 ^ order (s.take m)) ∧ 3 ^ order s < 2 ^ s.length := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (seqProduct_lt_one_iff s).mp h2⟩
    intro m hm h1m
    have h := (one_lt_seqProduct_iff _).mp (h1 m h1m hm)
    rwa [List.length_take, min_eq_left hm.le] at h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (seqProduct_lt_one_iff s).mpr h2⟩
    intro m h1m hm
    apply (one_lt_seqProduct_iff _).mpr
    rw [List.length_take, min_eq_left hm.le]
    exact h1 m hm h1m

theorem admissible_tBits_27 : Admissible (tBits 27 59) := by
  rw [admissible_iff_pow]
  decide

theorem admissible_tBits_31 : Admissible (tBits 31 56) := by
  rw [admissible_iff_pow]
  decide

example : IsCollatzPrime 27 :=
  (isCollatzPrime_iff 27 59 (by norm_num) admissible_tBits_27).mpr (by norm_num)

example : IsCollatzPrime 31 :=
  (isCollatzPrime_iff 31 56 (by norm_num) admissible_tBits_31).mpr (by norm_num)

example : order (tBits 27 59) = 37 := by
  decide

example : tStep^[3] 27 = 31 := by
  decide

example : order (tBits 31 56) = 35 := by
  decide

/-- 31 = T^3(27) has lower order than 27. -/
example : order (tBits (tStep^[3] 27) 56) < order (tBits 27 59) :=
  order_lt_of_trajectory 27 59 3 56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end AcceleratedCollatz
