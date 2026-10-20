-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TNest
import AcceleratedCollatz.TSieve

/-!
  Mersenne starts. For odd k ≥ 5, s = 2^k - 1 and 2s + 1 = 2^(k+1) - 1 both reach
  M = (3^(k+1) - 1)/8 after k + 1 odd steps (s after k + 3 steps, 2s + 1 after
  k + 4), neither drops before M, and on the shared path the drop below 2s + 1
  comes no later than the drop below s: Order(2^(k+1) - 1) ≤ Order(2^k - 1)
  (`order_mersenne_succ_le`).
-/

namespace AcceleratedCollatz

/-- The first k steps of 2^k - 1 are odd: T^j(2^k - 1) = 3^j 2^(k-j) - 1. -/
theorem mersenne_iterate (k : ℕ) :
    ∀ j ≤ k, tStep^[j] (2 ^ k - 1) = 3 ^ j * 2 ^ (k - j) - 1 := by
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hj
    rw [Function.iterate_succ_apply', ih (by omega)]
    obtain ⟨e, he⟩ : ∃ e, k - j = e + 1 := ⟨k - j - 1, by omega⟩
    have he' : k - (j + 1) = e := by omega
    rw [he, he']
    have hA : 0 < 3 ^ j * 2 ^ e := by positivity
    have h1 : 3 ^ j * 2 ^ (e + 1) = 2 * (3 ^ j * 2 ^ e) := by ring
    have h2 : 3 ^ (j + 1) * 2 ^ e = 3 * (3 ^ j * 2 ^ e) := by ring
    rw [h1, h2, tStep_odd _ (by omega)]
    omega

theorem mersenne_iterate_odd (k i : ℕ) (hi : i < k) : tStep^[i] (2 ^ k - 1) % 2 = 1 := by
  rw [mersenne_iterate k i hi.le]
  obtain ⟨e, he⟩ : ∃ e, k - i = e + 1 := ⟨k - i - 1, by omega⟩
  rw [he]
  have hA : 0 < 3 ^ i * 2 ^ e := by positivity
  have h1 : 3 ^ i * 2 ^ (e + 1) = 2 * (3 ^ i * 2 ^ e) := by ring
  rw [h1]
  omega

theorem mersenne_iterate_ge (k i : ℕ) (hi : i ≤ k) : 2 ^ k - 1 ≤ tStep^[i] (2 ^ k - 1) := by
  rw [mersenne_iterate k i hi]
  have h : 2 ^ k ≤ 3 ^ i * 2 ^ (k - i) := by
    calc 2 ^ k = 2 ^ i * 2 ^ (k - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
      _ ≤ 3 ^ i * 2 ^ (k - i) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) i)
  omega

theorem tBits_mersenne (k : ℕ) : tBits (2 ^ k - 1) k = List.replicate k true :=
  tBits_replicate true k _ (fun i hi => by simp [mersenne_iterate_odd k i hi])

theorem order_replicate_true (n : ℕ) : order (List.replicate n true) = n := by
  simp [order]

theorem three_pow_mod_eight (k : ℕ) (hk : k % 2 = 1) : 3 ^ k % 8 = 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem seven_two_pow_le (k : ℕ) (hk : 5 ≤ k) : 7 * 2 ^ k ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    norm_num
  | succ n _ ih =>
    rw [pow_succ, pow_succ]
    omega

/-- Order(2^(k+1) - 1) ≤ Order(2^k - 1) for odd k ≥ 5 (drops given). -/
theorem order_mersenne_succ_le (k : ℕ) (hk : 5 ≤ k) (hodd : k % 2 = 1) {j j' : ℕ}
    (hj : IsFirstDrop (tTraj (2 ^ k - 1)) 0 j)
    (hj' : IsFirstDrop (tTraj (2 ^ (k + 1) - 1)) 0 j') :
    order (tBits (2 ^ (k + 1) - 1) j') ≤ order (tBits (2 ^ k - 1) j) := by
  set s := 2 ^ k - 1 with hs
  set t := 2 ^ (k + 1) - 1 with ht
  set B := 3 ^ k with hB
  set P := 2 ^ k with hP
  have hB8 : B % 8 = 3 := three_pow_mod_eight k hodd
  have hBP : 7 * P ≤ B := seven_two_pow_le k hk
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have ht2 : t = 2 * P - 1 := by
    rw [ht, pow_succ]
    omega
  -- s: k odd steps to B - 1, then halving, odd step, halving to M
  have hsk : tStep^[k] s = B - 1 := by
    rw [hs, mersenne_iterate k k le_rfl]
    simp [hB]
  have e1 : tStep (B - 1) = (B - 1) / 2 := tStep_even _ (by omega)
  have e2 : tStep ((B - 1) / 2) = (3 * ((B - 1) / 2) + 1) / 2 := tStep_odd _ (by omega)
  have e3 : tStep ((3 * ((B - 1) / 2) + 1) / 2) = (3 * ((B - 1) / 2) + 1) / 2 / 2 :=
    tStep_even _ (by omega)
  -- t: k + 1 odd steps to 3B - 1, then three halvings to M
  have htk : tStep^[k + 1] t = 3 * B - 1 := by
    rw [ht, mersenne_iterate (k + 1) (k + 1) le_rfl]
    simp [hB, pow_succ]
    ring_nf
  have f1 : tStep (3 * B - 1) = (3 * B - 1) / 2 := tStep_even _ (by omega)
  have f2 : tStep ((3 * B - 1) / 2) = (3 * B - 1) / 2 / 2 := tStep_even _ (by omega)
  have f3 : tStep ((3 * B - 1) / 2 / 2) = (3 * B - 1) / 2 / 2 / 2 := tStep_even _ (by omega)
  set M := (3 * B - 1) / 8 with hM
  have hsM : tStep^[k + 3] s = M := by
    rw [show k + 3 = 3 + k by omega, Function.iterate_add_apply, hsk]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, e1, e2, e3]
    omega
  have htM : tStep^[k + 4] t = M := by
    rw [show k + 4 = 3 + (k + 1) by omega, Function.iterate_add_apply, htk]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, f1, f2, f3]
    omega
  -- no drop before M
  have hs_ge : ∀ i, i ≤ k + 3 → s ≤ tStep^[i] s := by
    intro i hi
    rcases (by omega : i ≤ k ∨ i = k + 1 ∨ i = k + 2 ∨ i = k + 3) with h | rfl | rfl | rfl
    · exact mersenne_iterate_ge k i h
    · rw [Function.iterate_succ_apply', hsk, e1]
      omega
    · rw [show k + 2 = 2 + k by omega, Function.iterate_add_apply, hsk]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, e1, e2]
      omega
    · rw [hsM]
      omega
  have ht_ge : ∀ i, i ≤ k + 4 → t ≤ tStep^[i] t := by
    intro i hi
    rcases (by omega : i ≤ k + 1 ∨ i = k + 2 ∨ i = k + 3 ∨ i = k + 4) with
      h | rfl | rfl | rfl
    · exact mersenne_iterate_ge (k + 1) i h
    · rw [Function.iterate_succ_apply', htk, f1]
      omega
    · rw [show k + 3 = 2 + (k + 1) by omega, Function.iterate_add_apply, htk]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, f1, f2]
      omega
    · rw [htM]
      omega
  -- drop positions past the merge
  obtain ⟨hj0, hjlt, hjmin⟩ := hj
  obtain ⟨hj0', hjlt', hjmin'⟩ := hj'
  simp only [tTraj, Function.iterate_zero_apply] at hjlt hjmin hjlt' hjmin'
  have hjk : k + 3 < j := by
    by_contra h
    have := hs_ge j (by omega)
    omega
  have hjk' : k + 4 < j' := by
    by_contra h
    have := ht_ge j' (by omega)
    omega
  obtain ⟨d, rfl⟩ : ∃ d, j = (k + 3) + d := ⟨j - (k + 3), by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', j' = (k + 4) + d' := ⟨j' - (k + 4), by omega⟩
  have hvs : tStep^[(k + 3) + d] s = tStep^[d] M := by
    rw [add_comm, Function.iterate_add_apply, hsM]
  have hvt : ∀ e, tStep^[(k + 4) + e] t = tStep^[e] M := by
    intro e
    rw [add_comm, Function.iterate_add_apply, htM]
  have hdd : d' ≤ d := by
    by_contra h
    have := hjmin' ((k + 4) + d) (by omega) (by omega)
    rw [hvt d] at this
    rw [hvs] at hjlt
    omega
  -- Orders: k + 1 up to M, then the shared tail
  have hos : order (tBits s (k + 3)) = k + 1 := by
    rw [tBits_add, hsk, order_append, hs, tBits_mersenne, order_replicate_true]
    have p1 : (B - 1) % 2 = 0 := by omega
    have p2 : (B - 1) / 2 % 2 = 1 := by omega
    have p3 : (3 * ((B - 1) / 2) + 1) / 2 % 2 = 0 := by omega
    simp [tBits, order, p1, p2, p3]
  have hot : order (tBits t (k + 4)) = k + 1 := by
    rw [show k + 4 = (k + 1) + 3 by omega, tBits_add, htk, order_append, ht, tBits_mersenne,
      order_replicate_true]
    have q1 : (3 * B - 1) % 2 = 0 := by omega
    have q2 : (3 * B - 1) / 2 % 2 = 0 := by omega
    have q3 : (3 * B - 1) / 2 / 2 % 2 = 0 := by omega
    simp [tBits, order, q1, q2, q3]
  rw [tBits_add, order_append, hot, htM, tBits_add s, order_append, hos, hsM]
  have := order_tBits_mono M d' d hdd
  omega

end AcceleratedCollatz
