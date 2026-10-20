-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhoBound

/-!
  A lower bound on rho. The i-th odd step of a word of Order n sits at a position
  k ≥ i - 1 and contributes 3^(n - i) 2^k to rho, so rho s ≥ 3^n - 2^n
  (`three_pow_le_rho_add`), with equality exactly for the words that start with all
  their odd steps (`rho_add_eq_three_pow_iff`). rho is positive exactly from Order 1
  on (`rho_pos_iff`).
-/

namespace AcceleratedCollatz

/-- 3^n ≤ rho s + 2^n for a word s of Order n. -/
theorem three_pow_le_rho_add (s : List Bool) : 3 ^ order s ≤ rho s + 2 ^ order s := by
  induction s using List.reverseRecOn with
  | nil =>
    simp [rho, affineNum, order]
  | append_singleton p b ih =>
    cases b with
    | false =>
      rw [rho_append_false, order_append_single]
      simpa using ih
    | true =>
      have hle : 2 ^ order p ≤ 2 ^ p.length :=
        Nat.pow_le_pow_right (by norm_num) (order_le_length p)
      rw [rho_append_true, order_append_single]
      simp only [↓reduceIte]
      rw [pow_succ, pow_succ]
      omega

/-- A word whose Order is its length consists of odd steps only. -/
theorem eq_replicate_of_order_eq_length {s : List Bool} (h : order s = s.length) :
    s = List.replicate (order s) true := by
  rw [h, List.eq_replicate_iff]
  refine ⟨rfl, fun b hb => ?_⟩
  unfold order at h
  exact List.length_filter_eq_length_iff.mp h b hb

/-- rho of n odd steps: 3^n - 2^n. -/
theorem rho_replicate_true (n : ℕ) : rho (List.replicate n true) + 2 ^ n = 3 ^ n := by
  induction n with
  | zero =>
    simp [rho, affineNum]
  | succ n ih =>
    rw [List.replicate_succ', rho_append_true, List.length_replicate, pow_succ, pow_succ]
    omega

/-- Halvings at the end leave rho as it is. -/
theorem rho_append_replicate_false (s : List Bool) (k : ℕ) :
    rho (s ++ List.replicate k false) = rho s := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc, rho_append_false, ih]

/-- rho s = 3^n - 2^n exactly for the words of Order n that start with all their odd
    steps. -/
theorem rho_add_eq_three_pow_iff (s : List Bool) :
    rho s + 2 ^ order s = 3 ^ order s ↔
      ∃ k, s = List.replicate (order s) true ++ List.replicate k false := by
  constructor
  · induction s using List.reverseRecOn with
    | nil =>
      intro _
      exact ⟨0, by simp [order]⟩
    | append_singleton p b ih =>
      cases b with
      | false =>
        rw [rho_append_false, order_append_single]
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        intro h
        obtain ⟨k, hk⟩ := ih h
        refine ⟨k + 1, ?_⟩
        rw [List.replicate_succ', ← List.append_assoc, ← hk]
      | true =>
        have hlow := three_pow_le_rho_add p
        have hle : 2 ^ order p ≤ 2 ^ p.length :=
          Nat.pow_le_pow_right (by norm_num) (order_le_length p)
        rw [rho_append_true, order_append_single]
        simp only [↓reduceIte]
        rw [pow_succ, pow_succ]
        intro h
        have hpow : 2 ^ p.length = 2 ^ order p := by
          omega
        have hlen : order p = p.length := (Nat.pow_right_injective le_rfl hpow).symm
        refine ⟨0, ?_⟩
        rw [List.replicate_zero, List.append_nil, List.replicate_succ',
          ← eq_replicate_of_order_eq_length hlen]
  · rintro ⟨k, hk⟩
    rw [congrArg rho hk, rho_append_replicate_false]
    exact rho_replicate_true (order s)

/-- rho is positive exactly from Order 1 on. -/
theorem rho_pos_iff (s : List Bool) : 0 < rho s ↔ 0 < order s := by
  induction s using List.reverseRecOn with
  | nil =>
    simp [rho, affineNum, order]
  | append_singleton p b ih =>
    cases b with
    | false =>
      rw [rho_append_false, order_append_single]
      simpa using ih
    | true =>
      have h2 : 0 < 2 ^ p.length := by
        positivity
      rw [rho_append_true, order_append_single]
      simp only [↓reduceIte]
      omega

end AcceleratedCollatz
