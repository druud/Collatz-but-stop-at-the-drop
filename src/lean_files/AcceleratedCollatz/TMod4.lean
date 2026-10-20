-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TEncode
import AcceleratedCollatz.TSieve

/-!
  sec:mod4. The first two T-parity bits are [1,1] iff x ≡ 3 mod 4
  (`tBits_two_eq_iff`); an admissible sequence of Order ≥ 2 starts with
  [1,1] (`admissible_take_two`); so class ids of Order ≥ 2 are 3 mod 4
  (`classId_mod4`). For x with an admissible parity prefix, the Order is
  0, 1 or ≥ 2 exactly when x is even, 1 mod 4 or 3 mod 4
  (`order_trichotomy`).
-/

namespace AcceleratedCollatz

theorem tBits_two_eq_iff (x : ℕ) : tBits x 2 = [true, true] ↔ x % 4 = 3 := by
  simp only [tBits]
  by_cases h : x % 2 = 1
  · rw [tStep_odd x h]
    simp only [h, decide_true, List.cons.injEq, decide_eq_true_eq, true_and, and_true]
    omega
  · simp only [h, decide_false, List.cons.injEq, Bool.false_eq_true, false_and, false_iff]
    omega

theorem admissible_take_two (s : List Bool) (hA : Admissible s) (hord : 2 ≤ order s) :
    s.take 2 = [true, true] := by
  have h32 : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have hlen : 2 < s.length := by
    by_contra hle
    have h9 : 3 ^ 2 ≤ 3 ^ order s := Nat.pow_le_pow_right (by norm_num) hord
    have h4 : 2 ^ s.length ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hp := ((admissible_iff_pow s).mp hA).1 2 hlen (by norm_num)
  match s, hlen with
  | a :: b :: rest, _ =>
    simp only [List.take_succ_cons, List.take_zero] at hp ⊢
    cases a with
    | true =>
      cases b with
      | true =>
        rfl
      | false =>
        simp [order] at hp
    | false =>
      cases b with
      | true =>
        simp [order] at hp
      | false =>
        simp [order] at hp

/-- sec:mod4: class ids of Order ≥ 2 are 3 mod 4. -/
theorem classId_mod4 (s : List Bool) (hA : Admissible s) (hord : 2 ≤ order s) :
    classId s % 4 = 3 := by
  have htake := admissible_take_two s hA hord
  have hlen : 2 ≤ s.length := by
    have := order_le_length s
    omega
  have h2 : tBits (classId s) 2 = [true, true] := by
    rw [← tBits_take (classId s) s.length 2 hlen, tBits_classId, htake]
  exact (tBits_two_eq_iff _).mp h2

/-- Order of x's admissible prefix: 0 ↔ even, 1 ↔ 1 mod 4, ≥ 2 ↔ 3 mod 4. -/
theorem order_trichotomy (x n : ℕ) (hA : Admissible (tBits x n)) :
    (order (tBits x n) = 0 ↔ x % 2 = 0) ∧ (order (tBits x n) = 1 ↔ x % 4 = 1) ∧
      (2 ≤ order (tBits x n) ↔ x % 4 = 3) := by
  have h0 : order (tBits x n) = 0 → x % 2 = 0 := by
    intro ho
    have hs := admissible_order_zero _ hA ho
    have hn : n = 1 := by
      have := length_tBits x n
      rw [hs] at this
      simp at this
      omega
    subst hn
    simp only [tBits, List.cons.injEq, decide_eq_false_iff_not, and_true] at hs
    omega
  have h1 : order (tBits x n) = 1 → x % 4 = 1 := by
    intro ho
    have hn : n = 2 := by
      have hl := admissible_length _ hA
      rw [ho, p2_of_one, length_tBits] at hl
      exact hl
    subst hn
    obtain ⟨u, hu⟩ := admissible_cons_true _ hA (by omega)
    have hodd : x % 2 = 1 := by
      simp only [tBits, List.cons.injEq, decide_eq_true_eq] at hu
      exact hu.1
    have heven : tStep x % 2 ≠ 1 := by
      intro hT
      rw [tStep_odd x hodd] at hT
      simp [tBits, order, hodd, hT] at ho
    rw [tStep_odd x hodd] at heven
    omega
  have h2 : 2 ≤ order (tBits x n) → x % 4 = 3 := by
    intro ho
    have htake := admissible_take_two _ hA ho
    have hlen : 2 ≤ n := by
      have := order_le_length (tBits x n)
      rw [length_tBits] at this
      omega
    rw [tBits_take x n 2 hlen] at htake
    exact (tBits_two_eq_iff x).mp htake
  refine ⟨⟨h0, ?_⟩, ⟨h1, ?_⟩, ⟨h2, ?_⟩⟩
  · intro hx
    by_contra hne
    rcases Nat.lt_or_ge (order (tBits x n)) 2 with hlt | hge
    · have := h1 (by omega)
      omega
    · have := h2 hge
      omega
  · intro hx
    by_contra hne
    rcases Nat.lt_or_ge (order (tBits x n)) 2 with hlt | hge
    · have := h0 (by omega)
      omega
    · have := h2 hge
      omega
  · intro hx
    by_contra hne
    rcases Nat.lt_or_ge (order (tBits x n)) 1 with hlt | hge
    · have := h0 (by omega)
      omega
    · have := h1 (by omega)
      omega

end AcceleratedCollatz
