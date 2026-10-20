-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBinomial

/-!
  Binomial identity for A100982 over a range of lengths (M. Winkler). With
  m(i) = p2(i) - 1 and a(i) = |admSet i|: for every M ≥ m(n - 1),
  C(M, n - 1) = a(n) + Σ_{i=1..n-1} a(i) C(M - m(i), n - i)
  (`choose_eq_sum_admSet_of_le`). M = m(n) is `choose_eq_sum_admSet`;
  M = m(n - 1) is a recurrence for a(n).
-/

namespace AcceleratedCollatz

/-- Right-hand side of the range identity. -/
def rangeSum (n M : ℕ) : ℕ :=
  (admSet n).card +
    ∑ i ∈ Finset.Ico 1 n, (admSet i).card * (M - (p2_of i - 1)).choose (n - i)

/-- p2(k) ≥ 1. -/
theorem one_le_p2_of (k : ℕ) : 1 ≤ p2_of k := by
  simp [p2_of]

/-- The anchor M = m(n): `choose_eq_sum_admSet` in range form. -/
theorem rangeSum_anchor (n : ℕ) (hn : 1 ≤ n) :
    (p2_of n - 1).choose (n - 1) = rangeSum n (p2_of n - 1) := by
  rw [choose_eq_sum_admSet n hn, rangeSum]
  have hIcc : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by
    rw [← Finset.Ico_insert_right hn]
  rw [hIcc, Finset.sum_insert Finset.right_notMem_Ico]
  simp only [Nat.sub_self, Nat.choose_zero_right, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 := one_le_p2_of i
  have hi2 := one_le_p2_of n
  congr 2
  omega

/-- Pascal step in M: rangeSum (n + 1) (M + 1) = rangeSum (n + 1) M + rangeSum n M. -/
theorem rangeSum_succ (n M : ℕ) (hn : 1 ≤ n) (hM : p2_of n - 1 ≤ M) :
    rangeSum (n + 1) (M + 1) = rangeSum (n + 1) M + rangeSum n M := by
  have hstep : ∀ i ∈ Finset.Ico 1 (n + 1),
      (admSet i).card * (M + 1 - (p2_of i - 1)).choose (n + 1 - i) =
        (admSet i).card * (M - (p2_of i - 1)).choose (n + 1 - i) +
          (admSet i).card * (M - (p2_of i - 1)).choose (n - i) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hmono := p2_of_mono (Nat.lt_succ_iff.mp hi.2)
    have hsub : M + 1 - (p2_of i - 1) = (M - (p2_of i - 1)) + 1 := by
      omega
    have hk : n + 1 - i = (n - i) + 1 := by
      omega
    rw [hsub, hk, Nat.choose_succ_succ', mul_add, add_comm]
  have hsplit :
      ∑ i ∈ Finset.Ico 1 (n + 1), (admSet i).card * (M - (p2_of i - 1)).choose (n - i) =
      ∑ i ∈ Finset.Ico 1 n, (admSet i).card * (M - (p2_of i - 1)).choose (n - i) +
        (admSet n).card := by
    rw [Finset.sum_Ico_succ_top hn]
    simp
  unfold rangeSum
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hsplit]
  ring

/-- Range identity (M. Winkler): C(M, n - 1) = a(n) + Σ_{i<n} a(i) C(M - m(i), n - i). -/
theorem choose_eq_sum_admSet_of_le (n : ℕ) (hn : 1 ≤ n) :
    ∀ M, p2_of (n - 1) - 1 ≤ M → M.choose (n - 1) = rangeSum n M := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro M _
    have h1 := rangeSum_anchor 1 le_rfl
    have hc : (admSet 1).card = 1 := by
      rw [rangeSum] at h1
      simpa using h1.symm
    simp [rangeSum, hc]
  | succ n hn ih =>
    have hsucc : n + 1 - 1 = n := by
      omega
    rw [hsucc]
    have hmono : p2_of n ≤ p2_of (n + 1) := p2_of_mono (Nat.le_add_right n 1)
    have hshift : ∀ k, (p2_of n - 1 + k + 1).choose n = rangeSum (n + 1) (p2_of n - 1 + k + 1) ↔
        (p2_of n - 1 + k).choose n = rangeSum (n + 1) (p2_of n - 1 + k) := by
      intro k
      have hle : p2_of (n - 1) - 1 ≤ p2_of n - 1 + k := by
        have := p2_of_mono (Nat.sub_le n 1)
        omega
      have hih := ih (p2_of n - 1 + k) hle
      have hn1 : n = (n - 1) + 1 := by
        omega
      rw [rangeSum_succ n _ hn (Nat.le_add_right _ _)]
      conv_lhs => rw [hn1, Nat.choose_succ_succ', ← hn1, hih]
      omega
    have hall : ∀ k, (p2_of n - 1 + k).choose n = rangeSum (n + 1) (p2_of n - 1 + k) ↔
        (p2_of n - 1).choose n = rangeSum (n + 1) (p2_of n - 1) := by
      intro k
      induction k with
      | zero =>
        rfl
      | succ k hk =>
        rw [← add_assoc, hshift k, hk]
    have hanchor := rangeSum_anchor (n + 1) (by omega)
    rw [hsucc] at hanchor
    have hbase : (p2_of n - 1).choose n = rangeSum (n + 1) (p2_of n - 1) := by
      have h := (hall (p2_of (n + 1) - 1 - (p2_of n - 1))).mp
      have heq : p2_of n - 1 + (p2_of (n + 1) - 1 - (p2_of n - 1)) = p2_of (n + 1) - 1 := by
        omega
      rw [heq] at h
      exact h hanchor
    intro M hM
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
    exact (hall k).mpr hbase

end AcceleratedCollatz
