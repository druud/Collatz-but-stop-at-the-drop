-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.DropEquivalence

/-!
  Drop as termination. From a start n, the rewrite step x ↦ f x is allowed
  while x ≥ n; the normal forms are exactly the values below n. The rewriting
  from n terminates (`Acc`) iff n drops, so DropsToward f m is termination from
  every start above m (`dropsToward_iff_acc`), and DropConjecture is
  termination under R from every start above 1 (`dropConjecture_iff_acc`).
-/

namespace AcceleratedCollatz

variable (f : ℕ → ℕ)

namespace DescendToMinimum

/-- One rewrite step toward a drop below n: y = f x, allowed while x ≥ n. -/
def DropStep (f : ℕ → ℕ) (n : ℕ) (y x : ℕ) : Prop :=
  n ≤ x ∧ y = f x

theorem exists_below_of_acc (n : ℕ) :
    ∀ x, Acc (DropStep f n) x → ∃ k, f^[k] x < n := by
  intro x hx
  induction hx with
  | intro x _ ih =>
    by_cases hlt : x < n
    · exact ⟨0, hlt⟩
    · obtain ⟨k, hk⟩ := ih (f x) ⟨by omega, rfl⟩
      exact ⟨k + 1, hk⟩

theorem acc_of_iterate_lt (n : ℕ) :
    ∀ k x, f^[k] x < n → Acc (DropStep f n) x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    refine Acc.intro x ?_
    rintro y ⟨hnx, _⟩
    simp only [Function.iterate_zero, id_eq] at hx
    omega
  | succ k ih =>
    intro x hx
    refine Acc.intro x ?_
    rintro y ⟨_, rfl⟩
    exact ih (f x) hx

/-- Rewriting from n terminates iff n drops below itself. -/
theorem acc_iff_drops (n : ℕ) :
    Acc (DropStep f n) n ↔ ∃ k ≥ 1, f^[k] n < n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_below_of_acc f n n h
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp at hk
    · exact ⟨k, hpos, hk⟩
  · rintro ⟨k, _, hk⟩
    exact acc_of_iterate_lt f n k n hk

theorem dropsToward_iff_acc (m : ℕ) :
    DropsToward f m ↔ ∀ n > m, Acc (DropStep f n) n := by
  constructor
  · intro h n hn
    exact (acc_iff_drops f n).mpr (h n hn)
  · intro h n hn
    exact (acc_iff_drops f n).mp (h n hn)

end DescendToMinimum

open DescendToMinimum

/-- DropConjecture as termination: from every start n > 1, R-rewriting while the
    value is at least n terminates. -/
theorem dropConjecture_iff_acc : DropConjecture ↔ ∀ n > 1, Acc (DropStep R n) n :=
  dropsToward_iff_acc R 1

end AcceleratedCollatz
