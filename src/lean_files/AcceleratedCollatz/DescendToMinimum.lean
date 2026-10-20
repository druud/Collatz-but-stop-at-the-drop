-- SPDX-License-Identifier: MIT
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Function.Iterate

/-!
  Generic result: for any f : N -> N that never goes below a minimum m
  (`NeverBelowMin`), every n above m drops below itself at some point iff every
  n at or above m reaches m (`drop_equiv_reaches`). Nothing here is specific to
  R; DropEquivalence.lean instantiates this with f := R, m := 1.
-/

namespace AcceleratedCollatz

variable (f : ℕ → ℕ) (m : ℕ)

namespace DescendToMinimum

def DropsToward (f : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ n > m, ∃ k ≥ 1, f^[k] n < n

def ReachesMin (f : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ n ≥ m, ∃ k, f^[k] n = m

def NeverBelowMin (f : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ n ≥ m, f n ≥ m

theorem reaches_imp_drops (hR : ReachesMin f m) :
    DropsToward f m := by
  intro n hn
  obtain ⟨k, hk⟩ := hR n (by omega)
  have h_exists : ∃ j ≤ k, f^[j] n < n := by
    refine ⟨k, le_refl k, ?_⟩
    rw [hk]
    omega
  have hj_spec := Nat.find_spec h_exists
  have hj_pos : Nat.find h_exists ≥ 1 := by
    by_contra h0
    have hj0 : Nat.find h_exists = 0 := by omega
    rw [hj0] at hj_spec
    simp only [Function.iterate_zero, id_eq] at hj_spec
    omega
  refine ⟨Nat.find h_exists, hj_pos, ?_⟩
  exact hj_spec.2

theorem drops_imp_reaches
    (hD : DropsToward f m) (hN : NeverBelowMin f m) :
    ReachesMin f m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    by_cases hn : n ≤ m
    · have : n = m := by omega
      exact ⟨0, this⟩
    · have hn' : n > m := by omega
      obtain ⟨k, hk1, hk_drop⟩ := hD n hn'
      have hfk : ∀ i, f^[i] n ≥ m := by
        intro i
        induction i with
        | zero => simpa using hn1
        | succ i ihi =>
          rw [Function.iterate_succ', Function.comp_apply]
          exact hN _ ihi
      obtain ⟨j, hj⟩ := ih (f^[k] n) hk_drop (hfk k)
      refine ⟨j + k, ?_⟩
      rw [Function.iterate_add, Function.comp_apply]
      exact hj

theorem drop_equiv_reaches (hN : NeverBelowMin f m) :
    DropsToward f m ↔ ReachesMin f m :=
  ⟨fun h => drops_imp_reaches f m h hN, reaches_imp_drops f m⟩

end DescendToMinimum

end AcceleratedCollatz
