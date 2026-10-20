-- SPDX-License-Identifier: MIT
import Mathlib.Data.Nat.Basic

/-!
  Bisection on the natural numbers, as in the A003586 program: `bisect f n lo hi` halves
  the interval (lo, hi] while it holds more than one number, keeping f(lo) < n ≤ f(hi).
  It ends at an r in (lo, hi] with f(r - 1) < n ≤ f(r) (`bisect_spec`); for monotone f
  that is the least r with n ≤ f(r).
-/

namespace AcceleratedCollatz

/-- Bisection for an r in (lo, hi] with f(r - 1) < n ≤ f(r). -/
def bisect (f : ℕ → ℕ) (n lo hi : ℕ) : ℕ :=
  if lo + 1 < hi then
    if f ((lo + hi) / 2) < n then bisect f n ((lo + hi) / 2) hi
    else bisect f n lo ((lo + hi) / 2)
  else hi
termination_by hi - lo

/-- With lo < hi and f(lo) < n ≤ f(hi), the result r has lo < r ≤ hi,
    n ≤ f(r) and f(r - 1) < n. -/
theorem bisect_spec (f : ℕ → ℕ) (n : ℕ) :
    ∀ lo hi, lo < hi → f lo < n → n ≤ f hi →
      lo < bisect f n lo hi ∧ bisect f n lo hi ≤ hi ∧ n ≤ f (bisect f n lo hi) ∧
        f (bisect f n lo hi - 1) < n := by
  intro lo hi
  induction lo, hi using bisect.induct f n with
  | case1 lo hi hlt hmid ih =>
    intro hlh hflo hfhi
    rw [bisect]
    simp only [hlt, hmid, ↓reduceIte]
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega) hmid hfhi
    exact ⟨by omega, h2, h3, h4⟩
  | case2 lo hi hlt hmid ih =>
    intro hlh hflo hfhi
    rw [bisect]
    simp only [hlt, hmid, ↓reduceIte]
    have hmid' : n ≤ f ((lo + hi) / 2) := Nat.le_of_not_lt hmid
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega) hflo hmid'
    exact ⟨h1, by omega, h3, h4⟩
  | case3 lo hi hlt =>
    intro hlh hflo hfhi
    rw [bisect]
    simp only [hlt, ↓reduceIte]
    have hlo : hi - 1 = lo := by omega
    rw [hlo]
    exact ⟨hlh, le_rfl, hfhi, hflo⟩

end AcceleratedCollatz
