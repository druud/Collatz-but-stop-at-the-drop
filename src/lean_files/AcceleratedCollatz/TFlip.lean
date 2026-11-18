-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TMerge

/-!
  One digit flipped (Questions B71, B76, B84). A path that reaches 1 after k steps with word w
  (m its ones) has 3^m x + rho(w) = 2^k (`point_of_reach_one`): x = (2^k - rho(w))/3^m.
  Two starts whose words agree on the first i digits and whose paths meet one step later,
  but not before, are a merge pair {o, 3o + 1} at step i (`tStep_eq_tStep_iff`, TMerge), and
  then 3^s (x' - x) = 2^i (2y + 1) or -2^i (2y' + 1), with s the ones among the first i digits
  and y, y' the values at step i (`flip_digit`): the flip of digit i moves x by 2^i (2y + 1)/3^s,
  B76's formula read in ℤ, without 2-adic numbers.
-/

namespace AcceleratedCollatz

/-- B71: a path that reaches 1 after k steps: 3^m x + rho(w) = 2^k. -/
theorem point_of_reach_one (x k : ℕ) (h : tStep^[k] x = 1) :
    3 ^ order (tBits x k) * x + rho (tBits x k) = 2 ^ k := by
  have e := tStep_iterate_nForm k x
  rw [h, mul_one] at e
  exact e.symm

/-- B76: the words of x and x' agree on the first i digits, the paths are apart at step i and
    together at step i + 1. Then 3^s (x' - x) = 2^i (2y + 1) (y odd, y' = 3y + 1) or
    3^s (x' - x) = -2^i (2y' + 1) (y' odd, y = 3y' + 1), with y = T^i(x), y' = T^i(x'). -/
theorem flip_digit (x x' i : ℕ) (hw : tBits x i = tBits x' i)
    (hne : tStep^[i] x ≠ tStep^[i] x') (hm : tStep^[i + 1] x = tStep^[i + 1] x') :
    (3 : ℤ) ^ order (tBits x i) * ((x' : ℤ) - x) = 2 ^ i * (2 * tStep^[i] x + 1) ∨
      (3 : ℤ) ^ order (tBits x i) * ((x' : ℤ) - x) = -(2 ^ i * (2 * tStep^[i] x' + 1)) := by
  have ex := tStep_iterate_nForm i x
  have ex' := tStep_iterate_nForm i x'
  rw [← hw] at ex'
  have exz : (2 : ℤ) ^ i * (tStep^[i] x : ℕ) =
      3 ^ order (tBits x i) * (x : ℤ) + (rho (tBits x i) : ℕ) := by exact_mod_cast ex
  have exz' : (2 : ℤ) ^ i * (tStep^[i] x' : ℕ) =
      3 ^ order (tBits x i) * (x' : ℤ) + (rho (tBits x i) : ℕ) := by exact_mod_cast ex'
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hm
  rcases (tStep_eq_tStep_iff _ _ hne).1 hm with ⟨_, h⟩ | ⟨_, h⟩
  · left
    have hz : ((tStep^[i] x' : ℕ) : ℤ) = 3 * (tStep^[i] x : ℕ) + 1 := by exact_mod_cast h
    rw [hz] at exz'
    linarith
  · right
    have hz : ((tStep^[i] x : ℕ) : ℤ) = 3 * (tStep^[i] x' : ℕ) + 1 := by exact_mod_cast h
    rw [hz] at exz
    linarith

end AcceleratedCollatz
