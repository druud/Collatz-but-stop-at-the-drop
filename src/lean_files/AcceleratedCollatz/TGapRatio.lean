-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TDrop
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
  The gap at the drop (A37, 3 Nov 2026; OEIS A398772). For x with T-parity word s, admissible,
  and y = T^|s|(x) <= x: 2^|s| (x - y) + rho s = d_23 s * x (`gap_identity`), so the gap ratio
  g = (x - y)/x is (d_23 s * x - rho s)/(2^|s| x). Of two starts with the same word s and
  rho s > 0, both dropping at |s|, the smaller has the smaller gap ratio (`gap_mul_lt_of_lt`):
  a record low of g is the least start of its word.
-/

namespace AcceleratedCollatz

/-- 2^|s| (x - y) + rho s = d_23 s * x, y = T^|s|(x) <= x, for x with the admissible word s. -/
theorem gap_identity (s : List Bool) (x : ℕ) (hA : Admissible s) (hs : tBits x s.length = s)
    (hy : tStep^[s.length] x ≤ x) :
    2 ^ s.length * (x - tStep^[s.length] x) + rho s = d_23 s * x := by
  have hN := tStep_iterate_nForm s.length x
  rw [hs] at hN
  have hd : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  unfold d_23
  zify [hy, hd.le] at hN ⊢
  linear_combination (-1 : ℤ) * hN

/-- Two starts x' < x with the same admissible word s (rho s > 0), x' dropping at |s|:
  (x' - y') / x' < (x - y) / x, cross-multiplied. -/
theorem gap_mul_lt_of_lt (s : List Bool) (x x' : ℕ) (hA : Admissible s) (hρ : 0 < rho s)
    (hs : tBits x s.length = s) (hs' : tBits x' s.length = s) (hlt : x' < x)
    (hy' : tStep^[s.length] x' < x') :
    (x' - tStep^[s.length] x') * x < (x - tStep^[s.length] x) * x' := by
  have h1 := (drop_iff_rho s x' hA hs').mp hy'
  have hy : tStep^[s.length] x < x :=
    (drop_iff_rho s x hA hs).mpr (lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ hlt.le))
  have e := gap_identity s x hA hs hy.le
  have e' := gap_identity s x' hA hs' hy'.le
  have hp : 0 < 2 ^ s.length := by positivity
  zify [hy.le, hy'.le] at e e' ⊢
  have key : ((2 : ℤ) ^ s.length) * (((x : ℤ) - (tStep^[s.length] x : ℕ)) * x'
      - ((x' : ℤ) - (tStep^[s.length] x' : ℕ)) * x) = (rho s : ℤ) * (x - x') := by
    linear_combination (x' : ℤ) * e - (x : ℤ) * e'
  have hpos : (0 : ℤ) < (rho s : ℤ) * (x - x') := by
    have : (x' : ℤ) < x := by exact_mod_cast hlt
    have : (0 : ℤ) < rho s := by exact_mod_cast hρ
    positivity
  have hp' : (0 : ℤ) < 2 ^ s.length := by positivity
  nlinarith

end AcceleratedCollatz
