-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.MarkedVector
import AcceleratedCollatz.TCorrespondence

/-!
  R-side fold in T-form. `rFoldFrom x` along x's own T-parity bits replays T,
  `rFold s = rho s / 2^|s|`, `classIdOf = -rho s / 3^(order s)`, and every x with
  parity sequence s satisfies x = classIdOf + (2^|s| / 3^(order s)) T^|s|(x).
-/

namespace AcceleratedCollatz

/-- Folding x's first n T-parity bits from x gives T^n(x). -/
theorem rFoldFrom_tBits (n x : ℕ) : rFoldFrom (x : ℚ) (tBits x n) = (tStep^[n] x : ℕ) := by
  induction n generalizing x with
  | zero =>
    simp [tBits, rFoldFrom]
  | succ n ih =>
    rw [tBits, rFoldFrom_cons, Function.iterate_succ_apply, ← ih (tStep x)]
    congr 1
    by_cases h : x % 2 = 1
    · have hn : 2 * tStep x = 3 * x + 1 := by
        rw [tStep_odd x h]
        omega
      have hq : (2 : ℚ) * (tStep x : ℕ) = 3 * x + 1 := by
        exact_mod_cast hn
      simp only [h, decide_true, ↓reduceIte]
      linarith
    · have hn : 2 * tStep x = x := by
        rw [tStep_even x h]
        omega
      have hq : (2 : ℚ) * (tStep x : ℕ) = x := by
        exact_mod_cast hn
      simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      linarith

theorem rFold_eq_rho (s : List Bool) : rFold s = rho s / 2 ^ s.length := by
  obtain ⟨x, _, _, hs⟩ := exists_pos_tBits_eq s
  have h1 := rFoldFrom_tBits s.length x
  rw [hs] at h1
  have h2 := rFoldFrom_linear s x
  rw [← order_eq_count_true, h1] at h2
  have h3 := tStep_iterate_nForm s.length x
  rw [hs] at h3
  have h3q : (2 : ℚ) ^ s.length * (tStep^[s.length] x : ℕ) = 3 ^ order s * x + rho s := by
    exact_mod_cast h3
  have h2pos : (2 : ℚ) ^ s.length ≠ 0 := by positivity
  rw [eq_div_iff h2pos, rFold]
  rw [h2] at h3q
  field_simp at h3q
  linarith

theorem classIdOf_eq (s : List Bool) :
    classIdOf s.length (order s) s = -(rho s : ℚ) / 3 ^ order s := by
  rw [classIdOf, rFold_eq_rho]
  field_simp

/-- Recovery: x = classIdOf + (2^n / 3^(order)) T^n(x), with the bits of x itself. -/
theorem eq_classIdOf_add (x n : ℕ) :
    (x : ℚ) = classIdOf n (order (tBits x n)) (tBits x n) +
      2 ^ n / 3 ^ order (tBits x n) * (tStep^[n] x : ℕ) := by
  have hc := classIdOf_eq (tBits x n)
  rw [length_tBits] at hc
  rw [hc]
  have h3 := tStep_iterate_nForm n x
  have h3q : (2 : ℚ) ^ n * (tStep^[n] x : ℕ) = 3 ^ order (tBits x n) * x + rho (tBits x n) := by
    exact_mod_cast h3
  have h3pos : (3 : ℚ) ^ order (tBits x n) ≠ 0 := by positivity
  field_simp
  linarith

/-- classId s = classIdOf + (2^|s| / 3^(order s)) T^|s|(classId s). -/
theorem classId_eq_classIdOf_add (s : List Bool) :
    (classId s : ℚ) = classIdOf s.length (order s) s +
      2 ^ s.length / 3 ^ order s * (tStep^[s.length] (classId s) : ℕ) := by
  have h := eq_classIdOf_add (classId s) s.length
  rw [tBits_classId] at h
  exact h

end AcceleratedCollatz
