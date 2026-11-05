-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Rule505
import AcceleratedCollatz.A349414Run

/-!
# The S column: A282798, the odd T-preimages of 2^(2m+1) and the letter S

Self-contained extract of the AcceleratedCollatz Lean 4 project; depends on Mathlib and
the extracts `Rule505` and `A349414Run` only (A63 of the project, 5 Nov 2026).

Both extracts define the same T (`T_eq`). The entry h 4 1 m = (4^(m+1) - 1)/3 of A401763
(1, 5, 21, 85, ..., A002450) is at once

* the odd T-preimage of 2^(2m+1) (`tPre_odd_eq`, `T_h41`),
* A282798(2m+1) + 1, the x-axis of Rule 505 at the odd stage 2m+1 read as a binary number,
  plus one (`axisVal_odd_add_one`); so A282798(2m+3) = 4 h 4 1 m (`axisVal_odd_eq_four_mul`),
* the offset of the letter power S^(m+1): 4^(m+1) y' + h 4 1 m = y (`pow_S_tPre`, with
  `A349414Run.pow_S`).

The letter S takes h 4 1 (m+1) to h 4 1 m (`st_h41`): the odd T-preimages of 2, 8, 32, 128,
... form one S-chain 85 → 21 → 5 → 1 (`st_iter_h41`).
-/

namespace A349414Pre

open A349414Run (h st)

/-- The two extracts define the same map T. -/
theorem T_eq : Rule505.T = A349414Run.T := rfl

theorem two_pow_eq (m : ℕ) : (2 : ℕ) ^ (2 * m + 2) = 4 ^ (m + 1) := by
  rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; norm_num

/-- The odd T-preimage of 2^(2m+1) is h 4 1 m = (4^(m+1) - 1)/3. -/
theorem tPre_odd_eq (m : ℕ) : Rule505.tPre (2 * m + 1) = h 4 1 m := by
  have h1 := Rule505.tPre_odd m
  have h2 := A349414Run.h41 m
  rw [two_pow_eq] at h1
  omega

/-- T (h 4 1 m) = 2^(2m+1). -/
theorem T_h41 (m : ℕ) : A349414Run.T (h 4 1 m) = 2 ^ (2 * m + 1) := by
  rw [← T_eq, ← tPre_odd_eq]; exact Rule505.T_tPre _

/-- A282798(2m+1) + 1 = h 4 1 m. -/
theorem axisVal_odd_add_one (m : ℕ) : Rule505.axisVal (2 * m + 1) + 1 = h 4 1 m := by
  rw [Rule505.axisVal_add_one, tPre_odd_eq]

/-- h 4 1 (m+1) = 1 + 4 h 4 1 m. -/
theorem h41_succ (m : ℕ) : h 4 1 (m + 1) = 1 + 4 * h 4 1 m := by
  rw [A349414Run.h_succ', one_pow]

/-- A282798(2m+3) = 4 h 4 1 m: the odd stages read 4 times the entries 1, 5, 21, 85, ... -/
theorem axisVal_odd_eq_four_mul (m : ℕ) : Rule505.axisVal (2 * m + 3) = 4 * h 4 1 m := by
  have h1 := axisVal_odd_add_one (m + 1)
  rw [h41_succ] at h1
  rw [show 2 * m + 3 = 2 * (m + 1) + 1 by ring]
  omega

/-- h 4 1 m is odd. -/
theorem h41_odd (m : ℕ) : h 4 1 m % 2 = 1 := by
  have h2 := A349414Run.h41 m
  have h4 : 4 ∣ 4 ^ (m + 1) := dvd_pow_self 4 (by omega)
  omega

/-- h 4 1 (m+1) ≡ 5 (mod 8): the letter S applies to it. -/
theorem h41_succ_mod (m : ℕ) : h 4 1 (m + 1) % 8 = 5 := by
  have := h41_odd m
  rw [h41_succ]; omega

/-- The letter S takes h 4 1 (m+1) to h 4 1 m. -/
theorem st_h41 (m a e : ℕ) : st (h 4 1 (m + 1), a, e) = (h 4 1 m, a, e + 2) := by
  have h5 := h41_succ_mod m
  have h1 := h41_succ m
  simp only [st, show h 4 1 (m + 1) % 4 ≠ 3 by omega, show h 4 1 (m + 1) % 8 ≠ 1 by omega,
    ite_false]
  congr 1
  omega

/-- m letters S take h 4 1 m to 1: the odd T-preimages of 2^(2m+1) form one S-chain. -/
theorem st_iter_h41 (m : ℕ) : ∀ a e, st^[m] (h 4 1 m, a, e) = (1, a, e + 2 * m) := by
  induction m with
  | zero => intro a e; simp [h]
  | succ m ih =>
    intro a e
    rw [Function.iterate_succ_apply, st_h41, ih, show e + 2 + 2 * m = e + 2 * (m + 1) by ring]

/-- The offset of the letter power S^(n+1) is the odd T-preimage of 2^(2n+1), A282798(2n+1) + 1:
4^(n+1) y' + tPre (2n+1) = y on y ≡ -1/3 (mod 2^(2n+3)). -/
theorem pow_S_tPre (n : ℕ) : ∀ y m e, (∃ a, 3 * y + 1 = 2 ^ (2 * n + 3) * a) →
    ∃ y', st^[n + 1] (y, m, e) = (y', m, e + 2 * (n + 1)) ∧
      4 ^ (n + 1) * y' + Rule505.tPre (2 * n + 1) = y := by
  rw [tPre_odd_eq]; exact A349414Run.pow_S n

end A349414Pre
