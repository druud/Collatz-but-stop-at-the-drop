-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TParity

/-!
  B109, the direct route of z and 2z + 1. With x on the path of z and y on
  that of 2z + 1: y = 2x + 1 persists while x is odd (`tStep_two_mul_add_one`).
  If z's word starts 1^a 0 1 (x_a = 2u, u odd), then y_(a+2) = 2 x_(a+2)
  (`pair_link`), so from then on y runs one step behind x
  (`pair_link_behind`), and after each later letter 0 of z, at step n + 1,
  T^(n+1)(2z + 1) = 2 T^(n+1)(z) (`pair_link_double`): at the drop of z both
  have the same odd part.
-/

namespace AcceleratedCollatz

theorem tStep_two_mul_add_one (x : ℕ) (h : x % 2 = 1) :
    tStep (2 * x + 1) = 2 * tStep x + 1 := by
  rw [tStep_odd x h, tStep_odd (2 * x + 1) (by omega)]
  omega

theorem tStep_two_mul (v : ℕ) : tStep (2 * v) = v := by
  rw [tStep_even (2 * v) (by omega)]
  omega

/-- While z's letters are 1, the path of 2z + 1 is y = 2x + 1. -/
theorem pair_ones (z a : ℕ) (h : ∀ j < a, tStep^[j] z % 2 = 1) :
    tStep^[a] (2 * z + 1) = 2 * tStep^[a] z + 1 := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun j hj => h j (by omega))]
    exact tStep_two_mul_add_one _ (h a (by omega))

/-- Word 1^a 0 1 ...: at step a + 2 the path of 2z + 1 is twice that of z. -/
theorem pair_link (z a : ℕ) (h : ∀ j < a, tStep^[j] z % 2 = 1)
    (h0 : tStep^[a] z % 2 = 0) (h1 : tStep^[a + 1] z % 2 = 1) :
    tStep^[a + 2] (2 * z + 1) = 2 * tStep^[a + 2] z := by
  have hy := pair_ones z a h
  set x := tStep^[a] z with hx
  have hu : tStep x = x / 2 := tStep_even x (by omega)
  have h1' : (x / 2) % 2 = 1 := by
    rw [Function.iterate_succ_apply', ← hx, hu] at h1
    exact h1
  have e1 : tStep^[a + 2] z = (3 * (x / 2) + 1) / 2 := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← hx, hu,
      tStep_odd _ h1']
  have e2 : tStep^[a + 2] (2 * z + 1) = 3 * (x / 2) + 1 := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hy,
      tStep_odd (2 * x + 1) (by omega),
      tStep_even _ (by omega)]
    omega
  rw [e1, e2]
  omega

/-- After the link, 2z + 1 runs one step behind z. -/
theorem pair_link_behind (z a n : ℕ) (h : ∀ j < a, tStep^[j] z % 2 = 1)
    (h0 : tStep^[a] z % 2 = 0) (h1 : tStep^[a + 1] z % 2 = 1) (hn : a + 2 ≤ n) :
    tStep^[n + 1] (2 * z + 1) = tStep^[n] z := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show a + 2 + k + 1 = k + 1 + (a + 2) by omega, Function.iterate_add_apply,
    pair_link z a h h0 h1, Function.iterate_succ_apply, tStep_two_mul,
    ← Function.iterate_add_apply, show k + (a + 2) = a + 2 + k by omega]

/-- If z's letter n (n ≥ a + 2) is 0, then T^(n+1)(2z + 1) = 2 T^(n+1)(z):
  at the drop d = n + 1 of z (its last letter is 0) the same odd part. -/
theorem pair_link_double (z a n : ℕ) (h : ∀ j < a, tStep^[j] z % 2 = 1)
    (h0 : tStep^[a] z % 2 = 0) (h1 : tStep^[a + 1] z % 2 = 1) (hn : a + 2 ≤ n)
    (hz : tStep^[n] z % 2 = 0) :
    tStep^[n + 1] (2 * z + 1) = 2 * tStep^[n + 1] z := by
  rw [pair_link_behind z a n h h0 h1 hn, Function.iterate_succ_apply',
    tStep_even _ (by omega)]
  omega

end AcceleratedCollatz
