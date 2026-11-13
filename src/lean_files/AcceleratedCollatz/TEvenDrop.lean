-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TDrop
import AcceleratedCollatz.TRhoBound

/-!
  The even case (B41, 13 Nov 2026; paper 3, Ch. 4, "With the zeros kept"). Let x have the
  admissible word s of Order n >= 2, length L, with n <= 3x. If the value T^L(x) is even,
  then T^(L+1)(x) < x: from rho s < n 3^(n-1) <= x 3^n < x 2^L, so 2^L T^L(x) =
  3^n x + rho s < 2^(L+1) x. So, counted by Order, the drop of x can come later than its
  word only when the value at the end of the word is odd.
-/

namespace AcceleratedCollatz

/-- rho s < x 2^|s| for an admissible word s of Order n >= 2 and n <= 3x. -/
theorem rho_lt_mul_two_pow (s : List Bool) (x : ℕ) (hA : Admissible s) (h2 : 2 ≤ order s)
    (hx : order s ≤ 3 * x) : rho s < x * 2 ^ s.length := by
  have hρ := rho_lt_of_admissible s hA h2
  have hd : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have h3 : 3 ^ order s = 3 * 3 ^ (order s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  calc rho s < order s * 3 ^ (order s - 1) := hρ
    _ ≤ 3 * x * 3 ^ (order s - 1) := Nat.mul_le_mul_right _ hx
    _ = x * 3 ^ order s := by rw [h3]; ring
    _ ≤ x * 2 ^ s.length := Nat.mul_le_mul_left _ hd.le

/-- The value at the end of the word is below 2x. -/
theorem tStep_iterate_lt_two_mul (s : List Bool) (x : ℕ) (hA : Admissible s)
    (h2 : 2 ≤ order s) (hs : tBits x s.length = s) (hx : order s ≤ 3 * x) :
    tStep^[s.length] x < 2 * x := by
  have hN := tStep_iterate_nForm s.length x
  rw [hs] at hN
  have hρ := rho_lt_mul_two_pow s x hA h2 hx
  have hd : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have hle : 3 ^ order s * x ≤ 2 ^ s.length * x := Nat.mul_le_mul_right x hd.le
  have hlt : 2 ^ s.length * tStep^[s.length] x < 2 ^ s.length * (2 * x) := by
    rw [hN]
    calc 3 ^ order s * x + rho s < 2 ^ s.length * x + x * 2 ^ s.length := by omega
      _ = 2 ^ s.length * (2 * x) := by ring
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- The even case: if T^|s|(x) is even, then x drops one step later, T^(|s|+1)(x) < x. -/
theorem drop_succ_of_even (s : List Bool) (x : ℕ) (hA : Admissible s) (h2 : 2 ≤ order s)
    (hs : tBits x s.length = s) (hx : order s ≤ 3 * x) (he : tStep^[s.length] x % 2 = 0) :
    tStep^[s.length + 1] x < x := by
  have hy := tStep_iterate_lt_two_mul s x hA h2 hs hx
  rw [Function.iterate_succ_apply']
  generalize tStep^[s.length] x = y at hy he
  have ht : tStep y = y / 2 := by
    unfold tStep
    simp [he]
  rw [ht]
  omega

end AcceleratedCollatz
