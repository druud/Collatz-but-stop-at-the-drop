-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCorrespondence

/-!
  The parity map is an isometry, level by level (C196; zeta paper, proof of Theorem thm:nodrop).

  The first k parity letters of x agree with those of y iff x ≡ y (mod 2^k)
  (`tBits_eq_iff_modEq`), and every word of length k is the parity word of exactly one residue
  below 2^k (`tBits_bijOn`). So the parity map keeps the 2-adic distance on the starts x ≥ 0:
  the first k letters of the words of x and y agree iff 2^k divides y - x
  (`tBits_eq_iff_two_pow_dvd`), so the first letter where they differ is at the 2-adic valuation
  of y - x. The passage to all of Z_2 (the limit over k) is not
  formalized.
-/

namespace AcceleratedCollatz

/-- The first k parity letters agree iff the starts agree mod 2^k. -/
theorem tBits_eq_iff_modEq (x y k : ℕ) : tBits x k = tBits y k ↔ x ≡ y [MOD 2 ^ k] :=
  ⟨modEq_of_tBits_eq x y k, tBits_congr x y k⟩

/-- The same in integers: 2^k divides y - x. -/
theorem tBits_eq_iff_two_pow_dvd (x y k : ℕ) :
    tBits x k = tBits y k ↔ (2 ^ k : ℤ) ∣ (y : ℤ) - x := by
  rw [tBits_eq_iff_modEq, Nat.modEq_iff_dvd]
  push_cast; rfl

/-- The residues below 2^k and the words of length k correspond one to one. -/
theorem tBits_bijOn (k : ℕ) :
    Set.BijOn (fun x => tBits x k) (Set.Iio (2 ^ k)) {s : List Bool | s.length = k} := by
  refine ⟨fun x _ => length_tBits x k, fun x hx y hy h => eq_of_tBits_eq x y k hx hy h,
    fun s hs => ?_⟩
  obtain ⟨x, hx, he⟩ := exists_tBits_eq s
  rw [Set.mem_ofPred_eq] at hs
  subst hs
  exact ⟨x, hx, he⟩

end AcceleratedCollatz
