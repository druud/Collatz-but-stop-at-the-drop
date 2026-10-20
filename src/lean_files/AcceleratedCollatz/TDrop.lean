-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TParity

/-!
  Drop behaviour of x along its own parity sequence s (standard map T).
  Admissible s: no drop at any 1 ≤ m < |s|. At m = |s|, with
  d_23 s = 2^|s| - 3^(order s): drop iff rho s < d_23 s * x, fixed point iff
  rho s = d_23 s * x.
-/

namespace AcceleratedCollatz

variable (s : List Bool) (x : ℕ)

/-- Product times 2^length is 3^Order. -/
theorem seqProduct_mul_pow (l : List Bool) :
    seqProduct l * (2 : ℚ) ^ l.length = (3 : ℚ) ^ order l := by
  rw [seqProduct_eq]
  exact seqProduct_combine_mul _ _ (order_le_length l)

/-- Product > 1 iff 2^length < 3^Order. -/
theorem one_lt_seqProduct_iff (l : List Bool) :
    1 < seqProduct l ↔ 2 ^ l.length < 3 ^ order l := by
  have h := seqProduct_mul_pow l
  have hpos : (0 : ℚ) < (2 : ℚ) ^ l.length := by positivity
  constructor
  · intro h1
    have h2 := mul_lt_mul_of_pos_right h1 hpos
    rw [one_mul, h] at h2
    exact_mod_cast h2
  · intro h2
    have h2q : (2 : ℚ) ^ l.length < (3 : ℚ) ^ order l := by exact_mod_cast h2
    rw [← h] at h2q
    apply lt_of_mul_lt_mul_right _ hpos.le
    rwa [one_mul]

/-- Product < 1 iff 3^Order < 2^length. -/
theorem seqProduct_lt_one_iff (l : List Bool) :
    seqProduct l < 1 ↔ 3 ^ order l < 2 ^ l.length := by
  have h := seqProduct_mul_pow l
  have hpos : (0 : ℚ) < (2 : ℚ) ^ l.length := by positivity
  constructor
  · intro h1
    have h2 := mul_lt_mul_of_pos_right h1 hpos
    rw [one_mul, h] at h2
    exact_mod_cast h2
  · intro h2
    have h2q : (3 : ℚ) ^ order l < (2 : ℚ) ^ l.length := by exact_mod_cast h2
    rw [← h] at h2q
    apply lt_of_mul_lt_mul_right _ hpos.le
    rwa [one_mul]

/-- 2^m < 3^o on x's first m bits gives T^m(x) > x. -/
theorem lt_iterate_of_pow_lt (x m : ℕ) (hx : 0 < x)
    (h : 2 ^ m < 3 ^ order (tBits x m)) : x < tStep^[m] x := by
  have hN := tStep_iterate_nForm m x
  have hlt : 2 ^ m * x < 2 ^ m * tStep^[m] x := by
    rw [hN]
    calc 2 ^ m * x < 3 ^ order (tBits x m) * x := Nat.mul_lt_mul_of_pos_right h hx
      _ ≤ 3 ^ order (tBits x m) * x + rho (tBits x m) := Nat.le_add_right _ _
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- No drop before |s| along an admissible parity sequence. -/
theorem no_drop_before (hA : Admissible s)
    (hs : tBits x s.length = s) (hx : 0 < x) (m : ℕ) (hm1 : 1 ≤ m) (hm : m < s.length) :
    x < tStep^[m] x := by
  apply lt_iterate_of_pow_lt x m hx
  have hp := hA.prefix_gt m hm1 hm
  rw [one_lt_seqProduct_iff] at hp
  have htake : s.take m = tBits x m := by
    rw [← hs]
    exact tBits_take x s.length m hm.le
  rw [htake, length_tBits] at hp
  exact hp

theorem drop_iff (hs : tBits x s.length = s) :
    tStep^[s.length] x < x ↔ 3 ^ order s * x + rho s < 2 ^ s.length * x := by
  have hN := tStep_iterate_nForm s.length x
  rw [hs] at hN
  rw [← hN]
  exact (Nat.mul_lt_mul_left (by positivity)).symm

theorem fixed_iff (hs : tBits x s.length = s) :
    tStep^[s.length] x = x ↔ 3 ^ order s * x + rho s = 2 ^ s.length * x := by
  have hN := tStep_iterate_nForm s.length x
  rw [hs] at hN
  rw [← hN]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h

/-- Drop at |s| iff rho s < d_23 s * x. -/
theorem drop_iff_rho (hA : Admissible s)
    (hs : tBits x s.length = s) :
    tStep^[s.length] x < x ↔ rho s < d_23 s * x := by
  have hd : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have hle : 3 ^ order s * x ≤ 2 ^ s.length * x := Nat.mul_le_mul_right x hd.le
  rw [drop_iff s x hs, Nat.sub_mul]
  omega

/-- Fixed point at |s| iff rho s = d_23 s * x (cycle point of s). -/
theorem fixed_iff_rho (hA : Admissible s)
    (hs : tBits x s.length = s) :
    tStep^[s.length] x = x ↔ rho s = d_23 s * x := by
  have hd : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have hle : 3 ^ order s * x ≤ 2 ^ s.length * x := Nat.mul_le_mul_right x hd.le
  rw [fixed_iff s x hs, Nat.sub_mul]
  omega

/-- Class conditions: admissible s, x > 0 has parity bits s, rho s < d_23 s * x. -/
structure ClassCond (s : List Bool) (x : ℕ) : Prop where
  adm : Admissible s
  bits : tBits x s.length = s
  pos : 0 < x
  drop : rho s < d_23 s * x

/-- First drop exactly at |s| under the class conditions. -/
theorem first_drop_at_length (h : ClassCond s x) :
    (∀ m, 1 ≤ m → m < s.length → x < tStep^[m] x) ∧ tStep^[s.length] x < x :=
  ⟨no_drop_before s x h.adm h.bits h.pos, (drop_iff_rho s x h.adm h.bits).mpr h.drop⟩

end AcceleratedCollatz
