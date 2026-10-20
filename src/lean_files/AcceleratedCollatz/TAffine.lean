-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCorrespondence

/-!
  sec:dropformula (affine class lemma). T-form: shifting x by i 2^Q
  (Q ≥ n) shifts T^n(x) by i 3^o 2^(Q-n), o the order of x's first n bits.
  R-form: for x satisfying the class conditions, the drop value is
  T^|s|(x), so D(x + i 2^|s|) = D(x) + i 3^(order s); in particular for
  x = classId s (x_init) and D(x_init) = x_drop.
-/

namespace AcceleratedCollatz

theorem tStep_iterate_shift (x i Q n : ℕ) (hQ : n ≤ Q) :
    tStep^[n] (x + i * 2 ^ Q) = tStep^[n] x + i * 3 ^ order (tBits x n) * 2 ^ (Q - n) := by
  have hmod : x + i * 2 ^ Q ≡ x [MOD 2 ^ n] := by
    have h0 : i * 2 ^ Q ≡ 0 [MOD 2 ^ n] :=
      Nat.modEq_zero_iff_dvd.mpr ((pow_dvd_pow 2 hQ).mul_left i)
    simpa using Nat.ModEq.add_left x h0
  have hbits : tBits (x + i * 2 ^ Q) n = tBits x n := tBits_congr _ _ _ hmod
  have h1 := tStep_iterate_nForm n (x + i * 2 ^ Q)
  have h2 := tStep_iterate_nForm n x
  rw [hbits] at h1
  have hpow : 2 ^ n * 2 ^ (Q - n) = 2 ^ Q := by
    rw [← pow_add, Nat.add_sub_cancel' hQ]
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ n)
  calc 2 ^ n * tStep^[n] (x + i * 2 ^ Q)
      = 3 ^ order (tBits x n) * (x + i * 2 ^ Q) + rho (tBits x n) := h1
    _ = (3 ^ order (tBits x n) * x + rho (tBits x n)) +
          i * 3 ^ order (tBits x n) * (2 ^ n * 2 ^ (Q - n)) := by
        rw [hpow]
        ring
    _ = 2 ^ n * (tStep^[n] x + i * 3 ^ order (tBits x n) * 2 ^ (Q - n)) := by
        rw [← h2]
        ring

/-- Drop value under the class conditions: D(x) = T^|s|(x). -/
theorem drop_eq_iterate_of_class (s : List Bool) (x fuel : ℕ) (h : ClassCond s x)
    (hterm : (trajStats x fuel x).2.2 < x) :
    (trajStats x fuel x).2.2 = tStep^[s.length] x := by
  have hx1 := one_lt_of_class s x h
  obtain ⟨_, hb, _⟩ := traceOK_markedVector x hx1 fuel x le_rfl
  rw [decodeVector_eq_of_class s x fuel h hterm] at hb
  exact hb.symm

/-- sec:dropformula: D(x + i 2^|s|) = D(x) + i 3^(order s) under the class conditions. -/
theorem affine_class (s : List Bool) (x i : ℕ) (h : ClassCond s x) :
    (trajStats (x + i * 2 ^ s.length) s.length (x + i * 2 ^ s.length)).2.2 =
      (trajStats x s.length x).2.2 + i * 3 ^ order s := by
  obtain ⟨hs', hd'⟩ := class_shift s x i s.length le_rfl h.bits h.drop
  have hx' : 0 < x + i * 2 ^ s.length := by
    have := h.pos
    omega
  have h' : ClassCond s (x + i * 2 ^ s.length) := ⟨h.adm, hs', hx', hd'⟩
  have hterm := terminates_of_class s x h
  have hterm' := terminates_of_class s _ h'
  rw [drop_eq_iterate_of_class s _ _ h' hterm',
    drop_eq_iterate_of_class s x _ h hterm,
    tStep_iterate_shift x i s.length s.length le_rfl, h.bits, Nat.sub_self, pow_zero, mul_one]

/-- sec:dropformula at the class id: D(x_init + i 2^p2) = x_drop + i 3^p3. -/
theorem affine_classId (s : List Bool) (i : ℕ) (hA : Admissible s)
    (hd : rho s < d_23 s * classId s) :
    (trajStats (classId s + i * 2 ^ s.length) s.length (classId s + i * 2 ^ s.length)).2.2 =
      (trajStats (classId s) s.length (classId s)).2.2 + i * 3 ^ order s :=
  affine_class s (classId s) i ⟨hA, tBits_classId s, classId_pos s, hd⟩

end AcceleratedCollatz
