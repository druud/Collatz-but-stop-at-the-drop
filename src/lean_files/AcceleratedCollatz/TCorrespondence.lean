-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TClass
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ModEq

/-!
  Correspondence of sec:sorting: for each order p3, admissible sequences of
  order p3 correspond bijectively to class ids, the least positive residues
  0 < x ≤ 2^(p2 p3) whose first p2 T-parity bits are admissible of order p3
  (`classEquiv`).
  A class id with rho < d_23 x is determined by its marked vector
  (`classId_eq_of_markedVector_eq`).
-/

namespace AcceleratedCollatz

variable (s : List Bool)

theorem tBits_congr (x y n : ℕ) (h : x ≡ y [MOD 2 ^ n]) : tBits x n = tBits y n := by
  have hx : tBits x (tBits x n).length = tBits x n := by
    rw [length_tBits]
  have hdx := (tBits_eq_iff (tBits x n) x).mp hx
  have hy : 2 ^ (tBits x n).length ∣ 3 ^ order (tBits x n) * y + rho (tBits x n) := by
    rw [length_tBits] at hdx ⊢
    have hmx : 3 ^ order (tBits x n) * x + rho (tBits x n) ≡ 0 [MOD 2 ^ n] :=
      Nat.modEq_zero_iff_dvd.mpr hdx
    have hmy : 3 ^ order (tBits x n) * y + rho (tBits x n) ≡ 0 [MOD 2 ^ n] :=
      ((h.symm.mul_left _).add_right _).trans hmx
    exact Nat.modEq_zero_iff_dvd.mp hmy
  have hyeq := (tBits_eq_iff (tBits x n) y).mpr hy
  rw [length_tBits] at hyeq
  exact hyeq.symm

theorem tBits_mod (x n : ℕ) : tBits (x % 2 ^ n) n = tBits x n :=
  tBits_congr _ _ _ (Nat.mod_modEq x _)

theorem modEq_of_tBits_eq (x y n : ℕ) (h : tBits x n = tBits y n) : x ≡ y [MOD 2 ^ n] := by
  have hx : tBits x (tBits x n).length = tBits x n := by
    rw [length_tBits]
  have hy : tBits y (tBits x n).length = tBits x n := by
    rw [length_tBits, h]
  have hdx := (tBits_eq_iff (tBits x n) x).mp hx
  have hdy := (tBits_eq_iff (tBits x n) y).mp hy
  rw [length_tBits] at hdx hdy
  have hm : 3 ^ order (tBits x n) * x + rho (tBits x n) ≡
      3 ^ order (tBits x n) * y + rho (tBits x n) [MOD 2 ^ n] :=
    (Nat.modEq_zero_iff_dvd.mpr hdx).trans (Nat.modEq_zero_iff_dvd.mpr hdy).symm
  have hcop : Nat.gcd (2 ^ n) (3 ^ order (tBits x n)) = 1 :=
    Nat.Coprime.pow n _ (by decide)
  exact Nat.ModEq.cancel_left_of_coprime hcop (Nat.ModEq.add_right_cancel' _ hm)

theorem eq_of_tBits_eq (x y n : ℕ) (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : tBits x n = tBits y n) : x = y :=
  Nat.ModEq.eq_of_lt_of_lt (modEq_of_tBits_eq x y n h) hx hy

/-- Every bit string is the parity sequence of some residue mod 2^|s|. -/
theorem exists_tBits_eq : ∃ x, x < 2 ^ s.length ∧ tBits x s.length = s := by
  have hcop : Nat.Coprime (3 ^ order s) (2 ^ s.length) := Nat.Coprime.pow _ _ (by decide)
  have hk : 2 ^ s.length ≠ 0 := by positivity
  obtain ⟨m, _, hm⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (rho s * (2 ^ s.length - 1)) hcop hk
  have hmod : 3 ^ order s * m ≡ rho s * (2 ^ s.length - 1) [MOD 2 ^ s.length] := hm
  have hsum : rho s * (2 ^ s.length - 1) + rho s = rho s * 2 ^ s.length := by
    have h1 : 1 ≤ 2 ^ s.length := Nat.one_le_two_pow
    rw [Nat.mul_sub, Nat.mul_one]
    have h2 : rho s ≤ rho s * 2 ^ s.length := Nat.le_mul_of_pos_right _ h1
    omega
  have hzero : 3 ^ order s * m + rho s ≡ 0 [MOD 2 ^ s.length] := by
    have h1 := hmod.add_right (rho s)
    rw [hsum] at h1
    exact h1.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _))
  have hbits : tBits m s.length = s :=
    (tBits_eq_iff s m).mpr (Nat.modEq_zero_iff_dvd.mp hzero)
  refine ⟨m % 2 ^ s.length, Nat.mod_lt _ (by positivity), ?_⟩
  rw [tBits_mod, hbits]

/-- Positive version of `eq_of_tBits_eq`: residues in (0, 2^n]. -/
theorem eq_of_tBits_eq_pos (x y n : ℕ) (hx0 : 0 < x) (hy0 : 0 < y) (hx : x ≤ 2 ^ n)
    (hy : y ≤ 2 ^ n) (h : tBits x n = tBits y n) : x = y := by
  have hm := modEq_of_tBits_eq x y n h
  have hx' : x - 1 + 1 = x := by omega
  have hy' : y - 1 + 1 = y := by omega
  rw [← hx', ← hy'] at hm
  have h1 := Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' 1 hm) (by omega) (by omega)
  omega

theorem exists_pos_tBits_eq :
    ∃ x, 0 < x ∧ x ≤ 2 ^ s.length ∧ tBits x s.length = s := by
  obtain ⟨m, hm, hbits⟩ := exists_tBits_eq s
  by_cases hm0 : m = 0
  · refine ⟨2 ^ s.length, by positivity, le_rfl, ?_⟩
    rw [← tBits_mod, Nat.mod_self, ← hm0, hbits]
  · exact ⟨m, by omega, hm.le, hbits⟩

/-- Class id of s: the least positive x with parity sequence s; 0 < x ≤ 2^|s|. -/
def classId (s : List Bool) : ℕ :=
  Nat.find (p := fun x => 0 < x ∧ tBits x s.length = s)
    (by
      obtain ⟨x, hx0, _, hs⟩ := exists_pos_tBits_eq s
      exact ⟨x, hx0, hs⟩)

theorem classId_pos : 0 < classId s :=
  (Nat.find_spec (p := fun x => 0 < x ∧ tBits x s.length = s) _).1

theorem tBits_classId : tBits (classId s) s.length = s :=
  (Nat.find_spec (p := fun x => 0 < x ∧ tBits x s.length = s) _).2

/-- classId s is at most every positive x with parity sequence s. -/
theorem classId_le_of (x : ℕ) (hx0 : 0 < x) (hs : tBits x s.length = s) :
    classId s ≤ x :=
  Nat.find_min' (p := fun x => 0 < x ∧ tBits x s.length = s) _ ⟨hx0, hs⟩

theorem classId_le : classId s ≤ 2 ^ s.length := by
  obtain ⟨x, hx0, hx, hs⟩ := exists_pos_tBits_eq s
  exact (classId_le_of s x hx0 hs).trans hx

theorem classId_unique (x : ℕ) (hx0 : 0 < x) (hx : x ≤ 2 ^ s.length)
    (hs : tBits x s.length = s) : x = classId s :=
  eq_of_tBits_eq_pos x (classId s) s.length hx0 (classId_pos s) hx (classId_le s)
    (by rw [hs, tBits_classId])

/-- Class ids of order p3: least positive residues mod 2^(p2 p3) with admissible parity
    bits of order p3. -/
structure IsClassId (p3 x : ℕ) : Prop where
  /-- x is positive. -/
  pos : 0 < x
  /-- x is at most 2^p2. -/
  le : x ≤ 2 ^ p2_of p3
  /-- The first p2 parity bits of x are admissible. -/
  adm : Admissible (tBits x (p2_of p3))
  /-- The first p2 parity bits of x have Order p3. -/
  order_eq : order (tBits x (p2_of p3)) = p3

theorem isClassId_classId (p3 : ℕ) (s : List Bool) (hA : Admissible s) (hord : order s = p3) :
    IsClassId p3 (classId s) := by
  have hlen : s.length = p2_of p3 := by
    rw [← hord]
    exact admissible_length s hA
  refine ⟨classId_pos s, ?_, ?_, ?_⟩
  · rw [← hlen]
    exact classId_le s
  · rw [← hlen, tBits_classId]
    exact hA
  · rw [← hlen, tBits_classId]
    exact hord

theorem classId_tBits (p3 x : ℕ) (hx : IsClassId p3 x) :
    classId (tBits x (p2_of p3)) = x := by
  have hlen : (tBits x (p2_of p3)).length = p2_of p3 := length_tBits x _
  symm
  apply classId_unique _ _ hx.pos
  · rw [hlen]
    exact hx.le
  · rw [hlen]

/-- Admissible sequences of order p3 ≃ class ids of order p3. -/
def classEquiv (p3 : ℕ) :
    {s : List Bool // Admissible s ∧ order s = p3} ≃ {x : ℕ // IsClassId p3 x} where
  toFun s := ⟨classId s.1, isClassId_classId p3 s.1 s.2.1 s.2.2⟩
  invFun x := ⟨tBits x.1 (p2_of p3), x.2.adm, x.2.order_eq⟩
  left_inv s := by
    obtain ⟨s, hA, hord⟩ := s
    have hlen : s.length = p2_of p3 := by
      rw [← hord]
      exact admissible_length s hA
    apply Subtype.ext
    change tBits (classId s) (p2_of p3) = s
    rw [← hlen, tBits_classId]
  right_inv x := by
    obtain ⟨x, hx⟩ := x
    apply Subtype.ext
    exact classId_tBits p3 x hx

theorem classCond_of_isClassId (p3 x : ℕ) (hx : IsClassId p3 x)
    (hd : rho (tBits x (p2_of p3)) < d_23 (tBits x (p2_of p3)) * x) :
    ClassCond (tBits x (p2_of p3)) x :=
  ⟨hx.adm, by rw [length_tBits], hx.pos, hd⟩

/-- A class id with rho < d_23 x decodes its marked vector to its parity sequence. -/
theorem decodeVector_classId (p3 x : ℕ) (hx : IsClassId p3 x)
    (hd : rho (tBits x (p2_of p3)) < d_23 (tBits x (p2_of p3)) * x) :
    decodeVector (markedVector (p2_of p3) x x) = tBits x (p2_of p3) := by
  have hlen : (tBits x (p2_of p3)).length = p2_of p3 := length_tBits x _
  have hC := classCond_of_isClassId p3 x hx hd
  have hterm := terminates_of_class _ x hC
  rw [hlen] at hterm
  exact decodeVector_eq_of_class _ x (p2_of p3) hC hterm

/-- Class ids (with rho < d_23 x) are determined by their marked vectors. -/
theorem classId_eq_of_markedVector_eq (p3 x y : ℕ) (hx : IsClassId p3 x) (hy : IsClassId p3 y)
    (hxd : rho (tBits x (p2_of p3)) < d_23 (tBits x (p2_of p3)) * x)
    (hyd : rho (tBits y (p2_of p3)) < d_23 (tBits y (p2_of p3)) * y)
    (h : markedVector (p2_of p3) x x = markedVector (p2_of p3) y y) : x = y := by
  have hbits : tBits x (p2_of p3) = tBits y (p2_of p3) := by
    rw [← decodeVector_classId p3 x hx hxd, ← decodeVector_classId p3 y hy hyd, h]
  exact eq_of_tBits_eq_pos x y (p2_of p3) hx.pos hy.pos hx.le hy.le hbits

end AcceleratedCollatz
