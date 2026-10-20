-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCorrespondence

/-!
  Width Identity (conj:width; Terras 1976, Conjecture 2.9) in T-form, and its
  reduction to class ids. Admissible (tBits x n) says n is x's coefficient
  stopping time; `no_drop_before` gives no drop before n. The identity says
  x drops at n. It holds iff every admissible s whose class id is > 1 drops
  at its class id (`widthIdentity_iff_classDrops`).
-/

namespace AcceleratedCollatz

/-- conj:width: x > 1 drops at its coefficient stopping time. -/
def WidthIdentity : Prop :=
  ∀ x n, 1 < x → Admissible (tBits x n) → tStep^[n] x < x

/-- Every admissible s with class id > 1 drops at its class id. -/
def ClassDrops : Prop :=
  ∀ s, Admissible s → 1 < classId s → rho s < d_23 s * classId s

theorem p2_of_zero : p2_of 0 = 1 := by
  simp [p2_of]

theorem p2_of_one : p2_of 1 = 2 := by
  have h : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  simp [p2_of, h]

/-- Orders 0 and 1: x > 1 drops at its coefficient stopping time. -/
theorem drop_of_order_le_one (x n : ℕ) (hx : 1 < x) (hA : Admissible (tBits x n))
    (ho : order (tBits x n) ≤ 1) : tStep^[n] x < x := by
  have hlen := admissible_length _ hA
  rw [length_tBits] at hlen
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ho with h0 | h1
  · rw [h0, p2_of_zero] at hlen
    subst hlen
    have heven : x % 2 ≠ 1 := by
      intro hodd
      simp [tBits, order, hodd] at h0
    simp only [Function.iterate_one]
    rw [tStep_even x heven]
    omega
  · rw [h1, p2_of_one] at hlen
    subst hlen
    have hl2 : 1 < (tBits x 2).length := by
      rw [length_tBits]
      omega
    have hp := hA.prefix_gt 1 le_rfl hl2
    rw [one_lt_seqProduct_iff, tBits_take x 2 1 (by omega)] at hp
    have hodd : x % 2 = 1 := by
      by_contra hne
      simp [tBits, order, hne] at hp
    have heven : tStep x % 2 ≠ 1 := by
      intro hTodd
      rw [tStep_odd x hodd] at hTodd
      simp [tBits, order, hodd, hTodd] at h1
    rw [Function.iterate_succ_apply', Function.iterate_one, tStep_even _ heven,
      tStep_odd x hodd]
    omega

/-- The class id of an admissible s of order ≥ 2 is > 1. -/
theorem one_lt_classId (s : List Bool) (hA : Admissible s) (hord : 2 ≤ order s) :
    1 < classId s := by
  have hodd := odd_of_class s (classId s) hA (by omega) (tBits_classId s)
  have h32 : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have hlen : 2 < s.length := by
    by_contra hle
    have h9 : 3 ^ 2 ≤ 3 ^ order s := Nat.pow_le_pow_right (by norm_num) hord
    have h4 : 2 ^ s.length ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_contra hle
  have h1 : classId s = 1 := by omega
  have hp := hA.prefix_gt 2 (by norm_num) hlen
  rw [one_lt_seqProduct_iff] at hp
  have htake : s.take 2 = tBits (classId s) 2 := by
    conv_lhs => rw [← tBits_classId s]
    exact tBits_take _ s.length 2 hlen.le
  rw [htake, h1] at hp
  have hb : tBits 1 2 = [true, false] := by
    decide
  rw [hb] at hp
  simp [order] at hp

theorem widthIdentity_iff_classDrops : WidthIdentity ↔ ClassDrops := by
  constructor
  · intro hW s hA hx1
    have hs := tBits_classId s
    have hAs : Admissible (tBits (classId s) s.length) := by
      rw [hs]
      exact hA
    have hdrop := hW (classId s) s.length hx1 hAs
    exact (drop_iff_rho s (classId s) hA hs).mp hdrop
  · intro hC x n hx hA
    by_cases ho : order (tBits x n) ≤ 1
    · exact drop_of_order_le_one x n hx hA ho
    · have hlen : (tBits x n).length = n := length_tBits x n
      have hs : tBits x (tBits x n).length = tBits x n := by
        rw [hlen]
      have hcs : tBits (classId (tBits x n)) (tBits x n).length = tBits x n :=
        tBits_classId _
      have hcle : classId (tBits x n) ≤ x := classId_le_of _ x (by omega) hs
      have hcm : classId (tBits x n) ≡ x [MOD 2 ^ n] := by
        apply modEq_of_tBits_eq
        have h1 := hcs
        rw [hlen] at h1
        exact h1
      obtain ⟨i, hi⟩ := (Nat.modEq_iff_dvd' hcle).mp hcm
      have hd := hC (tBits x n) hA (one_lt_classId _ hA (by omega))
      have hshift := (class_shift (tBits x n) (classId (tBits x n)) i n
        (by rw [hlen]) hcs hd).2
      have hx_eq : classId (tBits x n) + i * 2 ^ n = x := by
        rw [Nat.mul_comm, ← hi]
        omega
      rw [hx_eq] at hshift
      have hdrop := (drop_iff_rho (tBits x n) x hA hs).mpr hshift
      rw [hlen] at hdrop
      exact hdrop

end AcceleratedCollatz
