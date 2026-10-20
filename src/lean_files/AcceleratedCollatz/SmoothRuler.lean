-- SPDX-License-Identifier: MIT
/-
  SmoothRuler.lean

  The 3-smooth numbers 2^j 3^i on a plain ruler: a number v is drawn at distance v from the
  left, in row i (its number of factors 3), rows equally far apart, row 0 on top.

  1. `line_falls_short`: for a < b the straight line from a through b, continued over the
     same number of rows, arrives at 2b - a, before the place b^2 / a of a second step
     with the same factor.
  2. `RulerGap`, an open statement: when a and b are neighbours among the 3-smooth numbers,
     no 3-smooth number lies after 2b - a and before b^2 / a. `RulerGapUpTo J I` is the same
     for exponents of 2 up to J and exponents of 3 up to I.
  3. `rule_iff_of_rulerGap`: under `RulerGap` a 3-smooth number lies before the second step
     exactly when it lies at or before the end 2b - a of the line.
  4. The statement on exponents only. A step raises one exponent by P and lowers the other
     by β (`StepAt`: no number that fits lies before its end); a number in the gap raises
     the second exponent by v and lowers the first by u (`GapAt`), with more factors than
     the start of the step has: j < u ≤ j + P (`frame_gap`). `OrdersGapFrame 2 3` is the
     statement for the steps to fewer factors 3, `OrdersGapFrame 3 2` for the steps to more
     factors 3; `rulerGapUpTo_of_ordersGapFrame` for bounded exponents, `frame_fail` for the
     way back, and `rulerGap_iff_ordersGap`: `RulerGap` is the statement on exponents.
  5. `border_rule_fails`: the rule "a 3-smooth number before the place where the continued
     line meets row 0 is a number that a second step of the same factor skips" is false.
     The step 3^11 -> 2^8 3^6 goes 5 rows up and ends in row 6; its line meets row 0 at
     197996 + 2/5; the second step of that factor lands at 2^16 3, before that place, and
     no 3-smooth number lies between 2^8 3^6 and 2^16 3.

  Mathlib only; the tree imports it through TRulerRecord.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

namespace SmoothRuler

/-- A number of the form 2^j 3^i. -/
def IsSmooth (v : ℕ) : Prop := ∃ j i : ℕ, v = 2 ^ j * 3 ^ i

/-- No number p^x q^y lies strictly between lo and hi. -/
def NoneBetweenPQ (p q lo hi : ℕ) : Prop :=
  ∀ x y : ℕ, ¬(lo < p ^ x * q ^ y ∧ p ^ x * q ^ y < hi)

/-- No 3-smooth number lies strictly between lo and hi. -/
def NoneBetween (lo hi : ℕ) : Prop := NoneBetweenPQ 2 3 lo hi

/-- For neighbours a < b among the 3-smooth numbers, no 3-smooth number n has
    2b - a < n < b^2 / a. -/
def RulerGap : Prop :=
  ∀ a b n : ℕ, IsSmooth a → IsSmooth b → IsSmooth n → a < b → NoneBetween a b →
    ¬(2 * b < n + a ∧ n * a < b * b)

/-- `RulerGap` for a = 2^j 3^i, b = 2^j' 3^i', n = 2^x 3^y with j, j', x ≤ J and
    i, i', y ≤ I. -/
def RulerGapUpTo (J I : ℕ) : Prop :=
  ∀ j i j' i' x y : ℕ, j ≤ J → j' ≤ J → x ≤ J → i ≤ I → i' ≤ I → y ≤ I →
    2 ^ j * 3 ^ i < 2 ^ j' * 3 ^ i' → NoneBetween (2 ^ j * 3 ^ i) (2 ^ j' * 3 ^ i') →
    ¬(2 * (2 ^ j' * 3 ^ i') < 2 ^ x * 3 ^ y + 2 ^ j * 3 ^ i ∧
      2 ^ x * 3 ^ y * (2 ^ j * 3 ^ i) < 2 ^ j' * 3 ^ i' * (2 ^ j' * 3 ^ i'))

/-- A step with factor p^P / q^β from a number with exponent j of p: it goes up; no step
    with β' ≤ β goes up by less; and no step q^v' / p^u' that fits (u' ≤ j) goes up
    by less. -/
def StepAt (p q P β j : ℕ) : Prop :=
  q ^ β < p ^ P ∧
  (∀ P' β' : ℕ, β' ≤ β → q ^ β' < p ^ P' → p ^ P * q ^ β' ≤ p ^ P' * q ^ β) ∧
  (∀ u' v' : ℕ, u' ≤ j → p ^ u' < q ^ v' → p ^ (P + u') ≤ q ^ (v' + β))

/-- The factor s = q^v / p^u lies in the gap of the step with factor r = p^P / q^β:
    1 < s, s < r and 2 - 1/r < s. -/
def GapAt (p q P β u v : ℕ) : Prop :=
  p ^ u < q ^ v ∧ q ^ (v + β) < p ^ (P + u) ∧ 2 * p ^ (P + u) < p ^ P * q ^ v + p ^ u * q ^ β

/-- For the steps p^P / q^β with P ≤ M and β ≤ N: no factor q^v / p^u with u ≤ M and
    v ≤ N that fits after the step and not before it (j < u ≤ j + P) lies in the gap. -/
def OrdersGapFrame (p q M N : ℕ) : Prop :=
  ∀ P β u v j : ℕ, P ≤ M → u ≤ M → β ≤ N → v ≤ N → StepAt p q P β j → j < u → u ≤ j + P →
    ¬GapAt p q P β u v

/-- The statement on exponents, for both kinds of step and without bounds. -/
def OrdersGap : Prop := (∀ M N, OrdersGapFrame 2 3 M N) ∧ (∀ M N, OrdersGapFrame 3 2 M N)

/-- For a < b the continued line arrives at 2b - a, and (2b - a) a < b^2: it arrives
    before the second step with the factor b / a. -/
theorem line_falls_short {a b : ℕ} (h : a < b) : (2 * b - a) * a < b * b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  have h2 : 2 * (a + d + 1) - a = a + 2 * d + 2 := by
    omega
  have h3 : (a + d + 1) * (a + d + 1) = (a + 2 * d + 2) * a + (d + 1) * (d + 1) := by
    ring
  rw [h2, h3]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos d))

/-- Under `RulerGap`, for neighbours a < b: a 3-smooth number n lies before the second
    step, n a < b^2, exactly when it lies at or before the end of the line, n ≤ 2b - a. -/
theorem rule_iff_of_rulerGap (h : RulerGap) {a b n : ℕ} (ha : IsSmooth a) (hb : IsSmooth b)
    (hn : IsSmooth n) (hab : a < b) (hnb : NoneBetween a b) :
    n * a < b * b ↔ n + a ≤ 2 * b := by
  constructor
  · intro hlt
    by_contra hgt
    push Not at hgt
    exact h a b n ha hb hn hab hnb ⟨hgt, hlt⟩
  · intro hle
    have h1 : n ≤ 2 * b - a := by
      omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right a h1) (line_falls_short hab)

/-- The bases may be named in either order. -/
theorem noneBetweenPQ_swap {p q lo hi : ℕ} (h : NoneBetweenPQ p q lo hi) :
    NoneBetweenPQ q p lo hi := by
  intro x y hxy
  rw [Nat.mul_comm] at hxy
  exact h y x hxy

/-- A step from a = p^j q^(i' + β) to its neighbour b = p^(j + P) q^i', and a number
    n = p^x q^y with 2b - a < n < b^2 / a. Then n = b q^v / p^u with j < u ≤ j + P: the
    factor q^v / p^u fits at b and not at a, and it lies in the gap of the step. -/
theorem frame_gap {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {j i' P β x y : ℕ}
    (hab : p ^ j * q ^ (i' + β) < p ^ (j + P) * q ^ i')
    (hnb : NoneBetweenPQ p q (p ^ j * q ^ (i' + β)) (p ^ (j + P) * q ^ i'))
    (h2 : 2 * (p ^ (j + P) * q ^ i') < p ^ x * q ^ y + p ^ j * q ^ (i' + β))
    (hsk : p ^ x * q ^ y * (p ^ j * q ^ (i' + β)) <
      p ^ (j + P) * q ^ i' * (p ^ (j + P) * q ^ i')) :
    ∃ u v : ℕ, j < u ∧ u ≤ j + P ∧ x + u = j + P ∧ y = i' + v ∧ StepAt p q P β j ∧
      GapAt p q P β u v := by
  have hbn : p ^ (j + P) * q ^ i' < p ^ x * q ^ y := by
    omega
  have hxP : x < P := by
    by_contra hge
    push Not at hge
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
    have he : p ^ k * q ^ (β + y) * (p ^ (j + P) * q ^ i') =
        p ^ (P + k) * q ^ y * (p ^ j * q ^ (i' + β)) := by
      ring
    have h1 : p ^ j * q ^ (i' + β) * (p ^ (j + P) * q ^ i') <
        p ^ k * q ^ (β + y) * (p ^ (j + P) * q ^ i') := by
      rw [he, Nat.mul_comm (p ^ j * q ^ (i' + β))]
      exact Nat.mul_lt_mul_of_pos_right hbn (Nat.mul_pos (Nat.pow_pos hp) (Nat.pow_pos hq))
    have h3 : p ^ k * q ^ (β + y) * (p ^ (j + P) * q ^ i') <
        p ^ (j + P) * q ^ i' * (p ^ (j + P) * q ^ i') := by
      rw [he]
      exact hsk
    exact hnb k (β + y) ⟨Nat.lt_of_mul_lt_mul_right h1, Nat.lt_of_mul_lt_mul_right h3⟩
  obtain ⟨u, hu⟩ : ∃ u, j + P = x + u := ⟨j + P - x, by omega⟩
  have hy : i' < y := by
    by_contra hle
    push Not at hle
    have h1 : p ^ x * q ^ y ≤ p ^ (j + P) * q ^ i' :=
      Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega)) (Nat.pow_le_pow_right hq hle)
    omega
  obtain ⟨v, rfl⟩ : ∃ v, y = i' + v := ⟨y - i', by omega⟩
  have hpow : p ^ (j + P) = p ^ x * p ^ u := by
    rw [hu, pow_add]
  have hpow2 : p ^ (j + P) = p ^ j * p ^ P := pow_add p j P
  have hc : 0 < p ^ j * q ^ i' := Nat.mul_pos (Nat.pow_pos hp) (Nat.pow_pos hq)
  -- the step
  have s1 : q ^ β < p ^ P := by
    have e1 : p ^ j * q ^ (i' + β) = p ^ j * q ^ i' * q ^ β := by
      ring
    have e2 : p ^ (j + P) * q ^ i' = p ^ j * q ^ i' * p ^ P := by
      ring
    rw [e1, e2] at hab
    exact Nat.lt_of_mul_lt_mul_left hab
  have s2 : ∀ P' β' : ℕ, β' ≤ β → q ^ β' < p ^ P' → p ^ P * q ^ β' ≤ p ^ P' * q ^ β := by
    intro P' β' hβ hlt
    by_contra hcon
    push Not at hcon
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hβ
    have e3 : p ^ P' * q ^ (β' + d) = p ^ P' * q ^ d * q ^ β' := by
      ring
    rw [e3] at hcon
    have h4 : p ^ P' * q ^ d < p ^ P := Nat.lt_of_mul_lt_mul_right hcon
    have h5 : p ^ j * q ^ (i' + (β' + d)) < p ^ (j + P') * q ^ (i' + d) := by
      have e4 : p ^ j * q ^ (i' + (β' + d)) = p ^ j * q ^ (i' + d) * q ^ β' := by
        ring
      have e5 : p ^ (j + P') * q ^ (i' + d) = p ^ j * q ^ (i' + d) * p ^ P' := by
        ring
      rw [e4, e5]
      exact Nat.mul_lt_mul_of_pos_left hlt (Nat.mul_pos (Nat.pow_pos hp) (Nat.pow_pos hq))
    have h6 : p ^ (j + P') * q ^ (i' + d) < p ^ (j + P) * q ^ i' := by
      have e6 : p ^ (j + P') * q ^ (i' + d) = p ^ j * q ^ i' * (p ^ P' * q ^ d) := by
        ring
      have e7 : p ^ (j + P) * q ^ i' = p ^ j * q ^ i' * p ^ P := by
        ring
      rw [e6, e7]
      exact Nat.mul_lt_mul_of_pos_left h4 hc
    exact hnb (j + P') (i' + d) ⟨h5, h6⟩
  have s3 : ∀ u' v' : ℕ, u' ≤ j → p ^ u' < q ^ v' → p ^ (P + u') ≤ q ^ (v' + β) := by
    intro u' v' hu' hlt
    by_contra hcon
    push Not at hcon
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hu'
    have h5 : p ^ (u' + k) * q ^ (i' + β) < p ^ k * q ^ (i' + β + v') := by
      have e4 : p ^ (u' + k) * q ^ (i' + β) = p ^ k * q ^ (i' + β) * p ^ u' := by
        ring
      have e5 : p ^ k * q ^ (i' + β + v') = p ^ k * q ^ (i' + β) * q ^ v' := by
        ring
      rw [e4, e5]
      exact Nat.mul_lt_mul_of_pos_left hlt (Nat.mul_pos (Nat.pow_pos hp) (Nat.pow_pos hq))
    have h6 : p ^ k * q ^ (i' + β + v') < p ^ (u' + k + P) * q ^ i' := by
      have e6 : p ^ k * q ^ (i' + β + v') = p ^ k * q ^ i' * q ^ (v' + β) := by
        ring
      have e7 : p ^ (u' + k + P) * q ^ i' = p ^ k * q ^ i' * p ^ (P + u') := by
        ring
      rw [e6, e7]
      exact Nat.mul_lt_mul_of_pos_left hcon (Nat.mul_pos (Nat.pow_pos hp) (Nat.pow_pos hq))
    exact hnb k (i' + β + v') ⟨h5, h6⟩
  -- the gap
  have g1 : p ^ u < q ^ v := by
    have e1 : p ^ (j + P) * q ^ i' = p ^ x * q ^ i' * p ^ u := by
      rw [hpow]
      ring
    have e2 : p ^ x * q ^ (i' + v) = p ^ x * q ^ i' * q ^ v := by
      ring
    rw [e1, e2] at hbn
    exact Nat.lt_of_mul_lt_mul_left hbn
  have g2 : q ^ (v + β) < p ^ (P + u) := by
    have e1 : p ^ x * q ^ (i' + v) * (p ^ j * q ^ (i' + β)) =
        p ^ x * p ^ j * q ^ i' * q ^ i' * q ^ (v + β) := by
      ring
    have e2 : p ^ (j + P) * q ^ i' * (p ^ (j + P) * q ^ i') =
        p ^ x * p ^ j * q ^ i' * q ^ i' * p ^ (P + u) := by
      calc p ^ (j + P) * q ^ i' * (p ^ (j + P) * q ^ i')
          = p ^ x * p ^ u * q ^ i' * (p ^ j * p ^ P * q ^ i') := by
            rw [← hpow, ← hpow2]
        _ = p ^ x * p ^ j * q ^ i' * q ^ i' * p ^ (P + u) := by
            ring
    rw [e1, e2] at hsk
    exact Nat.lt_of_mul_lt_mul_left hsk
  have g3 : 2 * p ^ (P + u) < p ^ P * q ^ v + p ^ u * q ^ β := by
    have h7 := Nat.mul_lt_mul_of_pos_right h2 (Nat.pow_pos hp : 0 < p ^ u)
    have e1 : 2 * (p ^ (j + P) * q ^ i') * p ^ u = p ^ j * q ^ i' * (2 * p ^ (P + u)) := by
      ring
    have e2 : (p ^ x * q ^ (i' + v) + p ^ j * q ^ (i' + β)) * p ^ u =
        p ^ j * q ^ i' * (p ^ P * q ^ v + p ^ u * q ^ β) := by
      calc (p ^ x * q ^ (i' + v) + p ^ j * q ^ (i' + β)) * p ^ u
          = p ^ x * p ^ u * q ^ i' * q ^ v + p ^ j * q ^ i' * (p ^ u * q ^ β) := by
            ring
        _ = p ^ j * p ^ P * q ^ i' * q ^ v + p ^ j * q ^ i' * (p ^ u * q ^ β) := by
            rw [← hpow, hpow2]
        _ = p ^ j * q ^ i' * (p ^ P * q ^ v + p ^ u * q ^ β) := by
            ring
    rw [e1, e2] at h7
    exact Nat.lt_of_mul_lt_mul_left h7
  exact ⟨u, v, by omega, by omega, hu.symm, rfl, ⟨s1, s2, s3⟩, ⟨g1, g2, g3⟩⟩

/-- The statement on exponents, for P, u up to J and β, v up to I in the steps to fewer
    factors 3 and the other way round in the steps to more factors 3, gives `RulerGap` for
    the numbers with exponents of 2 up to J and exponents of 3 up to I. -/
theorem rulerGapUpTo_of_ordersGapFrame {J I : ℕ} (hU : OrdersGapFrame 2 3 J I)
    (hL : OrdersGapFrame 3 2 I J) : RulerGapUpTo J I := by
  intro j i j' i' x y hj hj' hx hi hi' hy hab hnb hf
  obtain ⟨h2, hsk⟩ := hf
  rcases Nat.lt_or_ge j j' with hjj | hjj
  · rcases Nat.lt_or_ge i i' with hii | hii
    · have ht : 0 < 2 ^ j * 3 ^ i :=
        Nat.mul_pos (Nat.pow_pos (by norm_num)) (Nat.pow_pos (by norm_num))
      have e : 2 ^ (j + 1) * 3 ^ i = 2 * (2 ^ j * 3 ^ i) := by
        ring
      have h1 : 2 ^ j * 3 ^ i < 2 ^ (j + 1) * 3 ^ i := by
        omega
      have h3 : 2 ^ (j + 1) * 3 ^ i < 2 ^ j' * 3 ^ i' :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hjj))
          (Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) hii)
            (Nat.pow_pos (by norm_num)))
      exact hnb (j + 1) i ⟨h1, h3⟩
    · obtain ⟨P, rfl⟩ := Nat.exists_eq_add_of_le hjj.le
      obtain ⟨β, rfl⟩ := Nat.exists_eq_add_of_le hii
      obtain ⟨u, v, hju, huP, hxu, rfl, hstep, hgap⟩ :=
        frame_gap (by norm_num) (by norm_num) hab hnb h2 hsk
      exact hU P β u v j (by omega) (by omega) (by omega) (by omega) hstep hju huP hgap
  · rcases Nat.lt_or_ge i i' with hii | hii
    · obtain ⟨P, rfl⟩ := Nat.exists_eq_add_of_le hii.le
      obtain ⟨β, rfl⟩ := Nat.exists_eq_add_of_le hjj
      have e1 : 2 ^ (j' + β) * 3 ^ i = 3 ^ i * 2 ^ (j' + β) := Nat.mul_comm _ _
      have e2 : 2 ^ j' * 3 ^ (i + P) = 3 ^ (i + P) * 2 ^ j' := Nat.mul_comm _ _
      have e3 : 2 ^ x * 3 ^ y = 3 ^ y * 2 ^ x := Nat.mul_comm _ _
      rw [e1, e2] at hab
      rw [e1, e2] at hnb
      rw [e1, e2, e3] at h2
      rw [e1, e2, e3] at hsk
      obtain ⟨u, v, hju, huP, hxu, rfl, hstep, hgap⟩ :=
        frame_gap (by norm_num) (by norm_num) hab (noneBetweenPQ_swap hnb) h2 hsk
      exact hL P β u v i (by omega) (by omega) (by omega) (by omega) hstep hju huP hgap
    · have h1 : 2 ^ j' * 3 ^ i' ≤ 2 ^ j * 3 ^ i :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hjj)
          (Nat.pow_le_pow_right (by norm_num) hii)
      omega

/-- The statement on exponents gives `RulerGap`. -/
theorem rulerGap_of_ordersGap (h : OrdersGap) : RulerGap := by
  intro a b n ha hb hn hab hnb hf
  obtain ⟨j, i, rfl⟩ := ha
  obtain ⟨j', i', rfl⟩ := hb
  obtain ⟨x, y, rfl⟩ := hn
  exact rulerGapUpTo_of_ordersGapFrame (J := j + j' + x) (I := i + i' + y) (h.1 _ _) (h.2 _ _)
    j i j' i' x y (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hab hnb hf

/-- A step that `StepAt` allows and a factor in its gap give numbers: a = p^j q^β and
    b = p^(j + P) are neighbours, and n = p^w q^v, with w + u = j + P, has
    2b - a < n < b^2 / a. -/
theorem frame_fail {p q : ℕ} (hp : 1 < p) (hq : 1 < q) {P β u v j : ℕ}
    (hs : StepAt p q P β j) (huP : u ≤ j + P) (hg : GapAt p q P β u v) :
    ∃ w : ℕ, w + u = j + P ∧ p ^ j * q ^ β < p ^ (j + P) ∧
      NoneBetweenPQ p q (p ^ j * q ^ β) (p ^ (j + P)) ∧
      2 * p ^ (j + P) < p ^ w * q ^ v + p ^ j * q ^ β ∧
      p ^ w * q ^ v * (p ^ j * q ^ β) < p ^ (j + P) * p ^ (j + P) := by
  obtain ⟨s1, s2, s3⟩ := hs
  obtain ⟨_, g2, g3⟩ := hg
  have hp0 : 0 < p := by
    omega
  have hq0 : 0 < q := by
    omega
  obtain ⟨w, hw⟩ : ∃ w, j + P = w + u := ⟨j + P - u, by omega⟩
  have hpw : p ^ w * p ^ u = p ^ (j + P) := by
    rw [← pow_add, hw]
  refine ⟨w, hw.symm, ?_, ?_, ?_, ?_⟩
  · rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left s1 (Nat.pow_pos hp0)
  · intro x y hxy
    obtain ⟨h1, h2⟩ := hxy
    rcases Nat.lt_or_ge β y with hy | hy
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hy
      rcases Nat.lt_or_ge x j with hx | hx
      · obtain ⟨u', rfl⟩ := Nat.exists_eq_add_of_le hx.le
        have e1 : p ^ (x + u') * q ^ β = p ^ x * q ^ β * p ^ u' := by
          ring
        have e2 : p ^ x * q ^ (β + k + 1) = p ^ x * q ^ β * q ^ (k + 1) := by
          ring
        rw [e1, e2] at h1
        have h3 := s3 u' (k + 1) (by omega) (Nat.lt_of_mul_lt_mul_left h1)
        have e3 : p ^ x * q ^ β * q ^ (k + 1) = p ^ x * q ^ (k + 1 + β) := by
          ring
        have e4 : p ^ (x + u' + P) = p ^ x * p ^ (P + u') := by
          ring
        rw [e2, e3, e4] at h2
        exact absurd (Nat.lt_of_mul_lt_mul_left h2) (Nat.not_lt.mpr h3)
      · have h01 : p ^ 0 < q ^ 1 := by
          rw [pow_zero, pow_one]
          exact hq
        have h3 := s3 0 1 (Nat.zero_le j) h01
        have hb : p ^ (j + P) ≤ p ^ x * q ^ (β + k + 1) := by
          rw [pow_add]
          exact Nat.mul_le_mul (Nat.pow_le_pow_right hp0 hx)
            (le_trans h3 (Nat.pow_le_pow_right hq0 (by omega)))
        exact absurd h2 (Nat.not_lt.mpr hb)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hy
      rcases Nat.lt_or_ge j x with hx | hx
      · obtain ⟨P', rfl⟩ := Nat.exists_eq_add_of_lt hx
        have e1 : p ^ j * q ^ (y + d) = p ^ j * q ^ y * q ^ d := by
          ring
        have e2 : p ^ (j + P' + 1) * q ^ y = p ^ j * q ^ y * p ^ (P' + 1) := by
          ring
        rw [e1, e2] at h1
        have h3 := s2 (P' + 1) d (by omega) (Nat.lt_of_mul_lt_mul_left h1)
        have e3 : p ^ j * q ^ y * p ^ (P' + 1) = p ^ j * (p ^ (P' + 1) * q ^ y) := by
          ring
        have e5 : p ^ (j + P) = p ^ j * p ^ P := pow_add p j P
        rw [e2, e3, e5] at h2
        have h4 : p ^ (P' + 1) * q ^ y < p ^ P := Nat.lt_of_mul_lt_mul_left h2
        have h5 : p ^ (P' + 1) * q ^ y * q ^ d < p ^ P * q ^ d :=
          Nat.mul_lt_mul_of_pos_right h4 (Nat.pow_pos hq0)
        have e4 : p ^ (P' + 1) * q ^ (y + d) = p ^ (P' + 1) * q ^ y * q ^ d := by
          ring
        rw [e4] at h3
        exact absurd h5 (Nat.not_lt.mpr h3)
      · have ha : p ^ x * q ^ y ≤ p ^ j * q ^ (y + d) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right hp0 hx) (Nat.pow_le_pow_right hq0 (by omega))
        exact absurd h1 (Nat.not_lt.mpr ha)
  · have h7 := Nat.mul_lt_mul_of_pos_right g3 (Nat.pow_pos hp0 : 0 < p ^ w)
    have e1 : 2 * p ^ (P + u) * p ^ w = p ^ P * (2 * p ^ (j + P)) := by
      calc 2 * p ^ (P + u) * p ^ w = 2 * p ^ P * (p ^ w * p ^ u) := by
            ring
        _ = 2 * p ^ P * p ^ (j + P) := by
            rw [hpw]
        _ = p ^ P * (2 * p ^ (j + P)) := by
            ring
    have e2 : (p ^ P * q ^ v + p ^ u * q ^ β) * p ^ w =
        p ^ P * (p ^ w * q ^ v + p ^ j * q ^ β) := by
      calc (p ^ P * q ^ v + p ^ u * q ^ β) * p ^ w
          = p ^ P * (p ^ w * q ^ v) + p ^ w * p ^ u * q ^ β := by
            ring
        _ = p ^ P * (p ^ w * q ^ v) + p ^ (j + P) * q ^ β := by
            rw [hpw]
        _ = p ^ P * (p ^ w * q ^ v + p ^ j * q ^ β) := by
            ring
    rw [e1, e2] at h7
    exact Nat.lt_of_mul_lt_mul_left h7
  · have h8 := Nat.mul_lt_mul_of_pos_left g2
      (Nat.mul_pos (Nat.pow_pos hp0) (Nat.pow_pos hp0) : 0 < p ^ w * p ^ j)
    have e3 : p ^ w * p ^ j * q ^ (v + β) = p ^ w * q ^ v * (p ^ j * q ^ β) := by
      ring
    have e4 : p ^ w * p ^ j * p ^ (P + u) = p ^ (j + P) * p ^ (j + P) := by
      calc p ^ w * p ^ j * p ^ (P + u) = p ^ w * p ^ u * p ^ (j + P) := by
            ring
        _ = p ^ (j + P) * p ^ (j + P) := by
            rw [hpw]
    rw [e3, e4] at h8
    exact h8

/-- `RulerGap` gives the statement on exponents. -/
theorem ordersGap_of_rulerGap (h : RulerGap) : OrdersGap := by
  constructor
  · intro M N P β u v j _ _ _ _ hs _ huP hg
    obtain ⟨w, _, hab, hnb, h2, hsk⟩ := frame_fail (by norm_num) (by norm_num) hs huP hg
    exact h (2 ^ j * 3 ^ β) (2 ^ (j + P)) (2 ^ w * 3 ^ v) ⟨j, β, rfl⟩
      ⟨j + P, 0, by rw [pow_zero, Nat.mul_one]⟩ ⟨w, v, rfl⟩ hab hnb ⟨h2, hsk⟩
  · intro M N P β u v j _ _ _ _ hs _ huP hg
    obtain ⟨w, _, hab, hnb, h2, hsk⟩ := frame_fail (by norm_num) (by norm_num) hs huP hg
    exact h (3 ^ j * 2 ^ β) (3 ^ (j + P)) (3 ^ w * 2 ^ v) ⟨β, j, Nat.mul_comm _ _⟩
      ⟨0, j + P, by rw [pow_zero, Nat.one_mul]⟩ ⟨v, w, Nat.mul_comm _ _⟩ hab
      (noneBetweenPQ_swap hnb) ⟨h2, hsk⟩

/-- `RulerGap` is the statement on exponents. -/
theorem rulerGap_iff_ordersGap : RulerGap ↔ OrdersGap :=
  ⟨ordersGap_of_rulerGap, rulerGap_of_ordersGap⟩

/-- `NoneBetween lo hi` follows from the exponents below X and Y when hi ≤ 2^X and
    hi ≤ 3^Y. -/
theorem noneBetween_of_bounded {lo hi X Y : ℕ} (hX : hi ≤ 2 ^ X) (hY : hi ≤ 3 ^ Y)
    (hfin : ∀ x < X, ∀ y < Y, ¬(lo < 2 ^ x * 3 ^ y ∧ 2 ^ x * 3 ^ y < hi)) :
    NoneBetween lo hi := by
  intro x y hxy
  have hx : x < X := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ X ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ x ≤ 2 ^ x * 3 ^ y := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by norm_num))
    omega
  have hy : y < Y := by
    by_contra hge
    push Not at hge
    have h1 : 3 ^ Y ≤ 3 ^ y := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 3 ^ y ≤ 2 ^ x * 3 ^ y := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by norm_num))
    omega
  exact hfin x hx y hy hxy

/-- 177147 = 3^11, 186624 = 2^8 3^6 and 196608 = 2^16 3. -/
theorem values : (177147 : ℕ) = 2 ^ 0 * 3 ^ 11 ∧ (186624 : ℕ) = 2 ^ 8 * 3 ^ 6 ∧
    (196608 : ℕ) = 2 ^ 16 * 3 ^ 1 := by
  norm_num

/-- No 3-smooth number lies between 3^11 and 2^8 3^6. -/
theorem noneBetween_first : NoneBetween 177147 186624 := by
  apply noneBetween_of_bounded (X := 18) (Y := 12) (by norm_num) (by norm_num)
  decide +kernel

/-- No 3-smooth number lies between 2^8 3^6 and 2^16 3. -/
theorem noneBetween_second : NoneBetween 186624 196608 := by
  apply noneBetween_of_bounded (X := 18) (Y := 12) (by norm_num) (by norm_num)
  decide +kernel

/-- The rule of the border fails. With a = 3^11 in row 11, b = 2^8 3^6 in row 6 and
    n = 2^16 3 in row 1: a, b, n are three 3-smooth numbers in a row; b -> n is the second
    step with the factor b / a (n a = b^2), so it skips nothing; and n lies before the place
    c where the line from a through b meets row 0, (11 - 6) c = (11 - 6) b + 6 (b - a). -/
theorem border_rule_fails : ∃ a b n : ℕ, IsSmooth a ∧ IsSmooth b ∧ IsSmooth n ∧
    a < b ∧ b < n ∧ NoneBetween a b ∧ NoneBetween b n ∧ n * a = b * b ∧
    (11 - 6) * n < (11 - 6) * b + 6 * (b - a) := by
  refine ⟨177147, 186624, 196608, ⟨0, 11, values.1⟩, ⟨8, 6, values.2.1⟩, ⟨16, 1, values.2.2⟩,
    by norm_num, by norm_num, noneBetween_first, noneBetween_second, by norm_num, by norm_num⟩

end SmoothRuler
