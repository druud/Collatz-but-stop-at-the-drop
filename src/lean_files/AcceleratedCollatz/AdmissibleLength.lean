-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Core

/-!
  Admissible length (paper sec:words): words of 3/2 (tripling) and 1/2
  (halving) factors, admissibility (level above 1 until the very end), and
  the length of an admissible word: p2 of its Order.
-/

namespace AcceleratedCollatz

variable (s : List Bool)

/-- true = tripling factor 3/2, false = halving factor 1/2. -/
def factor (b : Bool) : ℚ := if b then 3 / 2 else 1 / 2

/-- Running product of a word: the product of its factors. -/
def seqProduct (s : List Bool) : ℚ := (s.map factor).prod

/-- Order: count of tripling (true) entries. -/
def order (s : List Bool) : ℕ := (s.filter id).length

/-- An admissible (first-passage) word. -/
structure Admissible (s : List Bool) : Prop where
  /-- Every proper nonempty prefix has level > 1. -/
  prefix_gt : ∀ m, 1 ≤ m → m < s.length → 1 < seqProduct (s.take m)
  /-- The whole word has level < 1. -/
  lt_one : seqProduct s < 1

/-- `Admissible` is decidable. -/
instance (s : List Bool) : Decidable (Admissible s) :=
  decidable_of_iff
    ((∀ m, 1 ≤ m → m < s.length → 1 < seqProduct (s.take m)) ∧ seqProduct s < 1)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

/-- An admissible word ends with 0. -/
theorem admissible_last_false (hA : Admissible s) (hne : s ≠ []) :
    s.getLast hne = false := by
  by_contra hlast
  simp only [Bool.not_eq_false] at hlast
  have hlen : s.length ≥ 1 := List.length_pos_of_ne_nil hne
  have hsplit : s = s.dropLast ++ [s.getLast hne] :=
    (List.dropLast_append_getLast hne).symm
  have hfull : seqProduct s = seqProduct s.dropLast * (3 / 2) := by
    rw [hsplit]
    unfold seqProduct
    simp [factor, hlast]
  have hdlen : s.dropLast.length = s.length - 1 := by simp
  rcases Nat.lt_or_ge s.length 2 with hlt2 | hge2
  · have hz : s.dropLast.length = 0 := by omega
    have hdl : s.dropLast = [] := List.length_eq_zero_iff.mp hz
    rw [hdl] at hfull
    have heval : seqProduct s = 3 / 2 := by
      rw [hfull]
      simp [seqProduct]
    linarith [hA.lt_one, heval]
  · have hdlpos : 1 ≤ s.dropLast.length := by omega
    have hdllt : s.dropLast.length < s.length := by omega
    have hdltake : s.dropLast = s.take s.dropLast.length := by
      simp [List.dropLast_eq_take]
    have hprefix : 1 < seqProduct s.dropLast := by
      rw [hdltake]
      exact hA.prefix_gt s.dropLast.length hdlpos hdllt
    linarith [hA.lt_one, hfull, hprefix]

/-- The Order of a word is at most its length. -/
theorem order_le_length (l : List Bool) : order l ≤ l.length := by
  unfold order
  exact List.length_filter_le _ _

/-- Product of a word: (3/2)^(ones) (1/2)^(zeros). -/
theorem seqProduct_eq (l : List Bool) :
    seqProduct l = (3 / 2 : ℚ) ^ (order l) * (1 / 2 : ℚ) ^ (l.length - order l) := by
  induction l with
  | nil => simp [seqProduct, order]
  | cons b t ih =>
    have hle := order_le_length t
    cases b with
    | true =>
      have hord : order (true :: t) = order t + 1 := by
        unfold order
        simp
      have hlen : (true :: t).length = t.length + 1 := by simp
      have hprod : seqProduct (true :: t) = (3 / 2) * seqProduct t := by
        unfold seqProduct
        simp [factor]
      rw [hprod, ih, hord, hlen]
      have hsub : t.length + 1 - (order t + 1) = t.length - order t := by omega
      rw [hsub]
      ring
    | false =>
      have hord : order (false :: t) = order t := by
        unfold order
        simp
      have hlen : (false :: t).length = t.length + 1 := by simp
      have hprod : seqProduct (false :: t) = (1 / 2) * seqProduct t := by
        unfold seqProduct
        simp [factor]
      rw [hprod, ih, hord, hlen]
      have hsub : t.length + 1 - order t = (t.length - order t) + 1 := by omega
      rw [hsub, pow_succ]
      ring

/-- (3/2)^a (1/2)^(b-a) 2^b = 3^a for a ≤ b. -/
theorem seqProduct_combine_mul (a b : ℕ) (hab : a ≤ b) :
    (3 / 2 : ℚ) ^ a * (1 / 2 : ℚ) ^ (b - a) * (2 : ℚ) ^ b = (3 : ℚ) ^ a := by
  have hexp : (2:ℚ) ^ b = (2:ℚ) ^ a * (2:ℚ) ^ (b - a) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : (2:ℚ) ^ a ≠ 0 := by positivity
  have h2 : (2:ℚ) ^ (b - a) ≠ 0 := by positivity
  rw [hexp, div_pow, div_pow, one_pow]
  rw [show (3:ℚ) ^ a / (2:ℚ) ^ a * (1 / (2:ℚ) ^ (b - a)) * ((2:ℚ) ^ a * (2:ℚ) ^ (b - a))
      = (3:ℚ) ^ a * ((2:ℚ) ^ a / (2:ℚ) ^ a) * ((2:ℚ) ^ (b - a) / (2:ℚ) ^ (b - a)) from by ring]
  rw [div_self h1, div_self h2]
  ring

/-- An admissible word of Order n has length p2(n). -/
theorem admissible_length (hA : Admissible s) :
    s.length = p2_of (order s) := by
  have hne : s ≠ [] := by
    intro hcontra
    rw [hcontra] at hA
    have h := hA.lt_one
    simp [seqProduct] at h
  have hlast := admissible_last_false s hA hne
  have hsplit : s = s.dropLast ++ [false] := by
    rw [← hlast]
    exact (List.dropLast_append_getLast hne).symm
  have hdlen : s.dropLast.length = s.length - 1 := by simp
  have hdord : order s.dropLast = order s := by
    conv_rhs => rw [hsplit]
    unfold order
    simp
  have hple : order s ≤ s.length := order_le_length s
  have hple1 : order s ≤ s.length - 1 := by
    have := order_le_length s.dropLast
    rw [hdord, hdlen] at this
    exact this
  have hnpos : s.length ≥ 1 := List.length_pos_of_ne_nil hne
  have hub_nat : (3 : ℕ) ^ (order s) < 2 ^ s.length := by
    have hcombine := seqProduct_combine_mul (order s) s.length hple
    have heq : seqProduct s * (2:ℚ) ^ s.length = (3:ℚ) ^ (order s) := by
      rw [seqProduct_eq s]
      exact hcombine
    have h2pos : (0:ℚ) < (2:ℚ) ^ s.length := by positivity
    have hstep := mul_lt_mul_of_pos_right hA.lt_one h2pos
    rw [heq, one_mul] at hstep
    exact_mod_cast hstep
  have hdllt : s.dropLast.length < s.length := by omega
  rcases Nat.lt_or_ge s.length 2 with hlt2 | hge2
  · have hl1 : s.length = 1 := by omega
    have hz : s.dropLast.length = 0 := by omega
    have hdl : s.dropLast = [] := List.length_eq_zero_iff.mp hz
    have hord0 : order s = 0 := by
      rw [← hdord, hdl]
      unfold order
      simp
    rw [hl1, hord0]
    unfold p2_of
    simp
  · have hdlpos : 1 ≤ s.dropLast.length := by omega
    have hdltake : s.dropLast = s.take s.dropLast.length := by
      simp [List.dropLast_eq_take]
    have hlb_raw : 1 < seqProduct s.dropLast := by
      rw [hdltake]
      exact hA.prefix_gt s.dropLast.length hdlpos hdllt
    have hlb_nat : 2 ^ (s.length - 1) ≤ 3 ^ (order s) := by
      have hcombine := seqProduct_combine_mul (order s) (s.length - 1) hple1
      have heq : seqProduct s.dropLast * (2:ℚ) ^ (s.length - 1) = (3:ℚ) ^ (order s) := by
        rw [seqProduct_eq s.dropLast, hdord, hdlen]
        exact hcombine
      have h2pos : (0:ℚ) < (2:ℚ) ^ (s.length - 1) := by positivity
      have hstep := mul_lt_mul_of_pos_right hlb_raw h2pos
      rw [heq, one_mul] at hstep
      exact_mod_cast hstep.le
    have hub_nat' : 3 ^ order s < 2 ^ (s.length - 1 + 1) := by
      rw [Nat.sub_add_cancel hnpos]
      exact hub_nat
    have hlog : Nat.log 2 (3 ^ order s) = s.length - 1 :=
      Nat.log_eq_of_pow_le_of_lt_pow hlb_nat hub_nat'
    unfold p2_of
    omega

/-- Prefix property (paper sec:words): no admissible word is a proper
    prefix of another. -/
theorem admissible_not_prefix (s s' : List Bool)
    (hA : Admissible s) (hA' : Admissible s') (hne : s ≠ s') :
    ¬ s <+: s' := by
  intro hpre
  obtain ⟨t, ht⟩ := hpre
  have hspos : s ≠ [] := by
    intro h
    rw [h] at hA
    have h1 := hA.lt_one
    simp [seqProduct] at h1
  have hlen : s.length < s'.length := by
    rcases Nat.lt_or_ge s.length s'.length with h | h
    · exact h
    · exfalso
      have hsum : s.length + t.length = s'.length := by
        rw [← ht]
        simp
      have htlen : t.length = 0 := by omega
      have ht0 : t = [] := List.length_eq_zero_iff.mp htlen
      rw [ht0, List.append_nil] at ht
      exact hne ht
  have hstake : s'.take s.length = s := by
    rw [← ht]
    simp
  have hspos_len : 1 ≤ s.length := by
    rcases Nat.eq_zero_or_pos s.length with h0 | h0
    · exact absurd (List.length_eq_zero_iff.mp h0) hspos
    · exact h0
  have hbound := hA'.prefix_gt s.length hspos_len hlen
  rw [hstake] at hbound
  linarith [hA.lt_one, hbound]

end AcceleratedCollatz
