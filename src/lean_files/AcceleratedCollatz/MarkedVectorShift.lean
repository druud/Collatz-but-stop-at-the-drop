-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.MarkedVector

/-!
  Shift-invariance of markedVector (underlies the marked-vector <->
  class-id bijection, paper sec:fast): shifting the start
  x0 -> x0 + i*2^Q, for Q at least the decoded bit-length of the trajectory of
  x0, does not change the entries of markedVector, for any i
  (`markedVector_shift`, from `markedVector_shift_from`).
  Hypotheses: the decoded trajectory is admissible, and it ends within the
  given fuel.
  Step lemmas, with free parameters x, oc (ones so far), lc (letters so far):
  `markedVector_shift_terminal_odd`, `_continue_odd`, `_terminal_even`,
  `_continue_even`; for the terminal even entry `minCorrection_shift_matches`
  (from `_sufficiency` and `_minimality`).
-/

namespace AcceleratedCollatz

/-- One step, odd and terminal (R x < x0): the shifted start and value give the
    same entries. -/
theorem markedVector_shift_terminal_odd (x0 i Q x oc lc fuel : ℕ) (hx0 : x0 > 1)
    (hxge : x0 ≤ x) (hxodd : x % 2 = 1) (hlcQ : lc ≤ Q)
    (hQrem : Q - lc ≥ trailingOnes x + 1) (hprefix : x * 2 ^ lc ≥ x0 * 3 ^ oc)
    (hterm : R x < x0) :
    markedVector (fuel + 1) (x0 + i * 2 ^ Q) (x + i * 3 ^ oc * 2 ^ (Q - lc)) =
      markedVector (fuel + 1) x0 x := by
  have hx1 : x > 1 := by omega
  set v := trailingOnes x with hv_def
  have hdvd : 2 ^ v ∣ (x + 1) := pow_trailingOnes_dvd x
  set s := (x + 1) / 2 ^ v with hs_def
  have hsmul : s * 2 ^ v = x + 1 := Nat.div_mul_cancel hdvd
  have hxOddP : Odd x := Nat.odd_iff.mpr hxodd
  have hsOdd : Odd s := odd_div_pow_trailingOnes x hxOddP
  have hRclosed : R x = (3 ^ v * s - 1) / 2 := R_odd_closed_form x hx1 hxOddP
  have h3vsOdd : Odd (3 ^ v * s) := ((by decide : Odd 3).pow).mul hsOdd
  have hexact : 2 * R x + 1 = 3 ^ v * s := by
    obtain ⟨k, hk⟩ := h3vsOdd
    rw [hRclosed, hk]
    omega
  have hv2 : R x * 2 ^ (v + 1) = 3 ^ v * x + (3 ^ v - 2 ^ v) := by
    have hstep : (2 * R x + 1) * 2 ^ v = 3 ^ v * s * 2 ^ v := by rw [hexact]
    have hkey : R x * 2 ^ (v + 1) + 2 ^ v = 3 ^ v * x + 3 ^ v := by
      calc R x * 2 ^ (v + 1) + 2 ^ v = (2 * R x + 1) * 2 ^ v := by
             rw [pow_succ]
             ring
        _ = 3 ^ v * s * 2 ^ v := hstep
        _ = 3 ^ v * (s * 2 ^ v) := by ring
        _ = 3 ^ v * (x + 1) := by rw [hsmul]
        _ = 3 ^ v * x + 3 ^ v := by ring
    have hle32 : (2:ℕ) ^ v ≤ 3 ^ v := Nat.pow_le_pow_left (by norm_num) _
    omega
  rw [markedVector_succ_odd fuel x0 x hxodd]
  have hshifted_odd : (x + i * 3 ^ oc * 2 ^ (Q - lc)) % 2 = 1 := by
    have hdvd2 : (2:ℕ) ∣ 2 ^ (Q - lc) := dvd_pow_self 2 (by omega)
    have hdvd3 : (2:ℕ) ∣ i * 3 ^ oc * 2 ^ (Q - lc) := hdvd2.mul_left _
    omega
  rw [markedVector_succ_odd fuel (x0 + i * 2 ^ Q)
    (x + i * 3 ^ oc * 2 ^ (Q - lc)) hshifted_odd]
  have hvshift : trailingOnes (x + i * 3 ^ oc * 2 ^ (Q - lc)) = v :=
    trailingOnes_shift x (i * 3 ^ oc) (Q - lc) hxOddP (by omega)
  have hRshift : R (x + i * 3 ^ oc * 2 ^ (Q - lc)) =
      R x + 3 ^ v * (i * 3 ^ oc) * 2 ^ (Q - lc - v - 1) :=
    R_shift_odd x (i * 3 ^ oc) (Q - lc) hx1 hxOddP (by omega)
  rw [hvshift, hRshift]
  set E := Q - lc - v - 1 with hE_def
  have hQeq : Q = E + (lc + v + 1) := by omega
  have hQpow : (2:ℕ) ^ Q = 2 ^ E * 2 ^ (lc + v + 1) := by rw [hQeq, pow_add]
  have hshiftval : R x + 3 ^ v * (i * 3 ^ oc) * 2 ^ E =
      R x + i * 2 ^ E * 3 ^ (oc + v) := by
        rw [pow_add]
        ring
  have hv2ge : R x * 2 ^ (v + 1) ≥ 3 ^ v * x := by omega
  have h2vpos : 0 < (2:ℕ) ^ (v + 1) := by positivity
  have hmul : R x * 2 ^ (v + 1) < x0 * 2 ^ (v + 1) := (Nat.mul_lt_mul_right h2vpos).mpr hterm
  have h1 : x0 * 2 ^ (v + 1) > 3 ^ v * x := by omega
  have h2lcpos : 0 < (2:ℕ) ^ lc := by positivity
  have h2 : x0 * 2 ^ (v + 1) * 2 ^ lc > 3 ^ v * x * 2 ^ lc := (Nat.mul_lt_mul_right h2lcpos).mpr h1
  have h3' : 3 ^ v * (x * 2 ^ lc) ≥ 3 ^ v * (x0 * 3 ^ oc) := Nat.mul_le_mul_left _ hprefix
  have hcross : x0 * (2 ^ (v + 1) * 2 ^ lc) > x0 * 3 ^ (v + oc) := by
    have heq1 : x0 * 2 ^ (v + 1) * 2 ^ lc = x0 * (2 ^ (v + 1) * 2 ^ lc) := by ring
    have heq2 : 3 ^ v * x * 2 ^ lc = 3 ^ v * (x * 2 ^ lc) := by ring
    have heq3 : x0 * 3 ^ (v + oc) = 3 ^ v * (x0 * 3 ^ oc) := by
      rw [pow_add]
      ring
    omega
  have hcross' : (2:ℕ) ^ (v + 1) * 2 ^ lc > 3 ^ (v + oc) :=
    lt_of_mul_lt_mul_left hcross (by omega)
  have hcross2 : (2:ℕ) ^ (lc + v + 1) > 3 ^ (oc + v) := by
    have heq4 : (2:ℕ) ^ (v + 1) * 2 ^ lc = 2 ^ (lc + v + 1) := by
      rw [← pow_add]
      congr 1
      ring
    have heq5 : v + oc = oc + v := by ring
    rw [heq4, heq5] at hcross'
    exact hcross'
  have hterm_shift : R x + 3 ^ v * (i * 3 ^ oc) * 2 ^ E < x0 + i * 2 ^ Q := by
    have hstep1 : i * (2 ^ E * 2 ^ (lc + v + 1)) ≥ i * (2 ^ E * 3 ^ (oc + v)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_of_lt hcross2))
    rw [hshiftval, hQpow]
    have hassoc : i * 2 ^ E * 3 ^ (oc + v) = i * (2 ^ E * 3 ^ (oc + v)) := by ring
    rw [hassoc]
    omega
  rw [ite_eq_left hterm, ite_eq_left hterm_shift]

/-- One step, odd and continuing: the shifted start and value give the same
    entries, given the same for the tail (`htail`) and level > 1 after the step
    (`hadm_next`). -/
theorem markedVector_shift_continue_odd (x0 i Q x oc lc fuel : ℕ) (hx0 : x0 > 1)
    (hxge : x0 ≤ x) (hxodd : x % 2 = 1) (hlcQ : lc ≤ Q)
    (hQrem : Q - lc ≥ trailingOnes x + 1) (hterm : ¬ (R x < x0))
    (hadm_next : (2 : ℕ) ^ (lc + trailingOnes x + 1) < 3 ^ (oc + trailingOnes x))
    (htail : markedVector fuel (x0 + i * 2 ^ Q)
        (R x + i * 3 ^ (oc + trailingOnes x) * 2 ^ (Q - (lc + trailingOnes x + 1))) =
      markedVector fuel x0 (R x)) :
    markedVector (fuel + 1) (x0 + i * 2 ^ Q) (x + i * 3 ^ oc * 2 ^ (Q - lc)) =
      markedVector (fuel + 1) x0 x := by
  have hx1 : x > 1 := by omega
  have hxOddP : Odd x := Nat.odd_iff.mpr hxodd
  set v := trailingOnes x with hv_def
  rw [markedVector_succ_odd fuel x0 x hxodd, ite_eq_right hterm, ← hv_def]
  have hshifted_odd : (x + i * 3 ^ oc * 2 ^ (Q - lc)) % 2 = 1 := by
    have hdvd2 : (2:ℕ) ∣ 2 ^ (Q - lc) := dvd_pow_self 2 (by omega)
    have hdvd3 : (2:ℕ) ∣ i * 3 ^ oc * 2 ^ (Q - lc) := hdvd2.mul_left _
    omega
  rw [markedVector_succ_odd fuel (x0 + i * 2 ^ Q)
    (x + i * 3 ^ oc * 2 ^ (Q - lc)) hshifted_odd]
  have hvshift : trailingOnes (x + i * 3 ^ oc * 2 ^ (Q - lc)) = v :=
    trailingOnes_shift x (i * 3 ^ oc) (Q - lc) hxOddP (by omega)
  have hRshift : R (x + i * 3 ^ oc * 2 ^ (Q - lc)) =
      R x + 3 ^ v * (i * 3 ^ oc) * 2 ^ (Q - lc - v - 1) :=
    R_shift_odd x (i * 3 ^ oc) (Q - lc) hx1 hxOddP (by omega)
  rw [hvshift, hRshift]
  set E := Q - lc - v - 1 with hE_def
  have hQeq : Q = E + (lc + v + 1) := by omega
  have hQpow : (2:ℕ) ^ Q = 2 ^ E * 2 ^ (lc + v + 1) := by rw [hQeq, pow_add]
  have hshiftval : R x + 3 ^ v * (i * 3 ^ oc) * 2 ^ E =
      R x + i * (2 ^ E * 3 ^ (oc + v)) := by
        rw [pow_add]
        ring
  have hterm_shift : ¬ (R x + 3 ^ v * (i * 3 ^ oc) * 2 ^ E < x0 + i * 2 ^ Q) := by
    have hstep1 : i * (2 ^ E * 2 ^ (lc + v + 1)) ≤ i * (2 ^ E * 3 ^ (oc + v)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_of_lt hadm_next))
    rw [hshiftval, hQpow]
    omega
  rw [ite_eq_right hterm_shift]
  have hEeq : E = Q - (lc + v + 1) := by omega
  have hshiftval2 : R x + 3 ^ v * (i * 3 ^ oc) * 2 ^ E =
      R x + i * 3 ^ (oc + v) * 2 ^ (Q - (lc + v + 1)) := by
    rw [← hEeq, pow_add]
    ring
  rw [hshiftval2]
  congr 1

/-- A terminal even step gives the singleton [-(minCorrection x0 x)], for every
    fuel ≥ 1. -/
theorem markedVector_terminal_even_singleton (x0 x : ℕ) (hx0 : x0 > 1)
    (hxge : x0 ≤ x) (hxeven : x % 2 ≠ 1) (hterm : x / 2 ^ (trailingZeros x) < x0) :
    ∀ fuel, markedVector (fuel + 1) x0 x = [markedEntry false (minCorrection x0 x)] := by
  intro fuel
  have hxeven' : Even x := Nat.even_iff.mpr (by omega)
  rw [markedVector_succ_even fuel x0 x hxeven,
    evenStep_spec x0 (by omega) x hxge hxeven', ite_eq_left hterm]

/-- A prefix of the decoded trajectory that ends inside the zeros of the
    terminal even entry, at lc + k with k ≤ mc, has order oc. -/
theorem order_take_at_terminal_even (x0 : ℕ) (hx0 : x0 > 1) (fuel1 fuel2 k : ℕ)
    (hxge : x0 ≤ (trajStats x0 fuel1 x0).2.2)
    (hxeven : (trajStats x0 fuel1 x0).2.2 % 2 ≠ 1)
    (hterm : (trajStats x0 fuel1 x0).2.2 / 2 ^ (trailingZeros (trajStats x0 fuel1 x0).2.2) < x0)
    (hk : k ≤ minCorrection x0 (trajStats x0 fuel1 x0).2.2) :
    order ((decodeVector (markedVector (fuel1 + (fuel2 + 1)) x0 x0)).take
      ((trajStats x0 fuel1 x0).2.1 + k)) = (trajStats x0 fuel1 x0).1 := by
  set x := (trajStats x0 fuel1 x0).2.2 with hx_def
  set oc := (trajStats x0 fuel1 x0).1 with hoc_def
  set lc := (trajStats x0 fuel1 x0).2.1 with hlc_def
  have hsplit := markedVector_prefix_split x0 hx0 fuel1 (fuel2 + 1) x0 (le_refl x0)
    (by omega)
  have hterminal := markedVector_terminal_even_singleton x0 x hx0 hxge hxeven hterm fuel2
  rw [hsplit, hterminal]
  have hlen : (decodeVector (markedVector fuel1 x0 x0)).length = lc :=
    length_decodeVector_eq_trajStats x0 hx0 fuel1 x0 (le_refl x0)
  have hdecode : decodeVector (markedVector fuel1 x0 x0 ++ [markedEntry false
      (minCorrection x0 x)]) = decodeVector (markedVector fuel1 x0 x0) ++
      List.replicate (minCorrection x0 x) false := by
    unfold decodeVector
    rw [List.flatMap_append]
    simp [markedEntry_false, expandEntry]
  rw [hdecode]
  have htake : (decodeVector (markedVector fuel1 x0 x0) ++
      List.replicate (minCorrection x0 x) false).take (lc + k) =
      decodeVector (markedVector fuel1 x0 x0) ++ List.replicate k false := by
    rw [List.take_append, hlen]
    have h1 : lc + k - lc = k := by omega
    rw [h1, List.take_of_length_le (by omega), List.take_replicate, min_eq_left hk]
  rw [htake]
  have horder_append : order (decodeVector (markedVector fuel1 x0 x0) ++
      List.replicate k false) = order (decodeVector (markedVector fuel1 x0 x0)) +
      order (List.replicate k false) := by
    unfold order
    simp [List.filter_append]
  rw [horder_append, order_decodeVector_eq_trajOrder x0 (by omega) fuel1 x0 (le_refl x0),
    trajOrder_eq_trajStats_fst x0 fuel1 x0, ← hoc_def]
  unfold order
  simp

/-- For an admissible decoded trajectory with terminal even entry mc ≥ 2:
    3^oc > 2^(lc + mc - 1). -/
theorem admissible_gives_even_terminal_minimality (x0 : ℕ) (hx0 : x0 > 1) (fuel1 fuel2 : ℕ)
    (hxge : x0 ≤ (trajStats x0 fuel1 x0).2.2)
    (hxeven : (trajStats x0 fuel1 x0).2.2 % 2 ≠ 1)
    (hterm : (trajStats x0 fuel1 x0).2.2 / 2 ^ (trailingZeros (trajStats x0 fuel1 x0).2.2) < x0)
    (hmc2 : minCorrection x0 (trajStats x0 fuel1 x0).2.2 ≥ 2)
    (hAdm : Admissible (decodeVector (markedVector (fuel1 + (fuel2 + 1)) x0 x0))) :
    (3:ℕ) ^ (trajStats x0 fuel1 x0).1 >
      2 ^ ((trajStats x0 fuel1 x0).2.1 + minCorrection x0 (trajStats x0 fuel1 x0).2.2 - 1) := by
  set x := (trajStats x0 fuel1 x0).2.2 with hx_def
  set oc := (trajStats x0 fuel1 x0).1 with hoc_def
  set lc := (trajStats x0 fuel1 x0).2.1 with hlc_def
  set mc := minCorrection x0 x with hmc_def
  set m := lc + mc - 1 with hm_def
  have hm1 : 1 ≤ m := by omega
  have hk : mc - 1 ≤ minCorrection x0 (trajStats x0 fuel1 x0).2.2 := by
    rw [← hx_def, ← hmc_def]
    omega
  have horder := order_take_at_terminal_even x0 hx0 fuel1 fuel2 (mc - 1) hxge hxeven hterm hk
  rw [← hoc_def, ← hlc_def] at horder
  have hmeq : lc + (mc - 1) = m := by omega
  rw [hmeq] at horder
  have htrajadd := trajStats_add x0 hx0 fuel1 (fuel2 + 1) x0 (le_refl x0)
    (by omega)
  have hmcstep : (trajStats x0 (fuel2 + 1) x).2.1 = mc := by
    have hxeven' : Even x := Nat.even_iff.mpr (by omega)
    have hx1 : x > 1 := by
      obtain ⟨r, hr⟩ := hxeven'
      omega
    unfold trajStats
    simp only [hxeven, ite_false, hterm, ite_true]
    exact hmc_def.symm
  have hfulllen : (decodeVector (markedVector (fuel1 + (fuel2 + 1)) x0 x0)).length =
      lc + mc := by
    rw [length_decodeVector_eq_trajStats x0 hx0 (fuel1 + (fuel2 + 1)) x0 (le_refl x0)]
    rw [htrajadd.2.1, hmcstep, ← hlc_def]
  have hlenlt : m < (decodeVector (markedVector (fuel1 + (fuel2 + 1)) x0 x0)).length := by
    rw [hfulllen]
    omega
  have hclause := hAdm.prefix_gt m hm1 hlenlt
  rw [seqProduct_eq_pow_ratio] at hclause
  have hcnt : ((decodeVector (markedVector (fuel1 + (fuel2 + 1)) x0 x0)).take m).count
      true = oc := by
        rw [← order_eq_count_true]
        exact horder
  have htlen : ((decodeVector (markedVector (fuel1 + (fuel2 + 1)) x0 x0)).take
      m).length = m := by
    rw [List.length_take]
    omega
  rw [hcnt, htlen] at hclause
  rw [lt_div_iff₀ (by positivity)] at hclause
  have : (2:ℚ) ^ m < 3 ^ oc := by linarith [hclause]
  exact_mod_cast this

/-- Sufficiency under the shift: the shifted value, halved mc times, is below
    the shifted start. -/
theorem minCorrection_shift_sufficiency (x0 i Q x oc lc mc : ℕ) (hx0 : x0 > 1)
    (_hxge : x0 ≤ x) (hlcQ : lc ≤ Q) (hQrem : Q - lc ≥ mc)
    (hprefix : x * 2 ^ lc ≥ x0 * 3 ^ oc) (hmc_def : mc = minCorrection x0 x)
    (_hmcdvd : 2 ^ mc ∣ x) :
    (x + i * 3 ^ oc * 2 ^ (Q - lc)) / 2 ^ mc < x0 + i * 2 ^ Q := by
  have hsuff : x / 2 ^ mc < x0 := by
    rw [hmc_def]
    exact minCorrection_suff x0 x (by omega)
  have hxlt : x < x0 * 2 ^ mc := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)] at hsuff
    omega
  have hcross : x0 * 2 ^ (mc + lc) > x0 * 3 ^ oc := by
    have h1 : x0 * 2 ^ mc * 2 ^ lc > x * 2 ^ lc := by
      have h2vpos : 0 < (2:ℕ) ^ lc := by positivity
      exact (Nat.mul_lt_mul_right h2vpos).mpr hxlt
    have heq : x0 * 2 ^ mc * 2 ^ lc = x0 * 2 ^ (mc + lc) := by
      rw [pow_add]
      ring
    omega
  have hcross2 : (2:ℕ) ^ (mc + lc) > 3 ^ oc := by
    have hx0pos : 0 < x0 := by omega
    exact lt_of_mul_lt_mul_left hcross (le_of_lt hx0pos)
  have hpoweq : (2:ℕ) ^ (Q - lc) = 2 ^ mc * 2 ^ (Q - lc - mc) := by
    rw [← pow_add]
    congr 1
    omega
  have hswap : i * 3 ^ oc * 2 ^ (Q - lc) = (i * 3 ^ oc * 2 ^ (Q - lc - mc)) * 2 ^ mc := by
    rw [hpoweq]
    ring
  rw [hswap]
  have h2mcpos : (0:ℕ) < 2 ^ mc := by positivity
  rw [Nat.add_mul_div_right x (i * 3 ^ oc * 2 ^ (Q - lc - mc)) h2mcpos]
  have hstep1 : i * 3 ^ oc * 2 ^ (Q - lc - mc) < i * 2 ^ Q ∨ i = 0 := by
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · right
      exact hi0
    · left
      have hkey : 3 ^ oc * 2 ^ (Q - lc - mc) < 2 ^ Q := by
        have heq2 : (2:ℕ) ^ Q = 2 ^ (mc + lc) * 2 ^ (Q - lc - mc) := by
          rw [← pow_add]
          congr 1
          omega
        rw [heq2]
        have hpos2 : 0 < (2:ℕ) ^ (Q - lc - mc) := by positivity
        exact (Nat.mul_lt_mul_right hpos2).mpr hcross2
      calc i * 3 ^ oc * 2 ^ (Q - lc - mc) = i * (3 ^ oc * 2 ^ (Q - lc - mc)) := by ring
        _ < i * 2 ^ Q := (Nat.mul_lt_mul_left hipos).mpr hkey
  rcases hstep1 with h | h
  · omega
  · simp [h]
    omega

/-- Minimality under the shift: the shifted value, halved mc - 1 times, is not
    below the shifted start, given 3^oc > 2^(lc + mc - 1). -/
theorem minCorrection_shift_minimality (x0 i Q x oc lc mc : ℕ) (hx0 : x0 > 1)
    (hlcQ : lc ≤ Q) (hQrem : Q - lc ≥ mc) (hmcpos : mc ≥ 1)
    (hmc_def : mc = minCorrection x0 x) (_hmcdvd : 2 ^ (mc - 1) ∣ x)
    (hadm_min : (3 : ℕ) ^ oc > 2 ^ (lc + mc - 1)) :
    (x + i * 3 ^ oc * 2 ^ (Q - lc)) / 2 ^ (mc - 1) ≥ x0 + i * 2 ^ Q := by
  have hmin : x / 2 ^ (mc - 1) ≥ x0 := by
    rw [hmc_def]
    exact minCorrection_min x0 x (by omega) (by omega)
  have hpoweq : (2:ℕ) ^ (Q - lc) = 2 ^ (mc - 1) * 2 ^ (Q - lc - (mc - 1)) := by
    rw [← pow_add]
    congr 1
    omega
  have hswap : i * 3 ^ oc * 2 ^ (Q - lc) =
      (i * 3 ^ oc * 2 ^ (Q - lc - (mc - 1))) * 2 ^ (mc - 1) := by
    rw [hpoweq]
    ring
  rw [hswap]
  have hpos : (0:ℕ) < 2 ^ (mc - 1) := by positivity
  rw [Nat.add_mul_div_right x (i * 3 ^ oc * 2 ^ (Q - lc - (mc - 1))) hpos]
  have hstep1 : i * 2 ^ Q ≤ i * 3 ^ oc * 2 ^ (Q - lc - (mc - 1)) := by
    have hkey : (2:ℕ) ^ Q ≤ 3 ^ oc * 2 ^ (Q - lc - (mc - 1)) := by
      have heq2 : (2:ℕ) ^ Q = 2 ^ (lc + mc - 1) * 2 ^ (Q - lc - (mc - 1)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [heq2]
      exact Nat.mul_le_mul_right _ (le_of_lt hadm_min)
    calc i * 2 ^ Q ≤ i * (3 ^ oc * 2 ^ (Q - lc - (mc - 1))) :=
          Nat.mul_le_mul_left i hkey
      _ = i * 3 ^ oc * 2 ^ (Q - lc - (mc - 1)) := by ring
  omega

/-- `minCorrection` of the shifted start and value is mc. -/
theorem minCorrection_shift_matches (x0 i Q x oc lc mc : ℕ) (hx0 : x0 > 1)
    (hxge : x0 ≤ x) (hlcQ : lc ≤ Q) (hQrem : Q - lc ≥ mc)
    (hprefix : x * 2 ^ lc ≥ x0 * 3 ^ oc) (hmc_def : mc = minCorrection x0 x)
    (hmcdvd : 2 ^ mc ∣ x)
    (hadm_min : mc ≥ 1 → (3 : ℕ) ^ oc > 2 ^ (lc + mc - 1)) :
    minCorrection (x0 + i * 2 ^ Q) (x + i * 3 ^ oc * 2 ^ (Q - lc)) = mc := by
  apply minCorrection_unique _ _ _ (by omega)
  · exact minCorrection_shift_sufficiency x0 i Q x oc lc mc hx0 hxge hlcQ hQrem hprefix
      hmc_def hmcdvd
  · rcases Nat.eq_zero_or_pos mc with hmc0 | hmcpos
    · left
      exact hmc0
    · right
      have hmcdvd' : 2 ^ (mc - 1) ∣ x := by
        have : 2 ^ (mc - 1) ∣ 2 ^ mc := pow_dvd_pow 2 (by omega)
        exact this.trans hmcdvd
      exact minCorrection_shift_minimality x0 i Q x oc lc mc hx0 hlcQ hQrem hmcpos hmc_def
        hmcdvd' (hadm_min hmcpos)

/-- One step, even and terminal: the shifted start and value give the same
    entries. -/
theorem markedVector_shift_terminal_even (x0 i Q x oc lc fuel : ℕ) (hx0 : x0 > 1)
    (hxge : x0 ≤ x) (hxeven : x % 2 ≠ 1) (hlcQ : lc ≤ Q)
    (hQrem : Q - lc ≥ minCorrection x0 x) (hprefix : x * 2 ^ lc ≥ x0 * 3 ^ oc)
    (hterm : x / 2 ^ (trailingZeros x) < x0)
    (hxge_shift : x0 + i * 2 ^ Q ≤ x + i * 3 ^ oc * 2 ^ (Q - lc))
    (hadm_min : minCorrection x0 x ≥ 1 → (3 : ℕ) ^ oc > 2 ^ (lc + minCorrection x0 x - 1)) :
    markedVector (fuel + 1) (x0 + i * 2 ^ Q) (x + i * 3 ^ oc * 2 ^ (Q - lc)) =
      markedVector (fuel + 1) x0 x := by
  have hxeven' : Even x := Nat.even_iff.mpr (by omega)
  have hx1 : x > 1 := by
    obtain ⟨r, hr⟩ := hxeven'
    omega
  have hxpos : x ≠ 0 := by omega
  have hmc1 : minCorrection x0 x ≥ 1 := by
    have hne : ¬ (x < x0 ∨ x = 0) := by omega
    rw [minCorrection_eq]
    simp [hne]
  rw [markedVector_succ_even fuel x0 x hxeven,
    evenStep_spec x0 (by omega) x hxge hxeven', ite_eq_left hterm]
  have hshifted_even : (x + i * 3 ^ oc * 2 ^ (Q - lc)) % 2 ≠ 1 := by
    have hdvd2 : (2:ℕ) ∣ 2 ^ (Q - lc) := dvd_pow_self 2 (by omega)
    have hdvd3 : (2:ℕ) ∣ i * 3 ^ oc * 2 ^ (Q - lc) := hdvd2.mul_left _
    omega
  rw [markedVector_succ_even fuel (x0 + i * 2 ^ Q)
    (x + i * 3 ^ oc * 2 ^ (Q - lc)) hshifted_even]
  have hxeven'' : Even (x + i * 3 ^ oc * 2 ^ (Q - lc)) := by
    rw [Nat.even_iff]
    omega
  -- mc ≤ trailingZeros x
  have hmcle : minCorrection x0 x ≤ trailingZeros x := by
    by_contra hcon
    push Not at hcon
    have hpos : minCorrection x0 x ≥ 1 := by omega
    have hmin := minCorrection_min x0 x (by omega) hpos
    have hmono : x / 2 ^ (minCorrection x0 x - 1) ≤ x / 2 ^ (trailingZeros x) :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
    omega
  have hmcdvd : 2 ^ (trailingZeros x) ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
  have hmcdvd2 : 2 ^ (minCorrection x0 x) ∣ x := dvd_trans (pow_dvd_pow 2 hmcle) hmcdvd
  -- 2^mc divides the shifted x, so mc ≤ trailingZeros (shifted x)
  have hshiftdvd : 2 ^ (minCorrection x0 x) ∣ (x + i * 3 ^ oc * 2 ^ (Q - lc)) := by
    have h1 : (2:ℕ) ^ (minCorrection x0 x) ∣ i * 3 ^ oc * 2 ^ (Q - lc) :=
      (pow_dvd_pow 2 (by omega)).mul_left _
    exact Nat.dvd_add hmcdvd2 h1
  have hshiftpos : x + i * 3 ^ oc * 2 ^ (Q - lc) ≠ 0 := by omega
  have hmcleshift : minCorrection x0 x ≤ trailingZeros (x + i * 3 ^ oc * 2 ^ (Q - lc)) := by
    have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (padicValNat_dvd_iff_le hshiftpos).mp hshiftdvd
  -- the shifted x, halved trailingZeros (shifted x) times, is below the shifted start
  have hsuffshift : (x + i * 3 ^ oc * 2 ^ (Q - lc)) / 2 ^ (minCorrection x0 x) < x0 + i * 2 ^ Q :=
    minCorrection_shift_sufficiency x0 i Q x oc lc (minCorrection x0 x) hx0 hxge hlcQ hQrem
      hprefix rfl hmcdvd2
  have hcross_shift : (x + i * 3 ^ oc * 2 ^ (Q - lc)) /
      2 ^ (trailingZeros (x + i * 3 ^ oc * 2 ^ (Q - lc)))
      < x0 + i * 2 ^ Q := by
    have hmono : (x + i * 3 ^ oc * 2 ^ (Q - lc)) /
        2 ^ (trailingZeros (x + i * 3 ^ oc * 2 ^ (Q - lc))) ≤
        (x + i * 3 ^ oc * 2 ^ (Q - lc)) / 2 ^ (minCorrection x0 x) :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hmcleshift) (by positivity)
    omega
  rw [evenStep_spec (x0 + i * 2 ^ Q) (by omega) (x + i * 3 ^ oc * 2 ^ (Q - lc)) hxge_shift
    hxeven'', ite_eq_left hcross_shift]
  have hmceq : minCorrection (x0 + i * 2 ^ Q) (x + i * 3 ^ oc * 2 ^ (Q - lc)) =
      minCorrection x0 x :=
    minCorrection_shift_matches x0 i Q x oc lc (minCorrection x0 x) hx0 hxge hlcQ
      hQrem hprefix rfl hmcdvd2 hadm_min
  rw [hmceq]

/-- One step, even and continuing: the shifted start and value give the same
    entries, given the same for the tail (`htail`) and level ≥ 1 after the step
    (`hadm_next`). -/
theorem markedVector_shift_continue_even (x0 i Q x oc lc fuel : ℕ) (hx0 : x0 > 1)
    (hxge : x0 ≤ x) (hxeven : x % 2 ≠ 1) (hlcQ : lc ≤ Q)
    (hQrem : Q - lc ≥ trailingZeros x + 1) (hterm : ¬ (x / 2 ^ (trailingZeros x) < x0))
    (hxge_shift : x0 + i * 2 ^ Q ≤ x + i * 3 ^ oc * 2 ^ (Q - lc))
    (hadm_next : (2 : ℕ) ^ (lc + trailingZeros x) ≤ 3 ^ oc)
    (htail : markedVector fuel (x0 + i * 2 ^ Q)
        (x / 2 ^ (trailingZeros x) + i * 3 ^ oc * 2 ^ (Q - lc - trailingZeros x)) =
      markedVector fuel x0 (x / 2 ^ (trailingZeros x))) :
    markedVector (fuel + 1) (x0 + i * 2 ^ Q) (x + i * 3 ^ oc * 2 ^ (Q - lc)) =
      markedVector (fuel + 1) x0 x := by
  have hxeven' : Even x := Nat.even_iff.mpr (by omega)
  have hx1 : x > 1 := by
    obtain ⟨r, hr⟩ := hxeven'
    omega
  have hxpos : x ≠ 0 := by omega
  rw [markedVector_succ_even fuel x0 x hxeven,
    evenStep_spec x0 (by omega) x hxge hxeven', ite_eq_right hterm]
  have hshifted_even : (x + i * 3 ^ oc * 2 ^ (Q - lc)) % 2 ≠ 1 := by
    have hdvd2 : (2:ℕ) ∣ 2 ^ (Q - lc) := dvd_pow_self 2 (by omega)
    have hdvd3 : (2:ℕ) ∣ i * 3 ^ oc * 2 ^ (Q - lc) := hdvd2.mul_left _
    omega
  rw [markedVector_succ_even fuel (x0 + i * 2 ^ Q)
    (x + i * 3 ^ oc * 2 ^ (Q - lc)) hshifted_even]
  have hvshift : trailingZeros (x + i * 3 ^ oc * 2 ^ (Q - lc)) = trailingZeros x :=
    trailingZeros_shift x (i * 3 ^ oc) (Q - lc) hxpos (by omega)
  have hxeven'' : Even (x + i * 3 ^ oc * 2 ^ (Q - lc)) := by
    rw [Nat.even_iff]
    omega
  rw [evenStep_spec (x0 + i * 2 ^ Q) (by omega) (x + i * 3 ^ oc * 2 ^ (Q - lc)) hxge_shift
    hxeven'', hvshift]
  have hpoweq : (2:ℕ) ^ (Q - lc) = 2 ^ (trailingZeros x) * 2 ^ (Q - lc - trailingZeros x) := by
    rw [← pow_add]
    congr 1
    omega
  have hswap : i * 3 ^ oc * 2 ^ (Q - lc) =
      (i * 3 ^ oc * 2 ^ (Q - lc - trailingZeros x)) * 2 ^ (trailingZeros x) := by
    rw [hpoweq]
    ring
  have hxdvd : 2 ^ (trailingZeros x) ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
  have hexact : (x + i * 3 ^ oc * 2 ^ (Q - lc)) / 2 ^ (trailingZeros x) =
      x / 2 ^ (trailingZeros x) + i * 3 ^ oc * 2 ^ (Q - lc - trailingZeros x) := by
    rw [hswap]
    exact Nat.add_mul_div_right x (i * 3 ^ oc * 2 ^ (Q - lc - trailingZeros x)) (by positivity)
  have hterm_shift :
      ¬ (x + i * 3 ^ oc * 2 ^ (Q - lc)) / 2 ^ (trailingZeros x) < x0 + i * 2 ^ Q := by
    rw [hexact]
    have hstep1 : i * 2 ^ Q ≤ i * 3 ^ oc * 2 ^ (Q - lc - trailingZeros x) := by
      have hkey : (2:ℕ) ^ Q ≤ 3 ^ oc * 2 ^ (Q - lc - trailingZeros x) := by
        have heq2 : (2:ℕ) ^ Q = 2 ^ (lc + trailingZeros x) * 2 ^ (Q - lc - trailingZeros x) := by
          rw [← pow_add]
          congr 1
          omega
        rw [heq2]
        exact Nat.mul_le_mul_right _ hadm_next
      calc i * 2 ^ Q ≤ i * (3 ^ oc * 2 ^ (Q - lc - trailingZeros x)) := Nat.mul_le_mul_left i hkey
        _ = i * 3 ^ oc * 2 ^ (Q - lc - trailingZeros x) := by ring
    have hxtermge : x / 2 ^ (trailingZeros x) ≥ x0 := by omega
    omega
  rw [ite_eq_right hterm_shift, hexact]
  dsimp only
  congr 1

/-- Shift-invariance along the trajectory of an odd x0, by induction on the
    remaining fuel, with fuel1 steps done: if the decoded trajectory of x0 over
    totalFuel steps is admissible and ends within totalFuel steps, the entries
    from step fuel1 on are unchanged by the shift i*2^Q. -/
theorem markedVector_shift_from (x0 i Q totalFuel : ℕ) (hx0 : x0 > 1)
    (hx0odd : x0 % 2 = 1) (hsuff : (trajStats x0 totalFuel x0).2.2 < x0)
    (hAdm : Admissible (decodeVector (markedVector totalFuel x0 x0))) :
    ∀ fuel fuel1, fuel1 + fuel = totalFuel →
      x0 ≤ (trajStats x0 fuel1 x0).2.2 →
      (trajStats x0 fuel1 x0).2.1 ≤ Q →
      Q ≥ (trajStats x0 fuel1 x0).2.1 + (trajStats x0 fuel (trajStats x0 fuel1 x0).2.2).2.1 →
      (trajStats x0 fuel1 x0).2.2 * 2 ^ (trajStats x0 fuel1 x0).2.1 ≥
        x0 * 3 ^ (trajStats x0 fuel1 x0).1 →
      markedVector fuel (x0 + i * 2 ^ Q)
        ((trajStats x0 fuel1 x0).2.2 + i * 3 ^ (trajStats x0 fuel1 x0).1 *
          2 ^ (Q - (trajStats x0 fuel1 x0).2.1)) =
        markedVector fuel x0 (trajStats x0 fuel1 x0).2.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel1 _ _ _ _
    simp [markedVector]
  | succ fuel ih =>
    intro fuel1 hfueleq hxge hlcQ hbudget hprefix
    set x := (trajStats x0 fuel1 x0).2.2 with hx_def
    set oc := (trajStats x0 fuel1 x0).1 with hoc_def
    set lc := (trajStats x0 fuel1 x0).2.1 with hlc_def
    have hx1 : x > 1 := by omega
    have hfuel1ne0_of_even : x % 2 ≠ 1 → fuel1 ≠ 0 := by
      intro hxeven hfuel10
      rw [hfuel10] at hx_def
      simp only [trajStats] at hx_def
      omega
    have hAdm' : Admissible (decodeVector (markedVector (fuel1 + (fuel + 1)) x0 x0)) := by
      rw [hfueleq]
      exact hAdm
    have hAdm'' : Admissible (decodeVector (markedVector (fuel1 + 1 + fuel) x0 x0)) := by
      rw [show fuel1 + 1 + fuel = fuel1 + (fuel + 1) from by ring]
      exact hAdm'
    have hxge_shift : x0 + i * 2 ^ Q ≤ x + i * 3 ^ oc * 2 ^ (Q - lc) := by
      rcases Nat.eq_zero_or_pos fuel1 with hfuel10 | hfuel1pos
      · subst hfuel10
        simp only [trajStats] at hx_def hoc_def hlc_def
        rw [hx_def, hoc_def, hlc_def]
        simp
      · have hadm_cur : (2:ℕ) ^ lc < 3 ^ oc :=
          admissible_gives_prefix_lt x0 hx0 fuel1 (fuel + 1) hxge hfuel1pos (by omega) hAdm'
        have h1 : (x0 + i * 2 ^ Q) * 2 ^ lc ≤ x * 2 ^ lc + i * 3 ^ oc * 2 ^ Q := by
          have heq2 : i * 3 ^ oc * 2 ^ Q = i * 2 ^ lc * (3 ^ oc * 2 ^ (Q - lc)) := by
            have : (2:ℕ) ^ Q = 2 ^ lc * 2 ^ (Q - lc) := by
              rw [← pow_add]
              congr 1
              omega
            rw [this]
            ring
          have hstep : i * 2 ^ Q * 2 ^ lc ≤ i * 2 ^ lc * (3 ^ oc * 2 ^ (Q - lc)) := by
            have hb : (2:ℕ) ^ Q ≤ 3 ^ oc * 2 ^ (Q - lc) := by
              have heqQ : (2:ℕ) ^ Q = 2 ^ lc * 2 ^ (Q - lc) := by
                rw [← pow_add]
                congr 1
                omega
              rw [heqQ]
              exact Nat.mul_le_mul_right (2 ^ (Q - lc)) (le_of_lt hadm_cur)
            calc i * 2 ^ Q * 2 ^ lc = i * 2 ^ lc * 2 ^ Q := by ring
              _ ≤ i * 2 ^ lc * (3 ^ oc * 2 ^ (Q - lc)) := Nat.mul_le_mul_left _ hb
          have hxstep : x0 * 2 ^ lc ≤ x * 2 ^ lc := Nat.mul_le_mul_right _ hxge
          calc (x0 + i * 2 ^ Q) * 2 ^ lc = x0 * 2 ^ lc + i * 2 ^ Q * 2 ^ lc := by ring
            _ ≤ x * 2 ^ lc + i * 2 ^ lc * (3 ^ oc * 2 ^ (Q - lc)) := by omega
            _ = x * 2 ^ lc + i * 3 ^ oc * 2 ^ Q := by rw [← heq2]
        have h2 : (x + i * 3 ^ oc * 2 ^ (Q - lc)) * 2 ^ lc = x * 2 ^ lc + i * 3 ^ oc * 2 ^ Q := by
          have heq5 : (x + i * 3 ^ oc * 2 ^ (Q - lc)) * 2 ^ lc =
              x * 2 ^ lc + i * 3 ^ oc * (2 ^ (Q - lc) * 2 ^ lc) := by ring
          rw [heq5]
          congr 2
          rw [← pow_add]
          congr 1
          omega
        have h2lcpos : 0 < (2:ℕ) ^ lc := by positivity
        have hfin := h1
        rw [← h2] at hfin
        exact le_of_mul_le_mul_right hfin h2lcpos
    have hbudget' := hbudget
    simp only [trajStats] at hbudget'
    by_cases hxodd : x % 2 = 1
    · simp only [hxodd, ite_true] at hbudget'
      by_cases hterm : R x < x0
      · simp only [hterm, ite_true] at hbudget'
        exact markedVector_shift_terminal_odd x0 i Q x oc lc fuel hx0 hxge hxodd hlcQ
          (by omega) hprefix hterm
      · simp only [hterm, ite_false] at hbudget'
        have htrajstep : (trajStats x0 (fuel1 + 1) x0).1 = oc + trailingOnes x ∧
            (trajStats x0 (fuel1 + 1) x0).2.1 = lc + trailingOnes x + 1 ∧
            (trajStats x0 (fuel1 + 1) x0).2.2 = R x := by
          have hadd := trajStats_add x0 hx0 fuel1 1 x0 (le_refl x0) hxge
          have hone : trajStats x0 1 x = (trailingOnes x, trailingOnes x + 1, R x) := by
            simp only [trajStats, hxodd, ite_true, hterm, ite_false]
            simp
          rw [← hx_def] at hadd
          rw [hone] at hadd
          exact hadd
        obtain ⟨htraj1, htraj2, htraj3⟩ := htrajstep
        have hprefix2 : R x * 2 ^ (lc + trailingOnes x + 1) ≥ x0 * 3 ^ (oc + trailingOnes x) := by
          have hxOddP : Odd x := Nat.odd_iff.mpr hxodd
          have hRclosed : R x = (3 ^ trailingOnes x * ((x + 1) / 2 ^ trailingOnes x) - 1) / 2 :=
            R_odd_closed_form x hx1 hxOddP
          have hdvd : 2 ^ trailingOnes x ∣ (x + 1) := pow_trailingOnes_dvd x
          have hsmul : (x + 1) / 2 ^ trailingOnes x * 2 ^ trailingOnes x = x + 1 :=
            Nat.div_mul_cancel hdvd
          have hsOdd : Odd ((x + 1) / 2 ^ trailingOnes x) := odd_div_pow_trailingOnes x hxOddP
          have h3vsOdd : Odd (3 ^ trailingOnes x * ((x + 1) / 2 ^ trailingOnes x)) :=
            ((by decide : Odd 3).pow).mul hsOdd
          obtain ⟨k, hk⟩ := h3vsOdd
          have hexact : 2 * R x + 1 = 3 ^ trailingOnes x * ((x + 1) / 2 ^ trailingOnes x) := by
            rw [hRclosed, hk]
            omega
          have hkey : R x * 2 ^ (trailingOnes x + 1) + 2 ^ trailingOnes x =
              3 ^ trailingOnes x * x + 3 ^ trailingOnes x := by
            calc R x * 2 ^ (trailingOnes x + 1) + 2 ^ trailingOnes x =
                (2 * R x + 1) * 2 ^ trailingOnes x := by
                  rw [pow_succ]
                  ring
              _ = 3 ^ trailingOnes x * ((x + 1) / 2 ^ trailingOnes x) * 2 ^ trailingOnes x := by
                rw [hexact]
              _ = 3 ^ trailingOnes x * (((x + 1) / 2 ^ trailingOnes x) * 2 ^ trailingOnes x) := by
                ring
              _ = 3 ^ trailingOnes x * (x + 1) := by rw [hsmul]
              _ = 3 ^ trailingOnes x * x + 3 ^ trailingOnes x := by ring
          have hle32 : (2:ℕ) ^ trailingOnes x ≤ 3 ^ trailingOnes x :=
            Nat.pow_le_pow_left (by norm_num) _
          have hv2ge : R x * 2 ^ (trailingOnes x + 1) ≥ 3 ^ trailingOnes x * x := by omega
          have h1 : R x * 2 ^ (trailingOnes x + 1) * 2 ^ lc ≥ 3 ^ trailingOnes x * x * 2 ^ lc :=
            Nat.mul_le_mul_right _ hv2ge
          have h2 : 3 ^ trailingOnes x * x * 2 ^ lc ≥ 3 ^ trailingOnes x * (x0 * 3 ^ oc) := by
            have heq0 : 3 ^ trailingOnes x * x * 2 ^ lc = 3 ^ trailingOnes x * (x * 2 ^ lc) := by
              ring
            rw [heq0]
            exact Nat.mul_le_mul_left _ hprefix
          have heq1 : R x * 2 ^ (trailingOnes x + 1) * 2 ^ lc =
              R x * 2 ^ (lc + trailingOnes x + 1) := by
            rw [mul_assoc, ← pow_add]
            congr 2
            ring
          have heq2 : 3 ^ trailingOnes x * (x0 * 3 ^ oc) = x0 * 3 ^ (oc + trailingOnes x) := by
            rw [pow_add]
            ring
          omega
        have hg1 : x0 ≤ (trajStats x0 (fuel1 + 1) x0).2.2 := by
          rw [htraj3]
          omega
        have hg2 : (trajStats x0 (fuel1 + 1) x0).2.1 ≤ Q := by
          rw [htraj2]
          omega
        have hg3alt : Q ≥ (lc + trailingOnes x + 1) + (trajStats x0 fuel (R x)).2.1 := by
          have hb2 : (trajStats x0 (fuel + 1) x).2.1 =
              trailingOnes x + 1 + (trajStats x0 fuel (R x)).2.1 := by
            simp only [trajStats, hxodd, ite_true, hterm, ite_false]
          rw [hb2] at hbudget
          omega
        have hg3 : Q ≥ (trajStats x0 (fuel1 + 1) x0).2.1 +
            (trajStats x0 fuel (trajStats x0 (fuel1 + 1) x0).2.2).2.1 := by
          rw [htraj2, htraj3]
          exact hg3alt
        have hg4 : (trajStats x0 (fuel1 + 1) x0).2.2 * 2 ^ (trajStats x0 (fuel1 + 1) x0).2.1 ≥
            x0 * 3 ^ (trajStats x0 (fuel1 + 1) x0).1 := by
          rw [htraj1, htraj2, htraj3]
          exact hprefix2
        have hihcall := ih (fuel1 + 1) (by omega) hg1 hg2 hg3 hg4
        exact markedVector_shift_continue_odd x0 i Q x oc lc fuel hx0 hxge hxodd hlcQ
          (by omega) hterm
          (by
            have hnontermalt : R x ≥ x0 := by omega
            have hnonterm : (trajStats x0 (fuel1 + 1) x0).2.2 ≥ x0 := by
              rw [htraj3]
              exact hnontermalt
            have hfuelpos : fuel ≥ 1 := by
              by_contra hfuel0
              push Not at hfuel0
              interval_cases fuel
              have hTF : totalFuel = fuel1 + 1 := by omega
              have hsuff' := hsuff
              rw [hTF, htraj3] at hsuff'
              omega
            have hadm := admissible_gives_prefix_lt x0 hx0 (fuel1 + 1) fuel
              hnonterm (by omega) hfuelpos hAdm''
            exact htraj1 ▸ htraj2 ▸ hadm)
          (by
            have hthis := hihcall
            rw [htraj1, htraj2, htraj3] at hthis
            exact hthis)
    · simp only [hxodd, ite_false] at hbudget'
      have hfuel1pos : fuel1 ≥ 1 := by
        rcases Nat.eq_zero_or_pos fuel1 with h0 | hp
        · exact absurd h0 (hfuel1ne0_of_even hxodd)
        · exact hp
      have hadm_cur : (2:ℕ) ^ lc < 3 ^ oc :=
        admissible_gives_prefix_lt x0 hx0 fuel1 (fuel + 1) hxge hfuel1pos (by omega) hAdm'
      have hxeven : Even x := Nat.even_iff.mpr (by omega)
      by_cases hterm : x / 2 ^ (trailingZeros x) < x0
      · simp only [hterm, ite_true] at hbudget'
        have hQrem_ev : Q ≥ lc + minCorrection x0 x := by
          have hb2 : (trajStats x0 (fuel + 1) x).2.1 = minCorrection x0 x := by
            simp only [trajStats, hxodd, ite_false, hterm]
            simp
          rw [hb2] at hbudget
          omega
        exact markedVector_shift_terminal_even x0 i Q x oc lc fuel hx0 hxge hxodd hlcQ
          (by omega) hprefix hterm hxge_shift (by
            intro hmcpos
            by_cases hmc1 : minCorrection x0 x = 1
            · rw [hmc1]
              simpa using hadm_cur
            · have hmc2 : minCorrection x0 x ≥ 2 := by omega
              exact admissible_gives_even_terminal_minimality x0 hx0 fuel1 fuel hxge
                hxodd hterm hmc2 hAdm')
      · simp only [hterm, ite_false] at hbudget'
        have htrajstep : (trajStats x0 (fuel1 + 1) x0).1 = oc ∧
            (trajStats x0 (fuel1 + 1) x0).2.1 = lc + trailingZeros x ∧
            (trajStats x0 (fuel1 + 1) x0).2.2 = x / 2 ^ (trailingZeros x) := by
          have hadd := trajStats_add x0 hx0 fuel1 1 x0 (le_refl x0) hxge
          have hone : trajStats x0 1 x = (0, trailingZeros x, x / 2 ^ (trailingZeros x)) := by
            simp only [trajStats, hxodd, ite_false, hterm]
            simp
          rw [← hx_def] at hadd
          rw [hone] at hadd
          exact hadd
        obtain ⟨htraj1, htraj2, htraj3⟩ := htrajstep
        have hprefix2 : (x / 2 ^ (trailingZeros x)) * 2 ^ (lc + trailingZeros x) ≥ x0 * 3 ^ oc := by
          have hdvd : 2 ^ (trailingZeros x) ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
          obtain ⟨c, hc⟩ := hdvd
          have hxdiv : x / 2 ^ (trailingZeros x) = c := by
            nth_rewrite 1 [hc]
            have hpos : (0:ℕ) < 2 ^ trailingZeros x := by positivity
            exact Nat.mul_div_cancel_left c hpos
          rw [hxdiv]
          have heq : c * 2 ^ (lc + trailingZeros x) = x * 2 ^ lc := by
            have hcx : c * 2 ^ trailingZeros x = x := by
              rw [mul_comm]
              exact hc.symm
            calc c * 2 ^ (lc + trailingZeros x) = c * 2 ^ trailingZeros x * 2 ^ lc := by
                   rw [pow_add]
                   ring
              _ = x * 2 ^ lc := by rw [hcx]
          rw [heq]
          exact hprefix
        have hfuelpos : fuel ≥ 1 := by
          by_contra hfuel0
          push Not at hfuel0
          interval_cases fuel
          have hTF : totalFuel = fuel1 + 1 := by omega
          have hsuff' := hsuff
          rw [hTF, htraj3] at hsuff'
          omega
        have hremlen : (trajStats x0 fuel (x / 2 ^ (trailingZeros x))).2.1 ≥ 1 :=
          trajStats_length_ge_one x0 hx0 fuel (x / 2 ^ (trailingZeros x)) (by omega) hfuelpos
        have hg1 : x0 ≤ (trajStats x0 (fuel1 + 1) x0).2.2 := by
          rw [htraj3]
          omega
        have hg2 : (trajStats x0 (fuel1 + 1) x0).2.1 ≤ Q := by
          rw [htraj2]
          omega
        have hg3alt : Q ≥ (lc + trailingZeros x) +
            (trajStats x0 fuel (x / 2 ^ (trailingZeros x))).2.1 := by
          have hb2 : (trajStats x0 (fuel + 1) x).2.1 =
              trailingZeros x + (trajStats x0 fuel (x / 2 ^ (trailingZeros x))).2.1 := by
            simp only [trajStats, hxodd, ite_false, hterm]
          rw [hb2] at hbudget
          omega
        have hg3 : Q ≥ (trajStats x0 (fuel1 + 1) x0).2.1 +
            (trajStats x0 fuel (trajStats x0 (fuel1 + 1) x0).2.2).2.1 := by
          rw [htraj2, htraj3]
          exact hg3alt
        have hg4 : (trajStats x0 (fuel1 + 1) x0).2.2 * 2 ^ (trajStats x0 (fuel1 + 1) x0).2.1 ≥
            x0 * 3 ^ (trajStats x0 (fuel1 + 1) x0).1 := by
          rw [htraj1, htraj2, htraj3]
          exact hprefix2
        have hihcall := ih (fuel1 + 1) (by omega) hg1 hg2 hg3 hg4
        exact markedVector_shift_continue_even x0 i Q x oc lc fuel hx0 hxge hxodd hlcQ
          (by omega) hterm hxge_shift
          (by
            have hadm := admissible_gives_prefix_lt x0 hx0 (fuel1 + 1) fuel
              (by omega) (by omega) (by omega) hAdm''
            rw [htraj1, htraj2] at hadm
            omega)
          (by
            have hthis := hihcall
            rw [htraj1, htraj2, htraj3] at hthis
            have heqsub : Q - (lc + trailingZeros x) = Q - lc - trailingZeros x := by omega
            rw [heqsub] at hthis
            exact hthis)

/-- Shift-invariance of the marked vector of an odd x0 > 1 that drops, with
    admissible decoded trajectory: the same entries for x0 + i*2^Q, for Q at
    least the decoded length. The fuel is the least N at which x0 has dropped. -/
theorem markedVector_shift (x0 i Q : ℕ) (hx0 : x0 > 1) (hx0odd : x0 % 2 = 1)
    (hterm_exists : ∃ N, (trajStats x0 N x0).2.2 < x0)
    (hAdm : Admissible (decodeVector (markedVector (Nat.find hterm_exists) x0 x0)))
    (hQrem : Q ≥ (trajStats x0 (Nat.find hterm_exists) x0).2.1) :
    markedVector (Nat.find hterm_exists) (x0 + i * 2 ^ Q) (x0 + i * 2 ^ Q) =
      markedVector (Nat.find hterm_exists) x0 x0 := by
  set N := Nat.find hterm_exists with hN_def
  have hsuff : (trajStats x0 N x0).2.2 < x0 := Nat.find_spec hterm_exists
  have hmain := markedVector_shift_from x0 i Q N hx0 hx0odd hsuff hAdm N 0 (by omega)
    (by simp [trajStats]) (by simp [trajStats]) (by simpa [trajStats] using hQrem)
    (by simp [trajStats])
  simpa [trajStats] using hmain

end AcceleratedCollatz
