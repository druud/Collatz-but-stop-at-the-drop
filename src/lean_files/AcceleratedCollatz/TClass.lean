-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.MarkedVectorShift
import AcceleratedCollatz.TBridge
import AcceleratedCollatz.TDrop

/-!
  Class-id direction of sec:sorting. For an admissible s and x with
  tBits x |s| = s and rho s < d_23 s * x: x's marked
  vector terminates within |s| steps and decodes to s. Consequences: shift
  invariance of the marked vector without an admissibility hypothesis, and
  injectivity (x determines its admissible s).
-/

namespace AcceleratedCollatz

variable (s : List Bool)

theorem tStep_pos (y : ℕ) (h : 0 < y) : 0 < tStep y := by
  by_cases hy : y % 2 = 1
  · rw [tStep_odd y hy]
    omega
  · rw [tStep_even y hy]
    omega

theorem tStep_iterate_pos (n y : ℕ) (h : 0 < y) : 0 < tStep^[n] y := by
  induction n with
  | zero =>
    simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact tStep_pos _ ih

/-- A trajectory that has not terminated consumed at least one bit per step. -/
theorem trajStats_length_ge_fuel (x0 : ℕ) (hx0 : x0 > 1) :
    ∀ fuel x, x0 ≤ x → x0 ≤ (trajStats x0 fuel x).2.2 → fuel ≤ (trajStats x0 fuel x).2.1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro x _ _
    simp [trajStats]
  | succ fuel ih =>
    intro x hxge hnt
    have hx1 : x > 1 := by omega
    unfold trajStats at hnt ⊢
    by_cases hxodd : x % 2 = 1
    · simp only [hxodd, ↓reduceIte] at hnt ⊢
      by_cases hR : R x < x0
      · simp only [hR, ↓reduceIte] at hnt
        omega
      · simp only [hR, ↓reduceIte] at hnt ⊢
        have := ih (R x) (by omega) hnt
        change fuel + 1 ≤ trailingOnes x + 1 + (trajStats x0 fuel (R x)).2.1
        omega
    · simp only [hxodd, ↓reduceIte] at hnt ⊢
      by_cases hE : x / 2 ^ trailingZeros x < x0
      · simp only [hE, ↓reduceIte] at hnt
        have := minCorrection_suff x0 x (by omega)
        omega
      · simp only [hE, ↓reduceIte] at hnt ⊢
        have hv1 : trailingZeros x ≥ 1 := by
          have hxeven : Even x := Nat.even_iff.mpr (by omega)
          obtain ⟨r, hr⟩ := hxeven
          exact one_le_padicValNat_of_dvd (by omega) ⟨r, by omega⟩
        have := ih (x / 2 ^ trailingZeros x) (by omega) hnt
        change fuel + 1 ≤ trailingZeros x + (trajStats x0 fuel (x / 2 ^ trailingZeros x)).2.1
        omega

theorem one_lt_of_class (x : ℕ) (h : ClassCond s x) : 1 < x := by
  have hdrop := (first_drop_at_length s x h).2
  have hpos := tStep_iterate_pos s.length x h.pos
  omega

theorem odd_of_class (x : ℕ) (hA : Admissible s) (hord : 1 ≤ order s)
    (hs : tBits x s.length = s) : x % 2 = 1 := by
  have h32 : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have hle := order_le_length s
  have hlen : 2 ≤ s.length := by
    by_contra hlt
    have ho : order s = 1 := by omega
    have hl : s.length = 1 := by omega
    rw [ho, hl] at h32
    norm_num at h32
  have hp := hA.prefix_gt 1 le_rfl (by omega)
  rw [one_lt_seqProduct_iff] at hp
  have htake : s.take 1 = tBits x 1 := by
    rw [← hs]
    exact tBits_take x s.length 1 (by omega)
  rw [htake] at hp
  by_contra hodd
  simp [tBits, order, hodd] at hp

/-- Class ids terminate within |s| macro-steps. -/
theorem terminates_of_class (x : ℕ) (h : ClassCond s x) :
    (trajStats x s.length x).2.2 < x := by
  have hx1 := one_lt_of_class s x h
  have hdrop := (first_drop_at_length s x h).2
  by_contra hge
  push Not at hge
  have hL := trajStats_length_ge_fuel x hx1 s.length x le_rfl hge
  have hlen := length_decodeVector_eq_trajStats x hx1 s.length x le_rfl
  obtain ⟨_, hb, hc⟩ := traceOK_markedVector x hx1 s.length x le_rfl
  rw [hlen] at hb hc
  have hge' : x ≤ tStep^[s.length] x := by
    rcases Nat.lt_or_ge s.length (trajStats x s.length x).2.1 with hlt | hge2
    · exact hc s.length hlt
    · have heq : s.length = (trajStats x s.length x).2.1 := by omega
      rw [heq, hb]
      exact hge
  omega

/-- Class ids decode to their own sequence, at any terminating fuel. -/
theorem decodeVector_eq_of_class (x fuel : ℕ) (h : ClassCond s x)
    (hterm : (trajStats x fuel x).2.2 < x) :
    decodeVector (markedVector fuel x x) = s := by
  have hx1 := one_lt_of_class s x h
  obtain ⟨hnodrop, hdrop⟩ := first_drop_at_length s x h
  obtain ⟨ha, hb, hc⟩ := traceOK_markedVector x hx1 fuel x le_rfl
  rw [← hb] at hterm
  have hL : (decodeVector (markedVector fuel x x)).length = s.length := by
    rcases Nat.lt_trichotomy (decodeVector (markedVector fuel x x)).length s.length
      with hlt | heq | hgt
    · rcases Nat.eq_zero_or_pos (decodeVector (markedVector fuel x x)).length
        with h0 | hpos
      · rw [h0] at hterm
        simp at hterm
      · have := hnodrop _ hpos hlt
        omega
    · exact heq
    · have := hc s.length hgt
      omega
  rw [← ha, hL, h.bits]

/-- Class-id conditions are invariant under x ↦ x + i 2^Q, Q ≥ |s|. -/
theorem class_shift (x i Q : ℕ) (hQ : s.length ≤ Q)
    (hs : tBits x s.length = s) (hd : rho s < d_23 s * x) :
    tBits (x + i * 2 ^ Q) s.length = s ∧
      rho s < d_23 s * (x + i * 2 ^ Q) := by
  constructor
  · rw [tBits_eq_iff] at hs ⊢
    have hQdvd : 2 ^ s.length ∣ 2 ^ Q := pow_dvd_pow 2 hQ
    have hsplit : 3 ^ order s * (x + i * 2 ^ Q) + rho s =
        (3 ^ order s * x + rho s) + 3 ^ order s * i * 2 ^ Q := by
      ring
    rw [hsplit]
    exact dvd_add hs (hQdvd.mul_left _)
  · calc rho s < d_23 s * x := hd
      _ ≤ d_23 s * (x + i * 2 ^ Q) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

/-- markedVector_shift with its admissibility hypothesis discharged. -/
theorem markedVector_shift_of_class (x i Q : ℕ) (h : ClassCond s x)
    (hord : 1 ≤ order s) (hQ : s.length ≤ Q) :
    ∃ hterm : ∃ N, (trajStats x N x).2.2 < x,
      markedVector (Nat.find hterm) (x + i * 2 ^ Q) (x + i * 2 ^ Q) =
        markedVector (Nat.find hterm) x x := by
  have hx1 := one_lt_of_class s x h
  have hex : ∃ N, (trajStats x N x).2.2 < x := ⟨s.length, terminates_of_class s x h⟩
  have hdec := decodeVector_eq_of_class s x (Nat.find hex) h (Nat.find_spec hex)
  have hlen := length_decodeVector_eq_trajStats x hx1 (Nat.find hex) x le_rfl
  refine ⟨hex, ?_⟩
  apply markedVector_shift x i Q hx1 (odd_of_class s x h.adm hord h.bits) hex
  · rw [hdec]
    exact h.adm
  · rw [← hlen, hdec]
    exact hQ

/-- x determines its admissible parity sequence. -/
theorem class_injective (s s' : List Bool) (x : ℕ) (hA : Admissible s) (hA' : Admissible s')
    (hs : tBits x s.length = s) (hs' : tBits x s'.length = s') : s = s' := by
  by_contra hne
  rcases le_total s.length s'.length with hle | hle
  · have hpre : s <+: s' := by
      rw [← hs, ← tBits_take x s'.length s.length hle, hs']
      exact List.take_prefix _ _
    exact admissible_not_prefix s s' hA hA' hne hpre
  · have hpre : s' <+: s := by
      rw [← hs', ← tBits_take x s.length s'.length hle, hs]
      exact List.take_prefix _ _
    exact admissible_not_prefix s' s hA' hA (Ne.symm hne) hpre

end AcceleratedCollatz
