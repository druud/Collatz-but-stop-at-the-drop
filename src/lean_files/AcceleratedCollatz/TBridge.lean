-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.MarkedVector
import AcceleratedCollatz.TParity

/-!
  Bridge between the marked-vector encoding and T-parity bits. For x0 > 1
  whose trajectory terminates within the given fuel, the decoded
  `markedVector fuel x0 x0` equals x0's first L T-parity bits
  (L = its length), T^L(x0) is the drop value, and T^m(x0) ≥ x0 for m < L.
-/

namespace AcceleratedCollatz

/-- x's first |B| T-parity bits are B, T^|B|(x) = d, and no value before
    position |B| is below x0. -/
def TraceOK (x0 x : ℕ) (B : List Bool) (d : ℕ) : Prop :=
  tBits x B.length = B ∧ tStep^[B.length] x = d ∧ ∀ m < B.length, x0 ≤ tStep^[m] x

theorem traceOK_append (x0 x x' d : ℕ) (P B : List Bool)
    (hP : TraceOK x0 x P x') (hB : TraceOK x0 x' B d) :
    TraceOK x0 x (P ++ B) d := by
  obtain ⟨hPa, hPb, hPc⟩ := hP
  obtain ⟨hBa, hBb, hBc⟩ := hB
  have hsplit : ∀ m, tStep^[P.length + m] x = tStep^[m] x' := by
    intro m
    rw [Nat.add_comm, Function.iterate_add_apply, hPb]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, tBits_add, hPa, hPb, hBa]
  · rw [List.length_append, hsplit, hBb]
  · intro m hm
    rw [List.length_append] at hm
    by_cases hmP : m < P.length
    · exact hPc m hmP
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hmP)
      rw [hsplit]
      exact hBc m' (by omega)

/-- One odd macro-step: v ones and a zero, ending at R x. -/
theorem traceOK_odd (x0 x : ℕ) (hx1 : x > 1) (hxodd : x % 2 = 1) (hxge : x0 ≤ x) :
    TraceOK x0 x (List.replicate (trailingOnes x) true ++ [false]) (R x) := by
  have hxOdd : Odd x := Nat.odd_iff.mpr hxodd
  have hdvd : 2 ^ trailingOnes x ∣ x + 1 := pow_trailingOnes_dvd x
  have hsm : x + 1 = 2 ^ trailingOnes x * ((x + 1) / 2 ^ trailingOnes x) :=
    (Nat.mul_div_cancel' hdvd).symm
  have hsOdd : Odd ((x + 1) / 2 ^ trailingOnes x) := odd_div_pow_trailingOnes x hxOdd
  have hrun := tStep_iterate_odd_run x (trailingOnes x) ((x + 1) / 2 ^ trailingOnes x) hsm
  have hend : tStep^[trailingOnes x] x + 1 =
      3 ^ trailingOnes x * ((x + 1) / 2 ^ trailingOnes x) := by
    grind
  have hendOdd : (3 ^ trailingOnes x * ((x + 1) / 2 ^ trailingOnes x)) % 2 = 1 :=
    Nat.odd_iff.mp (((by decide : Odd 3).pow).mul hsOdd)
  have hRx : R x = (3 ^ trailingOnes x * ((x + 1) / 2 ^ trailingOnes x) - 1) / 2 :=
    R_odd_closed_form x hx1 hxOdd
  have hlen : (List.replicate (trailingOnes x) true ++ [false]).length = trailingOnes x + 1 := by
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hlen, tBits_add]
    have hrep : tBits x (trailingOnes x) = List.replicate (trailingOnes x) true := by
      apply tBits_replicate true
      intro k hk
      have hk' := hrun k hk.le
      have hv : 2 ^ (trailingOnes x - k) = 2 * 2 ^ (trailingOnes x - (k + 1)) := by
        rw [← pow_succ']
        grind
      rw [hv] at hk'
      grind
    rw [hrep]
    simp only [tBits, List.append_cancel_left_eq, List.cons.injEq, and_true]
    grind
  · have heven : tStep^[trailingOnes x] x % 2 ≠ 1 := by omega
    rw [hlen, Function.iterate_succ_apply', hRx, tStep_even _ heven]
    omega
  · intro m hm
    rw [hlen] at hm
    have hm' := hrun m (by omega)
    have h23 : 2 ^ trailingOnes x ≤ 3 ^ m * 2 ^ (trailingOnes x - m) := by
      have hsplit : 2 ^ trailingOnes x = 2 ^ m * 2 ^ (trailingOnes x - m) := by
        rw [← pow_add]
        grind
      rw [hsplit]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) m)
    have hge : x + 1 ≤ tStep^[m] x + 1 := by
      rw [hm']
      calc x + 1 = 2 ^ trailingOnes x * ((x + 1) / 2 ^ trailingOnes x) := hsm
        _ ≤ 3 ^ m * 2 ^ (trailingOnes x - m) * ((x + 1) / 2 ^ trailingOnes x) :=
          Nat.mul_le_mul_right _ h23
    omega

/-- k halvings of x (2^k ∣ x), all intermediate values ≥ x0. -/
theorem traceOK_even (x0 x k : ℕ) (h : 2 ^ k ∣ x) (hmono : ∀ m < k, x0 ≤ x / 2 ^ m) :
    TraceOK x0 x (List.replicate k false) (x / 2 ^ k) := by
  have hit := tStep_iterate_of_pow_dvd x k h
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_replicate]
    apply tBits_replicate false
    intro j hj
    rw [hit j hj.le, div_pow_even x j k hj h]
    simp
  · rw [List.length_replicate]
    exact hit k le_rfl
  · grind

/-- Decoded marked vector from x = T-parity bits of x up to trajStats's
    endpoint (drop value, or current value if fuel runs out). -/
theorem traceOK_markedVector (x0 : ℕ) (hx0 : x0 > 1) :
    ∀ fuel x, x0 ≤ x →
      TraceOK x0 x (decodeVector (markedVector fuel x0 x)) (trajStats x0 fuel x).2.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro x _
    refine ⟨?_, ?_, ?_⟩
    · simp [markedVector, decodeVector, tBits]
    · simp [markedVector, decodeVector, trajStats]
    · simp [markedVector, decodeVector]
  | succ fuel ih =>
    intro x hxge
    have hx1 : x > 1 := by omega
    by_cases hxodd : x % 2 = 1
    · have hv1 : 1 ≤ trailingOnes x := by
        have hxOdd : Odd x := Nat.odd_iff.mpr hxodd
        obtain ⟨j, hj⟩ := hxOdd
        exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
      have hstep := traceOK_odd x0 x hx1 hxodd hxge
      rw [markedVector_succ_odd fuel x0 x hxodd]
      unfold trajStats
      simp only [hxodd, ↓reduceIte]
      by_cases hR : R x < x0
      · simp only [hR, ↓reduceIte]
        rw [markedEntry_true, decodeVector_singleton, expandEntry_natCast _ hv1]
        exact hstep
      · simp only [hR, ↓reduceIte]
        rw [markedEntry_true, decodeVector_cons, expandEntry_natCast _ hv1]
        exact traceOK_append x0 x (R x) _ _ _ hstep (ih (R x) (by omega))
    · have hxeven : Even x := Nat.even_iff.mpr (by omega)
      have hdvd : 2 ^ trailingZeros x ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
      have hxne : x ≠ 0 := by omega
      rw [markedVector_succ_even fuel x0 x hxodd,
        evenStep_spec x0 (by omega) x hxge hxeven]
      unfold trajStats
      simp only [hxodd, ↓reduceIte]
      by_cases hE : x / 2 ^ trailingZeros x < x0
      · simp only [hE, ↓reduceIte]
        rw [markedEntry_false, decodeVector_singleton, expandEntry_neg_natCast]
        have hmc1 : minCorrection x0 x ≥ 1 := by
          rw [minCorrection_eq]
          grind
        have hmcmin := minCorrection_min x0 x (by omega) hmc1
        have hmcle : minCorrection x0 x ≤ trailingZeros x := by
          by_contra hgt
          have hle : x / 2 ^ (minCorrection x0 x - 1) ≤ x / 2 ^ trailingZeros x :=
            Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
          omega
        apply traceOK_even x0 x _ ((pow_dvd_pow 2 hmcle).trans hdvd)
        intro m hm
        have hle : x / 2 ^ (minCorrection x0 x - 1) ≤ x / 2 ^ m :=
          Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
        omega
      · simp only [hE, ↓reduceIte]
        rw [markedEntry_false, decodeVector_cons, expandEntry_neg_natCast]
        have hstep : TraceOK x0 x (List.replicate (trailingZeros x) false)
            (x / 2 ^ trailingZeros x) := by
          apply traceOK_even x0 x _ hdvd
          intro m hm
          have hle : x / 2 ^ trailingZeros x ≤ x / 2 ^ m :=
            Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hm.le) (by positivity)
          omega
        exact traceOK_append x0 x _ _ _ _ hstep (ih _ (by omega))

/-- x0's decoded marked vector s: x0 has T-parity bits s, drops at |s|, and
    stays ≥ x0 before. -/
theorem decodeVector_eq_tBits (x0 fuel : ℕ) (hx0 : x0 > 1)
    (hterm : (trajStats x0 fuel x0).2.2 < x0) :
    tBits x0 (decodeVector (markedVector fuel x0 x0)).length =
        decodeVector (markedVector fuel x0 x0) ∧
      tStep^[(decodeVector (markedVector fuel x0 x0)).length] x0 < x0 ∧
      ∀ m < (decodeVector (markedVector fuel x0 x0)).length, x0 ≤ tStep^[m] x0 := by
  obtain ⟨ha, hb, hc⟩ := traceOK_markedVector x0 hx0 fuel x0 le_rfl
  exact ⟨ha, hb ▸ hterm, hc⟩

end AcceleratedCollatz
