-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRulerDeficit
import AcceleratedCollatz.TWidthRecord

/-!
  The ruler gap as one deficit inequality per pair of neighbouring record Orders.
  For neighbouring upper record Orders b < b', let c be the largest upper record Order
  ≤ b + b'; for neighbouring lower record Orders P < P', let c be the largest lower record
  Order < P + P'. Over the window of a step (`upperTiming_at_iff_next`,
  `lowerTiming_at_iff_next`) the block factor is largest at c (upper) or smallest at c
  (lower), and c splits with b (adds with P); so the deficit inequality of the window holds
  for some v exactly when it holds at c (`UpperDeficitLt`, `LowerDeficitLt`).
  `RulerGap` is the failure of these inequalities at every pair (`rulerGap_iff_pairs`); at
  one record Order the pairs from it give its deficit condition (`upper_deficit_of_pairs`,
  `lower_deficit_of_pairs`).
-/

namespace AcceleratedCollatz

/-- The deficit inequality of an upper step from b, at K:
    d(K) 4^p2(b) < d(b)^2 2^p2(K) with d(n) = 2^p2(n) - 3^n. -/
def UpperDeficitLt (b K : ℕ) : Prop :=
  ((2 : ℤ) ^ p2_of K - 3 ^ K) * 4 ^ p2_of b < ((2 : ℤ) ^ p2_of b - 3 ^ b) ^ 2 * 2 ^ p2_of K

/-- The deficit inequality of a lower step from P, at K:
    (2·3^K - 2^p2(K)) (4·3^P - 2^p2(P)) 2^p2(P) < (2·3^P - 2^p2(P))^2 2^p2(K). -/
def LowerDeficitLt (P K : ℕ) : Prop :=
  (2 * (3 : ℤ) ^ K - 2 ^ p2_of K) * (4 * 3 ^ P - 2 ^ p2_of P) * 2 ^ p2_of P <
    (2 * (3 : ℤ) ^ P - 2 ^ p2_of P) ^ 2 * 2 ^ p2_of K

/-! ### Exact facts on p2 and the block factor -/

/-- 2^p2(n) ≤ 2·3^n. -/
theorem two_pow_p2_of_le (n : ℕ) : (2 : ℤ) ^ p2_of n ≤ 2 * 3 ^ n := by
  have h := p2_of_spec_lower n
  have h1 := one_le_p2_of n
  have e : 2 ^ p2_of n = 2 * 2 ^ (p2_of n - 1) := by
    rw [← pow_succ']
    congr 1
  have hn : 2 ^ p2_of n ≤ 2 * 3 ^ n := by
    omega
  exact_mod_cast hn

/-- v ≤ n when p2(v) ≤ p2(n). -/
theorem le_of_p2_of_le {v n : ℕ} (h : p2_of v ≤ p2_of n) : v ≤ n := by
  have h1 := p2_of_spec v
  have h2 := p2_of_spec_lower n
  have h3 := one_le_p2_of n
  have e : 2 ^ p2_of n = 2 * 2 ^ (p2_of n - 1) := by
    rw [← pow_succ']
    congr 1
  have h4 : 2 ^ p2_of v ≤ 2 ^ p2_of n := Nat.pow_le_pow_right (by norm_num) h
  have h5 : 3 ^ v < 3 ^ (n + 1) := by
    rw [pow_succ]
    omega
  exact Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h5)

/-- f(x) ≤ f(y) for the block factor, as cross products in the integers. -/
theorem blockFactor_le_iff_int {x y : ℕ} :
    blockFactor x ≤ blockFactor y ↔ (3 : ℤ) ^ x * 2 ^ p2_of y ≤ 3 ^ y * 2 ^ p2_of x := by
  rw [blockFactor_eq, blockFactor_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast

/-! ### Records below a given Order -/

/-- Every Order n ≥ 1 has a lower record Order r ≤ n with f(r) ≤ f(n). -/
theorem exists_lowerRecord_le :
    ∀ n : ℕ, 1 ≤ n → ∃ r, 1 ≤ r ∧ r ≤ n ∧ LowerRecord r ∧ blockFactor r ≤ blockFactor n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : LowerRecord n
    · exact ⟨n, hn, le_rfl, h, le_rfl⟩
    · rw [lowerRecord_iff_blockFactor] at h
      push Not at h
      obtain ⟨a, ha1, han, hfa⟩ := h
      obtain ⟨r, hr1, hra, hRr, hfr⟩ := ih a han ha1
      exact ⟨r, hr1, by omega, hRr, hfr.trans hfa⟩

/-- With no lower record Order in (c, X]: f(c) ≤ f(K) for 1 ≤ K ≤ X. -/
theorem blockFactor_ge_of_lowerRecord {c X K : ℕ} (hc : LowerRecord c)
    (hnone : ∀ x, c < x → x ≤ X → ¬LowerRecord x) (hK1 : 1 ≤ K) (hKX : K ≤ X) :
    blockFactor c ≤ blockFactor K := by
  obtain ⟨r, hr1, hrK, hRr, hfr⟩ := exists_lowerRecord_le K hK1
  have hrc : r ≤ c := by
    by_contra h
    exact hnone r (by omega) (by omega) hRr
  rcases Nat.lt_or_ge r c with h | h
  · exact ((lowerRecord_iff_blockFactor c).mp hc r hr1 h).le.trans hfr
  · have e : r = c := by omega
    rw [← e]
    exact hfr

/-- The least Order above b with property R. -/
theorem exists_least_above {R : ℕ → Prop} {b : ℕ} (hex : ∃ x, b < x ∧ R x) :
    ∃ b', b < b' ∧ R b' ∧ ∀ x, b < x → x < b' → ¬R x := by
  classical
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  exact ⟨Nat.find hex, h1, h2, fun x hx hxb hRx => Nat.find_min hex hxb ⟨hx, hRx⟩⟩

/-- The largest Order ≤ X with property R, given one at lo ≤ X. -/
theorem exists_greatest_le {R : ℕ → Prop} {lo X : ℕ} (hlo : R lo) (hle : lo ≤ X) :
    ∃ c, lo ≤ c ∧ c ≤ X ∧ R c ∧ ∀ x, c < x → x ≤ X → ¬R x := by
  classical
  exact ⟨Nat.findGreatest R X, Nat.le_findGreatest hle hlo, Nat.findGreatest_le X,
    Nat.findGreatest_spec hle hlo, fun x hx hxX => Nat.findGreatest_is_greatest hx hxX⟩

/-! ### The inequalities in the integers -/

/-- The upper inequality moves from K to an Order c with f(K) ≤ f(c)
    (A = 2^p2(K), B = 3^K, C = 2^p2(c), E = 3^c). -/
theorem upper_deficit_transfer (A B C E F G : ℤ) (hA : 0 < A) (hC : 0 < C) (hF : 0 ≤ F)
    (hf : B * C ≤ E * A) (h : (A - B) * F < G * A) : (C - E) * F < G * C := by
  have key : C * ((A - B) * F) - (C - E) * F * A = F * (E * A - B * C) := by
    ring
  have h1 : 0 ≤ F * (E * A - B * C) := mul_nonneg hF (by linarith)
  have h2 : C * ((A - B) * F) < C * (G * A) := mul_lt_mul_of_pos_left h hC
  have e : C * (G * A) = G * C * A := by
    ring
  have h3 : (C - E) * F * A < G * C * A := by
    linarith
  exact lt_of_mul_lt_mul_right h3 hA.le

/-- The lower inequality moves from K to an Order c with f(c) ≤ f(K)
    (A = 2^p2(K), B = 3^K, C = 2^p2(c), E = 3^c). -/
theorem lower_deficit_transfer (A B C E H Y G : ℤ) (hA : 0 < A) (hC : 0 < C) (hH : 0 ≤ H)
    (hY : 0 ≤ Y) (hf : E * A ≤ B * C) (h : (2 * B - A) * H * Y < G * A) :
    (2 * E - C) * H * Y < G * C := by
  have key : C * ((2 * B - A) * H * Y) - (2 * E - C) * H * Y * A =
      2 * (H * Y) * (B * C - E * A) := by
    ring
  have h1 : 0 ≤ 2 * (H * Y) * (B * C - E * A) :=
    mul_nonneg (by positivity) (by linarith)
  have h2 : C * ((2 * B - A) * H * Y) < C * (G * A) := mul_lt_mul_of_pos_left h hC
  have e : C * (G * A) = G * C * A := by
    ring
  have h3 : (2 * E - C) * H * Y * A < G * C * A := by
    linarith
  exact lt_of_mul_lt_mul_right h3 hA.le

/-- No upper inequality at K when f(K) ≤ f(b) (A = 2^p2(K), B = 3^K, T = 3^b, Y = 2^p2(b)). -/
theorem not_upper_deficit_of_le (A B T Y : ℤ) (hA : 0 < A) (hT : 0 < T) (hTY : T < Y)
    (hf : B * Y ≤ T * A) : ¬((A - B) * (Y * Y) < (Y - T) ^ 2 * A) := by
  intro h
  have h1 : (Y - T) * A ≤ (A - B) * Y := by
    linarith
  have h2 : (Y - T) * A * Y ≤ (A - B) * Y * Y := mul_le_mul_of_nonneg_right h1 (by linarith)
  have hp : 0 < (Y - T) * A := mul_pos (by linarith) hA
  have key : (Y - T) * A * Y - (Y - T) ^ 2 * A = (Y - T) * A * T := by
    ring
  have h3 : 0 < (Y - T) * A * T := mul_pos hp hT
  linarith

/-- No lower inequality at K when f(P) ≤ f(K) (A = 2^p2(K), B = 3^K, T = 3^P, Y = 2^p2(P)). -/
theorem not_lower_deficit_of_le (A B T Y : ℤ) (hA : 0 < A) (hY : 0 < Y) (hYT : Y ≤ 2 * T)
    (hf : T * A ≤ B * Y) : ¬((2 * B - A) * (4 * T - Y) * Y < (2 * T - Y) ^ 2 * A) := by
  intro h
  have h1 : (2 * T - Y) * A ≤ (2 * B - A) * Y := by
    linarith
  have h2 : (2 * T - Y) * A * (4 * T - Y) ≤ (2 * B - A) * Y * (4 * T - Y) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have key : (2 * T - Y) * A * (4 * T - Y) - (2 * T - Y) ^ 2 * A = (2 * T - Y) * A * (2 * T) := by
    ring
  have h3 : 0 ≤ (2 * T - Y) * A * (2 * T) :=
    mul_nonneg (mul_nonneg (by linarith) hA.le) (by linarith)
  linarith

/-! ### The ruler gap by pairs -/

/-- The upper deficit condition at an upper record Order b, from the pair condition at b. -/
theorem upper_deficit_of_pairs {b v : ℕ}
    (hU : ∀ b' c : ℕ, 1 ≤ b → b < b' → UpperRecord b' →
      (∀ x, b < x → x < b' → ¬UpperRecord x) → b' ≤ c → c ≤ b + b' → UpperRecord c →
      (∀ x, c < x → x ≤ b + b' → ¬UpperRecord x) → ¬UpperDeficitLt b c)
    (hR : UpperRecord b) (hv : 1 ≤ v) (ht : UpperTiming b (p2_of v - 1 - p2_of b)) :
    ¬(p2_of (b + v) + 1 = p2_of b + p2_of v ∧
      ((2 : ℤ) ^ p2_of (b + v) - 3 ^ (b + v)) * 4 ^ p2_of b <
        ((2 : ℤ) ^ p2_of b - 3 ^ b) ^ 2 * 2 ^ p2_of (b + v)) := by
  rintro ⟨_, hd⟩
  have hY := p2_of_spec b
  have hYint : (3 : ℤ) ^ b < 2 ^ p2_of b := by
    exact_mod_cast hY
  have h4 : (4 : ℤ) ^ p2_of b = 2 ^ p2_of b * 2 ^ p2_of b := by
    rw [← mul_pow]
    norm_num
  rcases Nat.eq_zero_or_pos b with h0 | hb
  · subst h0
    have p20 : p2_of 0 = 1 := by
      unfold p2_of
      simp
    have p21 : p2_of 1 = 2 := by
      unfold p2_of
      decide
    rcases Nat.lt_or_ge v 2 with hv2 | hv2
    · have e : v = 1 := by
        omega
      subst e
      rw [Nat.zero_add, p20, p21] at hd
      norm_num at hd
    · have h9 : 2 ^ 3 ≤ 3 ^ v := by
        have : 3 ^ 2 ≤ 3 ^ v := Nat.pow_le_pow_right (by norm_num) hv2
        omega
      have h3 := lt_p2_of_two_pow_le h9
      have hc := ht 1 le_rfl (by omega)
      rw [p20, p21] at hc
      norm_num at hc
  · by_cases hex : ∃ x, b < x ∧ UpperRecord x
    · obtain ⟨b', hbb, hR', hn⟩ := exists_least_above hex
      have hvb := le_of_p2_of_le ((upperTiming_at_iff_next hb hbb hR hR' hn).mp ht)
      obtain ⟨c, hbc, hcX, hRc, hcmax⟩ :=
        exists_greatest_le (R := UpperRecord) hR' (show b' ≤ b + b' by omega)
      have hfc := blockFactor_le_iff_int.mp
        (blockFactor_le_of_upperRecord hRc hcmax (b + v) (by omega) (by omega))
      apply hU b' c hb hbb hR' hn hbc hcX hRc hcmax
      exact upper_deficit_transfer _ _ _ _ _ _ (by positivity) (by positivity)
        (by positivity) hfc hd
    · have hnone : ∀ x, b < x → x ≤ b + v → ¬UpperRecord x :=
        fun x hx _ hRx => hex ⟨x, hx, hRx⟩
      have hfb := blockFactor_le_iff_int.mp
        (blockFactor_le_of_upperRecord hR hnone (b + v) (by omega) le_rfl)
      rw [h4] at hd
      exact not_upper_deficit_of_le _ _ _ _ (by positivity) (by positivity) hYint hfb hd

/-- The lower deficit condition at a lower record Order P ≥ 1, from the pair condition at P. -/
theorem lower_deficit_of_pairs {P u : ℕ}
    (hL : ∀ P' c : ℕ, P < P' → LowerRecord P' →
      (∀ x, P < x → x < P' → ¬LowerRecord x) → P' ≤ c → c < P + P' → LowerRecord c →
      (∀ x, c < x → x < P + P' → ¬LowerRecord x) → ¬LowerDeficitLt P c)
    (hP : 1 ≤ P) (hR : LowerRecord P) (hu : 1 ≤ u) (ht : LowerTiming P (u - P)) :
    ¬(p2_of (P + u) = p2_of P + p2_of u ∧
      (2 * (3 : ℤ) ^ (P + u) - 2 ^ p2_of (P + u)) * (4 * 3 ^ P - 2 ^ p2_of P) *
          2 ^ p2_of P <
        (2 * (3 : ℤ) ^ P - 2 ^ p2_of P) ^ 2 * 2 ^ p2_of (P + u)) := by
  rintro ⟨_, hd⟩
  have hYT := two_pow_p2_of_le P
  have hT : (0 : ℤ) < 3 ^ P := by
    positivity
  by_cases hex : ∃ x, P < x ∧ LowerRecord x
  · obtain ⟨P', hPP, hR', hn⟩ := exists_least_above hex
    have huP := (lowerTiming_at_iff_next hP hPP hR hR' hn).mp ht
    obtain ⟨c, hPc, hcX, hRc, hcmax⟩ :=
      exists_greatest_le (R := LowerRecord) hR' (show P' ≤ P + P' - 1 by omega)
    have hfc := blockFactor_le_iff_int.mp
      (blockFactor_ge_of_lowerRecord hRc hcmax (K := P + u) (by omega) (by omega))
    apply hL P' c hPP hR' hn hPc (by omega) hRc
      (fun x hx hxl => hcmax x hx (by omega))
    exact lower_deficit_transfer _ _ _ _ _ _ _ (by positivity) (by positivity)
      (by linarith) (by positivity) hfc hd
  · have hnone : ∀ x, P < x → x ≤ P + u → ¬LowerRecord x :=
      fun x hx _ hRx => hex ⟨x, hx, hRx⟩
    have hfP := blockFactor_le_iff_int.mp
      (blockFactor_ge_of_lowerRecord hR hnone (K := P + u) (by omega) le_rfl)
    exact not_lower_deficit_of_le _ _ _ _ (by positivity) (by positivity) hYT hfP hd

/-- `RulerGap` as one deficit inequality per pair of neighbouring record Orders: for upper
    b < b' it fails at the largest upper record Order c ≤ b + b'; for lower P < P' it fails
    at the largest lower record Order c < P + P'. -/
theorem rulerGap_iff_pairs :
    SmoothRuler.RulerGap ↔
      (∀ b b' c : ℕ, 1 ≤ b → b < b' → UpperRecord b → UpperRecord b' →
          (∀ x, b < x → x < b' → ¬UpperRecord x) → b' ≤ c → c ≤ b + b' → UpperRecord c →
          (∀ x, c < x → x ≤ b + b' → ¬UpperRecord x) → ¬UpperDeficitLt b c) ∧
      (∀ P P' c : ℕ, 1 ≤ P → P < P' → LowerRecord P → LowerRecord P' →
          (∀ x, P < x → x < P' → ¬LowerRecord x) → P' ≤ c → c < P + P' → LowerRecord c →
          (∀ x, c < x → x < P + P' → ¬LowerRecord x) → ¬LowerDeficitLt P c) := by
  rw [rulerGap_iff_deficit]
  constructor
  · rintro ⟨hU, hL⟩
    refine ⟨fun b b' c hb hbb hR hR' hn hbc hcb hRc _ hd => ?_,
      fun P P' c hP hPP hR hR' hn hPc hcP hRc _ hd => ?_⟩
    · have hv : 1 ≤ c - b := by
        omega
      have ht : UpperTiming b (p2_of (c - b) - 1 - p2_of b) :=
        (upperTiming_at_iff_next hb hbb hR hR' hn).mpr (p2_of_mono_le (by omega))
      have hs := (upperRecord_iff_add c).mp hRc b hb (by omega)
      have e : b + (c - b) = c := by
        omega
      apply hU b (c - b) hR hv ht
      rw [e]
      exact ⟨hs, hd⟩
    · have hu : 1 ≤ c - P := by
        omega
      have ht : LowerTiming P (c - P - P) :=
        (lowerTiming_at_iff_next hP hPP hR hR' hn).mpr (by omega)
      have hs := (lowerRecord_iff_add c).mp hRc P hP (by omega)
      have e : P + (c - P) = c := by
        omega
      apply hL P (c - P) hP hR hu ht
      rw [e]
      exact ⟨hs, hd⟩
  · rintro ⟨hU, hL⟩
    exact ⟨fun b v hR hv ht => upper_deficit_of_pairs
        (fun b' c hb hbb hR' hn hbc hcb hRc hcmax => hU b b' c hb hbb hR hR' hn hbc hcb hRc hcmax)
        hR hv ht,
      fun P u hP hR hu ht => lower_deficit_of_pairs
        (fun P' c hPP hR' hn hPc hcP hRc hcmax => hL P P' c hP hPP hR hR' hn hPc hcP hRc hcmax)
        hP hR hu ht⟩

end AcceleratedCollatz
