-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRulerRecord

/-!
  The gap condition of the ruler gap as an inequality on deficits d(n) = 2^p2(n) - 3^n.
  For a step 2^p2(b) / 3^b and a factor 3^v / 2^u (`gapAt_two_three_iff_deficit`): the
  factor lies in the gap exactly when u + 1 = p2(v), the Orders b and v split at
  K = b + v (p2(K) + 1 = p2(b) + p2(v)), and d(K) 4^p2(b) < d(b)^2 2^p2(K), i.e.
  1 - f(K) < (1 - f(b))^2 for the block factor f. For a step 3^P / 2^(p2(P) - 1) and a
  factor 2^v / 3^u (`gapAt_three_two_iff_deficit`): v = p2(u), p2(K) = p2(P) + p2(u)
  for K = P + u, and (2·3^K - 2^p2(K)) (4·3^P - 2^p2(P)) 2^p2(P) <
  (2·3^P - 2^p2(P))^2 2^p2(K).
  The timing of a step (`UpperTiming`, `LowerTiming`) ends at the next record Order: for
  neighbouring upper record Orders b < b' it holds at p2(v) - 1 - p2(b) exactly when
  p2(v) ≤ p2(b') (`upperTiming_at_iff_next`); for neighbouring lower record Orders P < P'
  at u - P exactly when u < P' (`lowerTiming_at_iff_next`). `RulerGap` is the two deficit
  conditions over the record Orders (`rulerGap_iff_deficit`).
-/

namespace AcceleratedCollatz

/-- k < p2(n) when 2^k ≤ 3^n. -/
theorem lt_p2_of_two_pow_le {k n : ℕ} (h : 2 ^ k ≤ 3 ^ n) : k < p2_of n :=
  (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h (p2_of_spec n))

/-- 1 ≤ p2(n). -/
theorem one_le_p2_of (n : ℕ) : 1 ≤ p2_of n := by
  unfold p2_of
  omega

/-- The third condition of `GapAt 2 3` as the deficit inequality, in the integers. -/
theorem gap_two_three_iff_int (A B U V : ℤ) (hA : 0 < A) (hB : 0 < B) :
    2 * (A * U) < A * V + U * B ↔ (A * U - B * V) * (A * A) < (A - B) ^ 2 * (A * U) := by
  have key : (A - B) ^ 2 * (A * U) - (A * U - B * V) * (A * A) =
      B * A * (A * V + U * B - 2 * (A * U)) := by
    ring
  have hBA : 0 < B * A := mul_pos hB hA
  constructor
  · intro h
    have h1 : 0 < B * A * (A * V + U * B - 2 * (A * U)) := mul_pos hBA (by linarith)
    linarith
  · intro h
    have h1 : 0 < B * A * (A * V + U * B - 2 * (A * U)) := by linarith
    have h2 := (pos_iff_pos_of_mul_pos h1).mp hBA
    linarith

/-- The third condition of `GapAt 3 2` as the deficit inequality, in the integers
    (A = 2^p2(P), B = 3^P, V = 2^v, W = 3^u). -/
theorem gap_three_two_iff_int (A B V W : ℤ) (hA : 0 < A) (hB : 0 < B) :
    4 * (B * W) < 2 * (B * V) + A * W ↔
      (2 * (B * W) - A * V) * (4 * B - A) * A < (2 * B - A) ^ 2 * (A * V) := by
  have key : (2 * B - A) ^ 2 * (A * V) - (2 * (B * W) - A * V) * (4 * B - A) * A =
      2 * B * A * (2 * (B * V) + A * W - 4 * (B * W)) := by
    ring
  have hBA : 0 < 2 * B * A := by positivity
  constructor
  · intro h
    have h1 : 0 < 2 * B * A * (2 * (B * V) + A * W - 4 * (B * W)) := mul_pos hBA (by linarith)
    linarith
  · intro h
    have h1 : 0 < 2 * B * A * (2 * (B * V) + A * W - 4 * (B * W)) := by linarith
    have h2 := (pos_iff_pos_of_mul_pos h1).mp hBA
    linarith

/-- A factor 3^v / 2^u in the gap of the step 2^p2(b) / 3^b: u + 1 = p2(v), b and v split
    at b + v, and d(b + v) 4^p2(b) < d(b)^2 2^p2(b + v). -/
theorem gapAt_two_three_iff_deficit {b u v : ℕ} :
    SmoothRuler.GapAt 2 3 (p2_of b) b u v ↔
      u + 1 = p2_of v ∧ p2_of (b + v) + 1 = p2_of b + p2_of v ∧
        ((2 : ℤ) ^ p2_of (b + v) - 3 ^ (b + v)) * 4 ^ p2_of b <
          ((2 : ℤ) ^ p2_of b - 3 ^ b) ^ 2 * 2 ^ p2_of (b + v) := by
  have hPs := p2_of_spec b
  have hPl := p2_of_spec_lower b
  have hvs := p2_of_spec v
  have hvl := p2_of_spec_lower v
  have hP1 := one_le_p2_of b
  have hv1 := one_le_p2_of v
  have h4 : (4 : ℤ) ^ p2_of b = (2 : ℤ) ^ p2_of b * (2 : ℤ) ^ p2_of b := by
    rw [← mul_pow]
    norm_num
  constructor
  · rintro ⟨g1, g2, g3⟩
    -- 3^v < 2^(u+1), from g2 and 2^(P-1) ≤ 3^b
    have hv2 : 3 ^ v < 2 ^ (u + 1) := by
      have e1 : 3 ^ (v + b) = 3 ^ v * 3 ^ b := pow_add 3 v b
      have e2 : 2 ^ (p2_of b + u) = 2 ^ (u + 1) * 2 ^ (p2_of b - 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e1, e2] at g2
      by_contra hc
      have hc' : 2 ^ (u + 1) ≤ 3 ^ v := Nat.le_of_not_lt hc
      have := Nat.mul_le_mul hc' hPl
      omega
    have hu1 : u + 1 = p2_of v := by
      have a1 := p2_of_le_of_three_pow_lt hv2
      have a2 := lt_p2_of_two_pow_le g1.le
      omega
    have hK : p2_of (b + v) = p2_of b + u := by
      have a1 : p2_of (b + v) ≤ p2_of b + u := by
        apply p2_of_le_of_three_pow_lt
        rw [Nat.add_comm b v]
        exact g2
      have a2 : p2_of b - 1 + u < p2_of (b + v) := by
        apply lt_p2_of_two_pow_le
        rw [pow_add, pow_add]
        have hu : 2 ^ u ≤ 3 ^ v := g1.le
        exact Nat.mul_le_mul hPl hu
      omega
    refine ⟨hu1, by omega, ?_⟩
    rw [hK, h4, pow_add, pow_add]
    have g3' : 2 * ((2 : ℤ) ^ p2_of b * 2 ^ u) < 2 ^ p2_of b * 3 ^ v + 2 ^ u * 3 ^ b := by
      have := g3
      rw [pow_add] at this
      exact_mod_cast this
    exact (gap_two_three_iff_int _ _ _ _ (by positivity) (by positivity)).mp g3'
  · rintro ⟨d1, d2, d3⟩
    have hK : p2_of (b + v) = p2_of b + u := by omega
    rw [hK, h4, pow_add, pow_add] at d3
    have g3' := (gap_two_three_iff_int _ _ _ _ (by positivity) (by positivity)).mpr d3
    have g3 : 2 * 2 ^ (p2_of b + u) < 2 ^ p2_of b * 3 ^ v + 2 ^ u * 3 ^ b := by
      rw [pow_add]
      exact_mod_cast g3'
    have g1 : 2 ^ u < 3 ^ v := by
      rw [pow_add] at g3
      by_contra hc
      have hc' : 3 ^ v ≤ 2 ^ u := Nat.le_of_not_lt hc
      have m1 : 2 ^ p2_of b * 3 ^ v ≤ 2 ^ p2_of b * 2 ^ u := Nat.mul_le_mul_left _ hc'
      have m2 : 2 ^ u * 3 ^ b ≤ 2 ^ u * 2 ^ p2_of b := Nat.mul_le_mul_left _ hPs.le
      have m3 : 2 ^ u * 2 ^ p2_of b = 2 ^ p2_of b * 2 ^ u := Nat.mul_comm _ _
      omega
    have g2 : 3 ^ (v + b) < 2 ^ (p2_of b + u) := by
      rw [← hK, Nat.add_comm v b]
      exact p2_of_spec (b + v)
    exact ⟨g1, g2, g3⟩

/-- A factor 2^v / 3^u in the gap of the step 3^P / 2^(p2(P) - 1): v = p2(u),
    p2(P + u) = p2(P) + p2(u), and the deficit inequality of the lower steps. -/
theorem gapAt_three_two_iff_deficit {P u v : ℕ} :
    SmoothRuler.GapAt 3 2 P (p2_of P - 1) u v ↔
      v = p2_of u ∧ p2_of (P + u) = p2_of P + p2_of u ∧
        (2 * (3 : ℤ) ^ (P + u) - 2 ^ p2_of (P + u)) * (4 * 3 ^ P - 2 ^ p2_of P) *
            2 ^ p2_of P <
          (2 * (3 : ℤ) ^ P - 2 ^ p2_of P) ^ 2 * 2 ^ p2_of (P + u) := by
  have hPs := p2_of_spec P
  have hPl := p2_of_spec_lower P
  have hus := p2_of_spec u
  have hul := p2_of_spec_lower u
  have hP1 := one_le_p2_of P
  have hA : 2 ^ p2_of P = 2 * 2 ^ (p2_of P - 1) := by
    rw [← pow_succ']
    congr 1
  have hAz : (2 : ℤ) ^ p2_of P = 2 * 2 ^ (p2_of P - 1) := by
    exact_mod_cast hA
  constructor
  · rintro ⟨g1, g2, g3⟩
    -- 2^v < 2 * 3^u, from g2 and 3^P < 2^p2(P)
    have hv2 : 2 ^ v < 2 * 3 ^ u := by
      have e1 : 2 ^ (v + (p2_of P - 1)) = 2 ^ v * 2 ^ (p2_of P - 1) := pow_add 2 v _
      have e2 : 3 ^ (P + u) = 3 ^ P * 3 ^ u := pow_add 3 P u
      rw [e1, e2] at g2
      by_contra hc
      have hc' : 2 * 3 ^ u ≤ 2 ^ v := Nat.le_of_not_lt hc
      have m1 := Nat.mul_le_mul_right (2 ^ (p2_of P - 1)) hc'
      have m2 : 3 ^ P * 3 ^ u < 2 ^ p2_of P * 3 ^ u :=
        Nat.mul_lt_mul_of_pos_right hPs (Nat.pow_pos (by norm_num))
      have m3 : 2 * 3 ^ u * 2 ^ (p2_of P - 1) = 2 ^ p2_of P * 3 ^ u := by
        rw [hA]
        ring
      omega
    have hv : v = p2_of u := by
      have a1 := p2_of_le_of_three_pow_lt g1
      have a2 : v - 1 < p2_of u := by
        apply lt_p2_of_two_pow_le
        by_contra hc
        have hc' : 3 ^ u < 2 ^ (v - 1) := Nat.lt_of_not_le hc
        rcases Nat.eq_zero_or_pos v with h0 | hpos
        · rw [h0] at g1
          simp at g1
        · have e2 : 2 ^ v = 2 * 2 ^ (v - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          omega
      omega
    have hK : p2_of (P + u) = p2_of P + p2_of u := by
      have a1 : p2_of (P + u) ≤ p2_of P + p2_of u := by
        apply p2_of_le_of_three_pow_lt
        rw [pow_add, pow_add]
        exact Nat.mul_lt_mul'' hPs hus
      have a2 : p2_of P - 1 + p2_of u < p2_of (P + u) := by
        apply lt_p2_of_two_pow_le
        rw [← hv, Nat.add_comm (p2_of P - 1) v]
        exact g2.le
      omega
    refine ⟨hv, hK, ?_⟩
    rw [hK, pow_add, pow_add, ← hv]
    have g3' : 4 * ((3 : ℤ) ^ P * 3 ^ u) <
        2 * ((3 : ℤ) ^ P * 2 ^ v) + 2 ^ p2_of P * 3 ^ u := by
      have h1 : 2 * 3 ^ (P + u) < 3 ^ P * 2 ^ v + 3 ^ u * 2 ^ (p2_of P - 1) := g3
      rw [pow_add] at h1
      have h2 : (2 : ℤ) * (3 ^ P * 3 ^ u) < 3 ^ P * 2 ^ v + 3 ^ u * 2 ^ (p2_of P - 1) := by
        exact_mod_cast h1
      rw [hAz]
      linarith
    exact (gap_three_two_iff_int _ _ _ _ (by positivity) (by positivity)).mp g3'
  · rintro ⟨d1, d2, d3⟩
    have hv1 := one_le_p2_of u
    rw [d2, pow_add, pow_add, ← d1] at d3
    have g3' := (gap_three_two_iff_int _ _ _ _ (by positivity) (by positivity)).mpr d3
    have g3 : 2 * 3 ^ (P + u) < 3 ^ P * 2 ^ v + 3 ^ u * 2 ^ (p2_of P - 1) := by
      rw [pow_add]
      have h2 : (2 : ℤ) * (3 ^ P * 3 ^ u) < 3 ^ P * 2 ^ v + 3 ^ u * 2 ^ (p2_of P - 1) := by
        rw [hAz] at g3'
        linarith
      exact_mod_cast h2
    have g1 : 3 ^ u < 2 ^ v := by
      rw [d1]
      exact hus
    have g2 : 2 ^ (v + (p2_of P - 1)) < 3 ^ (P + u) := by
      have a1 : 2 ^ (p2_of (P + u) - 1) ≤ 3 ^ (P + u) := p2_of_spec_lower (P + u)
      have a2 : 2 ^ (v + (p2_of P - 1)) ≤ 3 ^ (P + u) := by
        rw [d2, ← d1] at a1
        have e : v + (p2_of P - 1) = p2_of P + v - 1 := by
          omega
        rw [e]
        exact a1
      have a3 : 2 ^ (v + (p2_of P - 1)) ≠ 3 ^ (P + u) := by
        intro h
        have h2 : 2 ∣ 3 ^ (P + u) := by
          rw [← h]
          exact dvd_pow_self 2 (by omega)
        have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        omega
      omega
    exact ⟨g1, g2, g3⟩

/-! ### The windows: where the timing of a step ends -/

/-- The timing of an upper step from b with exponent j of 2 (as in `UpperGapRecords`):
    every lower step 3^a / 2^(p2(a) - 1) that fits (p2(a) - 1 ≤ j) goes up by more. -/
def UpperTiming (b j : ℕ) : Prop :=
  ∀ a, 1 ≤ a → p2_of a - 1 ≤ j → 2 ^ (p2_of b + (p2_of a - 1)) < 3 ^ (a + b)

/-- The timing of a lower step from P with exponent j of 3 (as in `LowerGapRecords`). -/
def LowerTiming (P j : ℕ) : Prop :=
  ∀ i, i ≤ j → 3 ^ (P + i) < 2 ^ (p2_of i + (p2_of P - 1))

/-- p2(a) ≤ p2(n) for a ≤ n. -/
theorem p2_of_mono_le {a n : ℕ} (h : a ≤ n) : p2_of a ≤ p2_of n :=
  p2Q_mono le_rfl h

/-- One lower step against an upper step: it goes up by more exactly when p2 is
    additive at b + a. -/
theorem upper_timing_one_iff {a b : ℕ} :
    2 ^ (p2_of b + (p2_of a - 1)) < 3 ^ (a + b) ↔ p2_of (a + b) = p2_of a + p2_of b := by
  have hle : p2_of (a + b) ≤ p2_of a + p2_of b := p2Q_add_le le_rfl a b
  have ha1 := one_le_p2_of a
  have hb1 := one_le_p2_of b
  constructor
  · intro h
    have h1 := lt_p2_of_two_pow_le h.le
    omega
  · intro h
    have h1 : 2 ^ (p2_of (a + b) - 1) ≤ 3 ^ (a + b) := p2_of_spec_lower (a + b)
    have h2 : p2_of (a + b) - 1 = p2_of b + (p2_of a - 1) := by
      omega
    rw [h2] at h1
    have h3 : 2 ^ (p2_of b + (p2_of a - 1)) ≠ 3 ^ (a + b) := by
      intro he
      have hd : 2 ∣ 3 ^ (a + b) := by
        rw [← he]
        exact dvd_pow_self 2 (by omega)
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd
      omega
    omega

/-- One upper step against a lower step: it goes up by more exactly when the Orders P and
    i split at P + i. -/
theorem lower_timing_one_iff {P i : ℕ} :
    3 ^ (P + i) < 2 ^ (p2_of i + (p2_of P - 1)) ↔ p2_of (P + i) + 1 = p2_of P + p2_of i := by
  have hle : p2_of P + p2_of i ≤ p2_of (P + i) + 1 := p2Q_add_le_succ le_rfl P i
  have hP1 := one_le_p2_of P
  constructor
  · intro h
    have h1 := p2_of_le_of_three_pow_lt h
    omega
  · intro h
    have h1 : 3 ^ (P + i) < 2 ^ p2_of (P + i) := p2_of_spec (P + i)
    have h2 : p2_of (P + i) = p2_of i + (p2_of P - 1) := by
      omega
    rw [h2] at h1
    exact h1

/-- Between an upper record Order b and the next one, p2(b + i) = p2(b) + p2(i). -/
theorem p2_of_add_of_upperRecord {b b' : ℕ} (hR : UpperRecord b)
    (hnone : ∀ x, b < x → x < b' → ¬UpperRecord x) {i : ℕ} (hi : 1 ≤ i) (hib : b + i < b') :
    p2_of (b + i) = p2_of b + p2_of i :=
  p2Q_add_of_upperRecordQ (by decide) le_rfl hR hnone hi hib

/-- For neighbouring upper record Orders 1 ≤ b < b', the timing of the step from b holds
    exactly up to j = p2(b' - b) - 2. -/
theorem upperTiming_iff_next {b b' j : ℕ} (hb : 1 ≤ b) (hbb : b < b') (hR : UpperRecord b)
    (hR' : UpperRecord b') (hnone : ∀ x, b < x → x < b' → ¬UpperRecord x) :
    UpperTiming b j ↔ j + 2 ≤ p2_of (b' - b) := by
  have hsplit := (upperRecord_iff_add b').mp hR' b hb hbb
  constructor
  · intro h
    by_contra hc
    have h1 := h (b' - b) (by omega) (by omega)
    rw [upper_timing_one_iff, Nat.sub_add_cancel hbb.le] at h1
    omega
  · intro h a ha haj
    rw [upper_timing_one_iff]
    have hlt : a < b' - b := by
      by_contra hc
      have := p2_of_mono_le (Nat.le_of_not_lt hc)
      have := one_le_p2_of a
      omega
    rw [Nat.add_comm a b]
    have := p2_of_add_of_upperRecord hR hnone ha (by omega)
    omega

/-- For neighbouring lower record Orders 1 ≤ P < P', the timing of the step from P holds
    exactly up to j = P' - P - 1. -/
theorem lowerTiming_iff_next {P P' j : ℕ} (hP : 1 ≤ P) (hPP : P < P') (hR : LowerRecord P)
    (hR' : LowerRecord P') (hnone : ∀ x, P < x → x < P' → ¬LowerRecord x) :
    LowerTiming P j ↔ j + P < P' := by
  have hadd := (lowerRecord_iff_add P').mp hR' P hP hPP
  constructor
  · intro h
    by_contra hc
    have h1 := h (P' - P) (by omega)
    rw [lower_timing_one_iff, Nat.add_sub_cancel' hPP.le] at h1
    omega
  · intro h i hij
    rw [lower_timing_one_iff]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have : p2_of 0 = 1 := by
        unfold p2_of
        simp
      change p2_of P + 1 = p2_of P + p2_of 0
      omega
    · exact p2_of_add_of_lowerRecord hR hnone hpos (by omega)

/-- The upper timing gets weaker as j falls. -/
theorem upperTiming_mono {b j j' : ℕ} (h : UpperTiming b j) (hj : j' ≤ j) :
    UpperTiming b j' :=
  fun a ha haj => h a ha (le_trans haj hj)

/-- The lower timing gets weaker as j falls. -/
theorem lowerTiming_mono {P j j' : ℕ} (h : LowerTiming P j) (hj : j' ≤ j) :
    LowerTiming P j' :=
  fun i hi => h i (le_trans hi hj)

/-- `UpperGapRecords` as the deficit condition: for every upper record Order b and every
    Order v ≥ 1 with the timing of b at p2(v) - 1 - p2(b), no split of b and v at b + v
    meets the deficit inequality. -/
theorem upperGapRecords_iff_deficit {M N : ℕ} :
    UpperGapRecords M N ↔
      ∀ b v : ℕ, p2_of b ≤ M → p2_of v - 1 ≤ M → b ≤ N → v ≤ N → UpperRecord b → 1 ≤ v →
        UpperTiming b (p2_of v - 1 - p2_of b) →
          ¬(p2_of (b + v) + 1 = p2_of b + p2_of v ∧
            ((2 : ℤ) ^ p2_of (b + v) - 3 ^ (b + v)) * 4 ^ p2_of b <
              ((2 : ℤ) ^ p2_of b - 3 ^ b) ^ 2 * 2 ^ p2_of (b + v)) := by
  constructor
  · intro h b v hbM hvM hbN hvN hR hv ht hd
    have hv2 : 2 ≤ p2_of v := by
      have h31 : 3 ^ 1 ≤ 3 ^ v := Nat.pow_le_pow_right (by norm_num) hv
      have h21 : 2 ^ 1 ≤ 3 ^ v := by
        omega
      have := lt_p2_of_two_pow_le h21
      omega
    have hb1 := one_le_p2_of b
    have hgap := gapAt_two_three_iff_deficit.mpr ⟨(by omega : p2_of v - 1 + 1 = p2_of v), hd⟩
    exact h b (p2_of v - 1 - p2_of b) (p2_of v - 1) v hbM hvM hbN hvN hR ht (by omega)
      (by omega) hgap
  · intro h b j u v hbM huM hbN hvN hR ht hju huj hgap
    obtain ⟨d1, d2, d3⟩ := gapAt_two_three_iff_deficit.mp hgap
    have hv : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with h0 | hpos
      · subst h0
        have : p2_of 0 = 1 := by
          unfold p2_of
          simp
        omega
      · exact hpos
    exact h b v hbM (by omega) hbN hvN hR hv (upperTiming_mono ht (by omega)) ⟨d2, d3⟩

/-- `LowerGapRecords` as the deficit condition: for every lower record Order P ≥ 1 and
    every u ≥ 1 with the timing of P at u - P, no split of P and u at P + u meets the
    deficit inequality of the lower steps. -/
theorem lowerGapRecords_iff_deficit {M N : ℕ} :
    LowerGapRecords M N ↔
      ∀ P u : ℕ, P ≤ M → u ≤ M → p2_of P - 1 ≤ N → p2_of u ≤ N → 1 ≤ P → LowerRecord P →
        1 ≤ u → LowerTiming P (u - P) →
          ¬(p2_of (P + u) = p2_of P + p2_of u ∧
            (2 * (3 : ℤ) ^ (P + u) - 2 ^ p2_of (P + u)) * (4 * 3 ^ P - 2 ^ p2_of P) *
                2 ^ p2_of P <
              (2 * (3 : ℤ) ^ P - 2 ^ p2_of P) ^ 2 * 2 ^ p2_of (P + u)) := by
  constructor
  · intro h P u hPM huM hPN hvN hP hR hu ht hd
    have hgap := gapAt_three_two_iff_deficit.mpr ⟨rfl, hd⟩
    exact h P (u - P) u (p2_of u) hPM huM hPN hvN hP hR ht (by omega) (by omega) hgap
  · intro h P j u v hPM huM hPN hvN hP hR ht hju huj hgap
    obtain ⟨d1, d2, d3⟩ := gapAt_three_two_iff_deficit.mp hgap
    subst d1
    exact h P u hPM huM hPN hvN hP hR (by omega) (lowerTiming_mono ht (by omega)) ⟨d2, d3⟩

/-- For neighbouring upper record Orders 1 ≤ b < b': the timing of b at p2(v) - 1 - p2(b)
    holds exactly when p2(v) ≤ p2(b'). -/
theorem upperTiming_at_iff_next {b b' v : ℕ} (hb : 1 ≤ b) (hbb : b < b') (hR : UpperRecord b)
    (hR' : UpperRecord b') (hnone : ∀ x, b < x → x < b' → ¬UpperRecord x) :
    UpperTiming b (p2_of v - 1 - p2_of b) ↔ p2_of v ≤ p2_of b' := by
  rw [upperTiming_iff_next hb hbb hR hR' hnone]
  have hsplit := (upperRecord_iff_add b').mp hR' b hb hbb
  have hmono := p2_of_mono_le hbb.le
  have h2 : 2 ≤ p2_of (b' - b) := by
    have h31 : 3 ^ 1 ≤ 3 ^ (b' - b) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h21 : 2 ^ 1 ≤ 3 ^ (b' - b) := by
      omega
    have := lt_p2_of_two_pow_le h21
    omega
  have hb1 := one_le_p2_of b
  omega

/-- For neighbouring lower record Orders 1 ≤ P < P': the timing of P at u - P holds
    exactly when u < P'. -/
theorem lowerTiming_at_iff_next {P P' u : ℕ} (hP : 1 ≤ P) (hPP : P < P') (hR : LowerRecord P)
    (hR' : LowerRecord P') (hnone : ∀ x, P < x → x < P' → ¬LowerRecord x) :
    LowerTiming P (u - P) ↔ u < P' := by
  rw [lowerTiming_iff_next hP hPP hR hR' hnone]
  omega

/-- `RulerGap` as the two deficit conditions, over the upper and the lower record Orders,
    each with the timing of its step. -/
theorem rulerGap_iff_deficit :
    SmoothRuler.RulerGap ↔
      (∀ b v : ℕ, UpperRecord b → 1 ≤ v → UpperTiming b (p2_of v - 1 - p2_of b) →
          ¬(p2_of (b + v) + 1 = p2_of b + p2_of v ∧
            ((2 : ℤ) ^ p2_of (b + v) - 3 ^ (b + v)) * 4 ^ p2_of b <
              ((2 : ℤ) ^ p2_of b - 3 ^ b) ^ 2 * 2 ^ p2_of (b + v))) ∧
      (∀ P u : ℕ, 1 ≤ P → LowerRecord P → 1 ≤ u → LowerTiming P (u - P) →
          ¬(p2_of (P + u) = p2_of P + p2_of u ∧
            (2 * (3 : ℤ) ^ (P + u) - 2 ^ p2_of (P + u)) * (4 * 3 ^ P - 2 ^ p2_of P) *
                2 ^ p2_of P <
              (2 * (3 : ℤ) ^ P - 2 ^ p2_of P) ^ 2 * 2 ^ p2_of (P + u))) := by
  rw [rulerGap_iff_records]
  constructor
  · rintro ⟨hU, hL⟩
    refine ⟨fun b v hR hv ht => ?_, fun P u hP hR hu ht => ?_⟩
    · exact upperGapRecords_iff_deficit.mp
        (hU (p2_of b + p2_of v) (b + v)) b v (by omega) (by omega) (by omega) (by omega)
        hR hv ht
    · exact lowerGapRecords_iff_deficit.mp
        (hL (P + u) (p2_of P + p2_of u)) P u (by omega) (by omega) (by omega) (by omega)
        hP hR hu ht
  · rintro ⟨hU, hL⟩
    refine ⟨fun M N => ?_, fun M N => ?_⟩
    · exact upperGapRecords_iff_deficit.mpr
        fun b v _ _ _ _ hR hv ht => hU b v hR hv ht
    · exact lowerGapRecords_iff_deficit.mpr
        fun P u _ _ _ _ hP hR hu ht => hL P u hP hR hu ht

end AcceleratedCollatz
