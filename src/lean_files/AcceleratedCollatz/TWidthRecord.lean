-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecord
import AcceleratedCollatz.TWidthBound

/-!
  Records of the width bound. tau(n) = n 3^(n-1) / (2^p2(n) - 3^n) (`tau`), and
  `widthBound n` is the largest natural number at most tau(n)
  (`natCast_le_tau_iff`). An Order m such that no
  Order from 1 to m has a block factor above that of a has tau at most tau(a), and
  below it when m is above a
  (`tau_le_of_blockFactor_le`, `tau_lt_of_blockFactor_le`). So the Orders at which
  tau is above every earlier value are the upper record Orders
  (`upperRecord_iff_tau`), and the same holds for the floors
  (`upperRecord_iff_widthBound`). Up to n the width bound is largest at the last
  upper record Order (`widthBound_le_of_upperRecord`), so a verified range that
  reaches its width bound covers every Order up to n
  (`classDropsAt_of_verified_record`).
-/

namespace AcceleratedCollatz

/-- tau(n) = n 3^(n-1) / (2^p2(n) - 3^n). -/
def tau (n : ℕ) : ℚ := n * 3 ^ (n - 1) / (2 ^ p2_of n - 3 ^ n)

/-- 3^n < 2^p2(n), in ℚ. -/
theorem three_pow_lt_two_pow_p2 (n : ℕ) : (3 : ℚ) ^ n < 2 ^ p2_of n := by
  exact_mod_cast p2_of_spec n

theorem tau_den_pos (n : ℕ) : (0 : ℚ) < 2 ^ p2_of n - 3 ^ n :=
  sub_pos.mpr (three_pow_lt_two_pow_p2 n)

/-- The width bound is the largest natural number at most tau. -/
theorem natCast_le_tau_iff (w n : ℕ) : (w : ℚ) ≤ tau n ↔ w ≤ widthBound n := by
  have hle : 3 ^ n ≤ 2 ^ p2_of n := (p2_of_spec n).le
  have hpos : 0 < 2 ^ p2_of n - 3 ^ n := Nat.sub_pos_of_lt (p2_of_spec n)
  unfold tau widthBound
  rw [le_div_iff₀ (tau_den_pos n), Nat.le_div_iff_mul_le hpos]
  constructor
  · intro h
    have h' : ((w * (2 ^ p2_of n - 3 ^ n) : ℕ) : ℚ) ≤ ((n * 3 ^ (n - 1) : ℕ) : ℚ) := by
      rw [Nat.cast_mul, Nat.cast_sub hle]
      push_cast
      exact h
    exact_mod_cast h'
  · intro h
    have h' : ((w * (2 ^ p2_of n - 3 ^ n) : ℕ) : ℚ) ≤ ((n * 3 ^ (n - 1) : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hle] at h'
    push_cast at h'
    exact h'

/-- A larger tau has a width bound at least as large. -/
theorem widthBound_le_of_tau_le {m a : ℕ} (h : tau m ≤ tau a) :
    widthBound m ≤ widthBound a :=
  (natCast_le_tau_iff _ a).mp (((natCast_le_tau_iff _ m).mpr le_rfl).trans h)

/-- tau(n) = n 3^n / (3 (2^p2(n) - 3^n)). -/
theorem tau_eq (n : ℕ) : tau n = n * 3 ^ n / (3 * (2 ^ p2_of n - 3 ^ n)) := by
  have hpos := tau_den_pos n
  cases n with
  | zero =>
    simp [tau]
  | succ n =>
    unfold tau
    rw [Nat.add_sub_cancel, div_eq_div_iff hpos.ne' (mul_pos three_pos hpos).ne']
    ring

/-- tau(a) ≤ tau(n), cross-multiplied. -/
theorem tau_le_iff (a n : ℕ) :
    tau a ≤ tau n ↔
      (a : ℚ) * 3 ^ a * (2 ^ p2_of n - 3 ^ n) ≤ n * 3 ^ n * (2 ^ p2_of a - 3 ^ a) := by
  have ha := tau_den_pos a
  have hn := tau_den_pos n
  rw [tau_eq, tau_eq, div_le_div_iff₀ (mul_pos three_pos ha) (mul_pos three_pos hn)]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- tau(a) < tau(n), cross-multiplied. -/
theorem tau_lt_iff (a n : ℕ) :
    tau a < tau n ↔
      (a : ℚ) * 3 ^ a * (2 ^ p2_of n - 3 ^ n) < n * 3 ^ n * (2 ^ p2_of a - 3 ^ a) := by
  have ha := tau_den_pos a
  have hn := tau_den_pos n
  rw [tau_eq, tau_eq, div_lt_div_iff₀ (mul_pos three_pos ha) (mul_pos three_pos hn)]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- Block factors compare like the cross products 3^a 2^p2(c) and 3^c 2^p2(a). -/
theorem blockFactor_le_iff (a c : ℕ) :
    blockFactor a ≤ blockFactor c ↔
      (3 : ℚ) ^ a * 2 ^ p2_of c ≤ 3 ^ c * 2 ^ p2_of a := by
  rw [blockFactor_eq, blockFactor_eq, div_le_div_iff₀ (by positivity) (by positivity)]

theorem blockFactor_lt_iff (a c : ℕ) :
    blockFactor a < blockFactor c ↔
      (3 : ℚ) ^ a * 2 ^ p2_of c < 3 ^ c * 2 ^ p2_of a := by
  rw [blockFactor_eq, blockFactor_eq, div_lt_div_iff₀ (by positivity) (by positivity)]

/-- A later Order with a block factor at least as large has tau at least as large. -/
theorem tau_le_of_le_of_blockFactor_le {a n : ℕ} (han : a ≤ n)
    (h : blockFactor a ≤ blockFactor n) : tau a ≤ tau n := by
  have hA : (0 : ℚ) < 3 ^ a := by positivity
  have hB : (0 : ℚ) < 3 ^ n := by positivity
  have hAP := three_pow_lt_two_pow_p2 a
  have hf := (blockFactor_le_iff a n).mp h
  have hc : (a : ℚ) ≤ n := by exact_mod_cast han
  have ha0 : (0 : ℚ) ≤ a := by positivity
  rw [tau_le_iff]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) hB.le) (sub_nonneg.mpr hAP.le),
    mul_nonneg ha0 (sub_nonneg.mpr hf)]

/-- A later Order with a larger block factor has a larger tau. -/
theorem tau_lt_of_le_of_blockFactor_lt {a n : ℕ} (ha : 1 ≤ a) (han : a ≤ n)
    (h : blockFactor a < blockFactor n) : tau a < tau n := by
  have hA : (0 : ℚ) < 3 ^ a := by positivity
  have hB : (0 : ℚ) < 3 ^ n := by positivity
  have hAP := three_pow_lt_two_pow_p2 a
  have hf := (blockFactor_lt_iff a n).mp h
  have hc : (a : ℚ) ≤ n := by exact_mod_cast han
  have ha0 : (0 : ℚ) < a := by exact_mod_cast ha
  rw [tau_lt_iff]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) hB.le) (sub_nonneg.mpr hAP.le),
    mul_pos ha0 (sub_pos.mpr hf)]

/-- A block factor not above that of a shorter word: p2 is additive at the split. -/
theorem p2_of_add_of_blockFactor_le {a b : ℕ} (hb : 1 ≤ b)
    (h : blockFactor (a + b) ≤ blockFactor a) : p2_of (a + b) = p2_of a + p2_of b := by
  have hle : p2_of (a + b) ≤ p2_of a + p2_of b := p2Q_add_le (q := 3) le_rfl a b
  have hiff : blockFactor a < blockFactor (a + b) ↔
      p2_of (a + b) + 1 = p2_of a + p2_of b :=
    blockFactorQ_lt_add_iff (q := 3) (by decide) le_rfl a hb
  have hne : ¬(p2_of (a + b) + 1 = p2_of a + p2_of b) := fun he => absurd (hiff.mpr he) h.not_gt
  have hsucc : p2_of a + p2_of b ≤ p2_of (a + b) + 1 := p2Q_add_le_succ (q := 3) le_rfl a b
  omega

/-- tau(a + m) < tau(a) when p2 is additive at the split and tau(m) ≤ tau(a). -/
theorem tau_add_lt {a m : ℕ} (ha : 1 ≤ a) (hp : p2_of (a + m) = p2_of a + p2_of m)
    (h : tau m ≤ tau a) : tau (a + m) < tau a := by
  have hA : (0 : ℚ) < 3 ^ a := by positivity
  have hAP := three_pow_lt_two_pow_p2 a
  have hBQ := three_pow_lt_two_pow_p2 m
  have ha0 : (0 : ℚ) < a := by exact_mod_cast ha
  have hm := (tau_le_iff m a).mp h
  rw [tau_lt_iff, hp, pow_add, pow_add]
  push_cast
  nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hm),
    mul_pos (mul_pos (mul_pos hA ha0) (sub_pos.mpr hAP)) (sub_pos.mpr hBQ)]

/-- If no Order from 1 to m has a block factor above that of a, then tau(m) ≤ tau(a),
    and tau(m) < tau(a) when a < m. -/
theorem tau_le_and_lt_of_blockFactor_le {a : ℕ} (ha : 1 ≤ a) (m : ℕ) (hm : 1 ≤ m)
    (hdom : ∀ k, 1 ≤ k → k ≤ m → blockFactor k ≤ blockFactor a) :
    tau m ≤ tau a ∧ (a < m → tau m < tau a) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge a m with ham | hma
    · obtain ⟨b, rfl⟩ : ∃ b, m = a + b := ⟨m - a, by omega⟩
      have hb : 1 ≤ b := by omega
      have hp := p2_of_add_of_blockFactor_le hb (hdom (a + b) hm le_rfl)
      have hb' := (ih b (by omega) hb fun k hk1 hkb => hdom k hk1 (by omega)).1
      have hlt := tau_add_lt ha hp hb'
      exact ⟨hlt.le, fun _ => hlt⟩
    · exact ⟨tau_le_of_le_of_blockFactor_le hma (hdom m hm le_rfl), fun h => absurd h (by omega)⟩

theorem tau_le_of_blockFactor_le {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m)
    (hdom : ∀ k, 1 ≤ k → k ≤ m → blockFactor k ≤ blockFactor a) : tau m ≤ tau a :=
  (tau_le_and_lt_of_blockFactor_le ha m hm hdom).1

theorem tau_lt_of_blockFactor_le {a m : ℕ} (ha : 1 ≤ a) (ham : a < m)
    (hdom : ∀ k, 1 ≤ k → k ≤ m → blockFactor k ≤ blockFactor a) : tau m < tau a :=
  (tau_le_and_lt_of_blockFactor_le ha m (by omega) hdom).2 ham

/-- Among the Orders 1 to n one has the largest block factor. -/
theorem exists_blockFactor_max {n : ℕ} (hn : 1 ≤ n) :
    ∃ a, 1 ≤ a ∧ a ≤ n ∧ ∀ k, 1 ≤ k → k ≤ n → blockFactor k ≤ blockFactor a := by
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image (Finset.Icc 1 n) blockFactor ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  rw [Finset.mem_Icc] at ha
  exact ⟨a, ha.1, ha.2, fun k hk1 hkn => hmax k (Finset.mem_Icc.mpr ⟨hk1, hkn⟩)⟩

/-- An Order that is no upper record has an earlier Order with a larger tau. -/
theorem exists_tau_lt_of_not_upperRecord {n : ℕ} (h : ¬UpperRecord n) :
    ∃ a, 1 ≤ a ∧ a < n ∧ tau n < tau a := by
  rw [upperRecord_iff_blockFactor] at h
  push Not at h
  obtain ⟨c, hc1, hcn, hc⟩ := h
  obtain ⟨a, ha1, han, hmax⟩ := exists_blockFactor_max (n := n - 1) (by omega)
  refine ⟨a, ha1, by omega, tau_lt_of_blockFactor_le ha1 (by omega) fun k hk1 hkn => ?_⟩
  rcases Nat.lt_or_ge k n with hlt | hge
  · exact hmax k hk1 (by omega)
  · have hk : k = n := by omega
    rw [hk]
    exact hc.trans (hmax c hc1 (by omega))

/-- The upper record Orders are the Orders at which tau is above every earlier value. -/
theorem upperRecord_iff_tau (n : ℕ) :
    UpperRecord n ↔ ∀ a, 1 ≤ a → a < n → tau a < tau n := by
  constructor
  · intro hR a ha1 han
    exact tau_lt_of_le_of_blockFactor_lt ha1 han.le
      ((upperRecord_iff_blockFactor n).mp hR a ha1 han)
  · intro h
    by_contra hR
    obtain ⟨a, ha1, han, hlt⟩ := exists_tau_lt_of_not_upperRecord hR
    exact lt_asymm hlt (h a ha1 han)

/-- tau(a) + 1 ≤ tau(n) for a < n, when the block factor of a is at least that of
    Order 1 (3/4) and at most that of n. -/
theorem tau_add_one_le {a n : ℕ} (han : a < n) (h34 : blockFactor 1 ≤ blockFactor a)
    (h : blockFactor a ≤ blockFactor n) : tau a + 1 ≤ tau n := by
  have hA : (0 : ℚ) < 3 ^ a := by positivity
  have hB : (0 : ℚ) < 3 ^ n := by positivity
  have hAP := three_pow_lt_two_pow_p2 a
  have hBQ := three_pow_lt_two_pow_p2 n
  have hf := (blockFactor_le_iff a n).mp h
  have h1 := (blockFactor_le_iff 1 a).mp h34
  rw [p2_of_one] at h1
  have hc : (a : ℚ) + 1 ≤ n := by exact_mod_cast han
  have ha0 : (0 : ℚ) ≤ a := by positivity
  have hda := tau_den_pos a
  have hdn := tau_den_pos n
  rw [tau_eq, tau_eq, div_add_one (mul_pos three_pos hda).ne',
    div_le_div_iff₀ (mul_pos three_pos hda) (mul_pos three_pos hdn)]
  have hkey : ((a : ℚ) + 1) * 3 ^ a * (2 ^ p2_of n - 3 ^ n)
      ≤ n * 3 ^ n * (2 ^ p2_of a - 3 ^ a) := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) hB.le) hda.le,
      mul_nonneg (add_nonneg ha0 zero_le_one) (sub_nonneg.mpr hf)]
  have hsmall : (3 : ℚ) * (2 ^ p2_of a - 3 ^ a) ≤ 3 ^ a := by
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) hdn.le]

/-- The upper record Orders are the Orders at which the width bound is above every
    earlier value. -/
theorem upperRecord_iff_widthBound (n : ℕ) :
    UpperRecord n ↔ ∀ a, 1 ≤ a → a < n → widthBound a < widthBound n := by
  constructor
  · intro hR a ha1 han
    obtain ⟨c, hc1, hcn, hmax⟩ := exists_blockFactor_max (n := n - 1) (by omega)
    have hac : tau a ≤ tau c :=
      tau_le_of_blockFactor_le hc1 ha1 fun k hk1 hka => hmax k hk1 (by omega)
    have hcn' : tau c + 1 ≤ tau n :=
      tau_add_one_le (by omega) (hmax 1 le_rfl (by omega))
        ((upperRecord_iff_blockFactor n).mp hR c hc1 (by omega)).le
    have hw : (widthBound a : ℚ) ≤ tau a := (natCast_le_tau_iff _ a).mpr le_rfl
    have hsucc : ((widthBound a + 1 : ℕ) : ℚ) ≤ tau n := by
      push_cast
      linarith
    exact (natCast_le_tau_iff _ n).mp hsucc
  · intro h
    by_contra hR
    obtain ⟨a, ha1, han, hlt⟩ := exists_tau_lt_of_not_upperRecord hR
    exact absurd (h a ha1 han) (widthBound_le_of_tau_le hlt.le).not_gt

/-- With a the last upper record Order up to n, no Order from 1 to n has a block
    factor above that of a. -/
theorem blockFactor_le_of_upperRecord {a n : ℕ} (hR : UpperRecord a)
    (hno : ∀ k, a < k → k ≤ n → ¬UpperRecord k) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    blockFactor k ≤ blockFactor a := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_trichotomy k a with hlt | heq | hgt
    · exact ((upperRecord_iff_blockFactor a).mp hR k hk1 hlt).le
    · rw [heq]
    · have hnot := hno k hgt hkn
      rw [upperRecord_iff_blockFactor] at hnot
      push Not at hnot
      obtain ⟨c, hc1, hck, hc⟩ := hnot
      exact hc.trans (ih c hck hc1 (by omega))

/-- With a the last upper record Order up to n, the width bound of every Order up to n
    is at most that of a. -/
theorem widthBound_le_of_upperRecord {a n : ℕ} (ha : 1 ≤ a) (hR : UpperRecord a)
    (hno : ∀ k, a < k → k ≤ n → ¬UpperRecord k) {m : ℕ} (hmn : m ≤ n) :
    widthBound m ≤ widthBound a := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]
    simp [widthBound]
  · exact widthBound_le_of_tau_le (tau_le_of_blockFactor_le ha hpos fun k hk1 hkm =>
      blockFactor_le_of_upperRecord hR hno k hk1 (by omega))

/-- A verified range that reaches the width bound of the last upper record Order up
    to n gives ClassDrops at every Order up to n. -/
theorem classDropsAt_of_verified_record (X : ℕ)
    (hX : ∀ x, 1 < x → x ≤ X → ∀ m, Admissible (tBits x m) → tStep^[m] x < x)
    {a n : ℕ} (ha : 1 ≤ a) (hR : UpperRecord a)
    (hno : ∀ k, a < k → k ≤ n → ¬UpperRecord k) (haX : widthBound a ≤ X)
    {m : ℕ} (hmn : m ≤ n) : ClassDropsAt m :=
  classDropsAt_of_verified X hX m ((widthBound_le_of_upperRecord ha hR hno hmn).trans haX)

end AcceleratedCollatz
