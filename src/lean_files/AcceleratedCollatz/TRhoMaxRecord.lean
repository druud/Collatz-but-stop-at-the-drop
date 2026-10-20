-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhoMaxBound
import AcceleratedCollatz.TWidthRecord

/-!
  The records of rhoMax(n) / d(n), d(n) = 2^p2(n) - 3^n, and of its floor
  `widthBoundMax`, are exactly the upper record Orders (`upperRecord_iff_rmax`,
  `upperRecord_iff_widthBoundMax`), as for tau (`upperRecord_iff_tau`). At a split
  a + b where p2 is additive at a + j for every 1 ≤ j < b, rhoMax(a + b) is
  3^b rhoMax(a) + 2^p2(a) rhoMax(b) minus 3^(b-1) 2^(p2(a)-1) (`rhoMax_add`) and d(a + b) is
  3^b d(a) + 2^p2(a) d(b), so the ratio
  at a + b is below a mediant of those at a and b (`rmax_add_lt`); a later Order with a
  block factor at least as large has a ratio at least as large
  (`rmax_le_of_le_of_blockFactor_le`); between neighbouring candidates the ratio grows by
  at least 1 once the block factor is that of Order 3 or more (`rmax_add_one_le`).
-/

namespace AcceleratedCollatz

/-- rhoMax(n) / (2^p2(n) - 3^n). -/
def rmax (n : ℕ) : ℚ := rhoMax n / (2 ^ p2_of n - 3 ^ n)

theorem one_le_p2_of (x : ℕ) : 1 ≤ p2_of x := by
  unfold p2_of
  omega

/-- x^k = x x^(k-1) for k ≥ 1. -/
theorem pow_eq_mul_pow_pred {M : Type*} [Monoid M] (x : M) {k : ℕ} (hk : 1 ≤ k) :
    x ^ k = x * x ^ (k - 1) := by
  rw [← pow_succ', Nat.sub_add_cancel hk]

/-- widthBoundMax n is the largest natural number at most rmax n. -/
theorem natCast_le_rmax_iff (w n : ℕ) : (w : ℚ) ≤ rmax n ↔ w ≤ widthBoundMax n := by
  have hle : 3 ^ n ≤ 2 ^ p2_of n := (p2_of_spec n).le
  have hpos : 0 < 2 ^ p2_of n - 3 ^ n := Nat.sub_pos_of_lt (p2_of_spec n)
  unfold rmax widthBoundMax
  rw [le_div_iff₀ (tau_den_pos n), Nat.le_div_iff_mul_le hpos]
  constructor
  · intro h
    have h' : ((w * (2 ^ p2_of n - 3 ^ n) : ℕ) : ℚ) ≤ ((rhoMax n : ℕ) : ℚ) := by
      rw [Nat.cast_mul, Nat.cast_sub hle]
      push_cast
      exact h
    exact_mod_cast h'
  · intro h
    have h' : ((w * (2 ^ p2_of n - 3 ^ n) : ℕ) : ℚ) ≤ ((rhoMax n : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hle] at h'
    push_cast at h'
    exact h'

/-- A larger ratio has a floor at least as large. -/
theorem widthBoundMax_le_of_rmax_le {m a : ℕ} (h : rmax m ≤ rmax a) :
    widthBoundMax m ≤ widthBoundMax a :=
  (natCast_le_rmax_iff _ a).mp (((natCast_le_rmax_iff _ m).mpr le_rfl).trans h)

/-- 3^t rhoMax(m) ≤ rhoMax(m + t). -/
theorem three_pow_mul_rhoMax_le (m t : ℕ) : 3 ^ t * rhoMax m ≤ rhoMax (m + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← Nat.add_assoc, rhoMax_succ, pow_succ]
    have h := Nat.mul_le_mul_left 3 ih
    calc 3 ^ t * 3 * rhoMax m = 3 * (3 ^ t * rhoMax m) := by ring
      _ ≤ 3 * rhoMax (m + t) := h
      _ ≤ 3 * rhoMax (m + t) + 2 ^ (p2_of (m + t) - 1) := Nat.le_add_right _ _

/-- 3^t rhoMax(c) + 3^(t-1) 2^(p2(c)-1) ≤ rhoMax(c + t) for t ≥ 1. -/
theorem rhoMax_add_ge (c t : ℕ) (ht : 1 ≤ t) :
    3 ^ t * rhoMax c + 3 ^ (t - 1) * 2 ^ (p2_of c - 1) ≤ rhoMax (c + t) := by
  induction t, ht using Nat.le_induction with
  | base =>
    rw [rhoMax_succ]
    simp
  | succ t ht ih =>
    rw [← Nat.add_assoc, rhoMax_succ]
    have e1 : 3 ^ (t + 1) * rhoMax c + 3 ^ (t + 1 - 1) * 2 ^ (p2_of c - 1) =
        3 * (3 ^ t * rhoMax c + 3 ^ (t - 1) * 2 ^ (p2_of c - 1)) := by
      have h3 : 3 ^ t = 3 * 3 ^ (t - 1) := pow_eq_mul_pow_pred 3 ht
      rw [Nat.add_sub_cancel, pow_succ, h3]
      ring
    rw [e1]
    have h := Nat.mul_le_mul_left 3 ih
    exact le_trans h (Nat.le_add_right _ _)

/-- At a split a + b with p2 additive at a + j for 1 ≤ j < b:
    rhoMax(a + b) + 3^(b-1) 2^(p2(a)-1) = 3^b rhoMax(a) + 2^p2(a) rhoMax(b). -/
theorem rhoMax_add (a b : ℕ) (hb : 1 ≤ b)
    (hp : ∀ j, 1 ≤ j → j < b → p2_of (a + j) = p2_of a + p2_of j) :
    rhoMax (a + b) + 3 ^ (b - 1) * 2 ^ (p2_of a - 1) =
      3 ^ b * rhoMax a + 2 ^ p2_of a * rhoMax b := by
  induction b, hb using Nat.le_induction with
  | base =>
    have h1 : rhoMax 1 = 1 := by decide
    rw [rhoMax_succ, h1]
    have h2 : 2 ^ p2_of a = 2 * 2 ^ (p2_of a - 1) := pow_eq_mul_pow_pred 2 (one_le_p2_of a)
    rw [h2]
    ring
  | succ b hb ih =>
    have ih' := ih fun j hj1 hjb => hp j hj1 (by omega)
    have hpb := hp b hb (by omega)
    have hR1 : rhoMax (a + (b + 1)) =
        3 * rhoMax (a + b) + 2 ^ p2_of a * 2 ^ (p2_of b - 1) := by
      have hsub : p2_of a + p2_of b - 1 = p2_of a + (p2_of b - 1) := by
        have := one_le_p2_of b
        omega
      rw [← Nat.add_assoc, rhoMax_succ, hpb, hsub, pow_add]
    have h3 : 3 ^ b = 3 * 3 ^ (b - 1) := pow_eq_mul_pow_pred 3 hb
    have hA : 3 ^ (b + 1 - 1) * 2 ^ (p2_of a - 1) = 3 * (3 ^ (b - 1) * 2 ^ (p2_of a - 1)) := by
      rw [Nat.add_sub_cancel, h3]
      ring
    have hB : 3 ^ (b + 1) * rhoMax a = 3 * (3 ^ b * rhoMax a) := by ring
    have hC : 2 ^ p2_of a * rhoMax (b + 1) =
        3 * (2 ^ p2_of a * rhoMax b) + 2 ^ p2_of a * 2 ^ (p2_of b - 1) := by
      rw [rhoMax_succ]
      ring
    rw [hR1, hA, hB, hC]
    omega

/-- At a split a + b with p2 additive at a + j for 1 ≤ j ≤ b and rmax(b) ≤ rmax(a):
    rmax(a + b) < rmax(a). -/
theorem rmax_add_lt {a b : ℕ} (hb : 1 ≤ b)
    (hp : ∀ j, 1 ≤ j → j ≤ b → p2_of (a + j) = p2_of a + p2_of j)
    (h : rmax b ≤ rmax a) : rmax (a + b) < rmax a := by
  have hid := rhoMax_add a b hb fun j hj1 hjb => hp j hj1 hjb.le
  have hpab := hp b hb le_rfl
  have hDa := tau_den_pos a
  have hDb := tau_den_pos b
  have hDn := tau_den_pos (a + b)
  have hD : (2 : ℚ) ^ p2_of (a + b) - 3 ^ (a + b) =
      3 ^ b * (2 ^ p2_of a - 3 ^ a) + 2 ^ p2_of a * (2 ^ p2_of b - 3 ^ b) := by
    rw [hpab, pow_add, pow_add]
    ring
  have hidQ : (rhoMax (a + b) : ℚ) + 3 ^ (b - 1) * 2 ^ (p2_of a - 1) =
      3 ^ b * rhoMax a + 2 ^ p2_of a * rhoMax b := by
    exact_mod_cast hid
  have heps : (0 : ℚ) < 3 ^ (b - 1) * 2 ^ (p2_of a - 1) := by positivity
  unfold rmax at h ⊢
  rw [div_le_div_iff₀ hDb hDa] at h
  rw [div_lt_div_iff₀ hDn hDa, hD]
  have h2 : (0 : ℚ) ≤ 2 ^ p2_of a := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h h2, mul_pos heps hDa]

/-- A later Order with a block factor at least as large has rmax at least as large. -/
theorem rmax_le_of_le_of_blockFactor_le {m a : ℕ} (hma : m ≤ a)
    (h : blockFactor m ≤ blockFactor a) : rmax m ≤ rmax a := by
  obtain ⟨t, rfl⟩ : ∃ t, a = m + t := ⟨a - m, by omega⟩
  have hR : ((3 ^ t * rhoMax m : ℕ) : ℚ) ≤ ((rhoMax (m + t) : ℕ) : ℚ) := by
    exact_mod_cast three_pow_mul_rhoMax_le m t
  push_cast at hR
  rw [blockFactor_le_iff] at h
  have hDm := tau_den_pos m
  have hDa := tau_den_pos (m + t)
  have h3m : (0 : ℚ) < 3 ^ m := by positivity
  have h3t : (0 : ℚ) < 3 ^ t := by positivity
  have hRm : (0 : ℚ) ≤ rhoMax m := by positivity
  unfold rmax
  rw [div_le_div_iff₀ hDm hDa]
  rw [pow_add] at h hDa ⊢
  have h' : (2 : ℚ) ^ p2_of (m + t) ≤ 3 ^ t * 2 ^ p2_of m := by
    have h'' : (3 : ℚ) ^ m * 2 ^ p2_of (m + t) ≤ 3 ^ m * (3 ^ t * 2 ^ p2_of m) := by
      linarith [h]
    exact le_of_mul_le_mul_left h'' h3m
  have hDD' : (2 : ℚ) ^ p2_of (m + t) - 3 ^ m * 3 ^ t ≤ 3 ^ t * (2 ^ p2_of m - 3 ^ m) := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hDD' hRm, mul_le_mul_of_nonneg_left hR hDm.le]

/-- A later Order with a larger block factor has a larger rmax (Order at least 1). -/
theorem rmax_lt_of_lt_of_blockFactor_lt {m a : ℕ} (hm : 1 ≤ m) (hma : m < a)
    (h : blockFactor m < blockFactor a) : rmax m < rmax a := by
  obtain ⟨t, rfl⟩ : ∃ t, a = m + t := ⟨a - m, by omega⟩
  have hR : ((3 ^ t * rhoMax m : ℕ) : ℚ) ≤ ((rhoMax (m + t) : ℕ) : ℚ) := by
    exact_mod_cast three_pow_mul_rhoMax_le m t
  push_cast at hR
  rw [blockFactor_lt_iff] at h
  have hDm := tau_den_pos m
  have hDa := tau_den_pos (m + t)
  have h3m : (0 : ℚ) < 3 ^ m := by positivity
  have h3t : (0 : ℚ) < 3 ^ t := by positivity
  have hRm1 : 1 ≤ rhoMax m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [rhoMax_succ]
    have := Nat.one_le_two_pow (n := p2_of k - 1)
    omega
  have hRm : (1 : ℚ) ≤ rhoMax m := by exact_mod_cast hRm1
  unfold rmax
  rw [div_lt_div_iff₀ hDm hDa]
  rw [pow_add] at h hDa ⊢
  have h' : (2 : ℚ) ^ p2_of (m + t) < 3 ^ t * 2 ^ p2_of m := by
    have h'' : (3 : ℚ) ^ m * 2 ^ p2_of (m + t) < 3 ^ m * (3 ^ t * 2 ^ p2_of m) := by
      linarith [h]
    exact lt_of_mul_lt_mul_left h'' h3m.le
  have hDD' : (2 : ℚ) ^ p2_of (m + t) - 3 ^ m * 3 ^ t < 3 ^ t * (2 ^ p2_of m - 3 ^ m) := by
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hDD' (by linarith : (0 : ℚ) < rhoMax m),
    mul_le_mul_of_nonneg_left hR hDm.le]

/-- If no Order from 1 to m has a block factor above that of a, then rmax(m) ≤ rmax(a),
    and rmax(m) < rmax(a) when a < m. -/
theorem rmax_le_and_lt_of_blockFactor_le {a : ℕ} (ha : 1 ≤ a) (m : ℕ) (hm : 1 ≤ m)
    (hdom : ∀ k, 1 ≤ k → k ≤ m → blockFactor k ≤ blockFactor a) :
    rmax m ≤ rmax a ∧ (a < m → rmax m < rmax a) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge a m with ham | hma
    · obtain ⟨b, rfl⟩ : ∃ b, m = a + b := ⟨m - a, by omega⟩
      have hb : 1 ≤ b := by omega
      have hp : ∀ j, 1 ≤ j → j ≤ b → p2_of (a + j) = p2_of a + p2_of j :=
        fun j hj1 hjb => p2_of_add_of_blockFactor_le hj1 (hdom (a + j) (by omega) (by omega))
      have hb' := (ih b (by omega) hb fun k hk1 hkb => hdom k hk1 (by omega)).1
      have hlt := rmax_add_lt hb hp hb'
      exact ⟨hlt.le, fun _ => hlt⟩
    · exact ⟨rmax_le_of_le_of_blockFactor_le hma (hdom m hm le_rfl),
        fun h => absurd h (by omega)⟩

theorem rmax_le_of_blockFactor_le {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m)
    (hdom : ∀ k, 1 ≤ k → k ≤ m → blockFactor k ≤ blockFactor a) : rmax m ≤ rmax a :=
  (rmax_le_and_lt_of_blockFactor_le ha m hm hdom).1

/-- An Order that is no upper record has an earlier Order with a larger rmax. -/
theorem exists_rmax_lt_of_not_upperRecord {n : ℕ} (h : ¬UpperRecord n) :
    ∃ a, 1 ≤ a ∧ a < n ∧ rmax n < rmax a := by
  rw [upperRecord_iff_blockFactor] at h
  push Not at h
  obtain ⟨c, hc1, hcn, hc⟩ := h
  obtain ⟨a, ha1, han, hmax⟩ := exists_blockFactor_max (n := n - 1) (by omega)
  refine ⟨a, ha1, by omega, (rmax_le_and_lt_of_blockFactor_le ha1 n (by omega)
    fun k hk1 hkn => ?_).2 (by omega)⟩
  rcases Nat.lt_or_ge k n with hlt | hge
  · exact hmax k hk1 (by omega)
  · have hk : k = n := by omega
    rw [hk]
    exact hc.trans (hmax c hc1 (by omega))

/-- The upper record Orders are the Orders at which rmax is above every earlier value. -/
theorem upperRecord_iff_rmax (n : ℕ) :
    UpperRecord n ↔ ∀ a, 1 ≤ a → a < n → rmax a < rmax n := by
  constructor
  · intro hR a ha1 han
    exact rmax_lt_of_lt_of_blockFactor_lt ha1 han
      ((upperRecord_iff_blockFactor n).mp hR a ha1 han)
  · intro h
    by_contra hR
    obtain ⟨a, ha1, han, hlt⟩ := exists_rmax_lt_of_not_upperRecord hR
    exact lt_asymm hlt (h a ha1 han)

/-- rmax(c) + 1 ≤ rmax(n) for c < n, when the block factor of c is at least that of
    Order 3 (27/32) and at most that of n. -/
theorem rmax_add_one_le {c n : ℕ} (hcn : c < n) (h3 : blockFactor 3 ≤ blockFactor c)
    (h : blockFactor c ≤ blockFactor n) : rmax c + 1 ≤ rmax n := by
  obtain ⟨t, rfl⟩ : ∃ t, n = c + t := ⟨n - c, by omega⟩
  have ht : 1 ≤ t := by omega
  have hR : ((3 ^ t * rhoMax c + 3 ^ (t - 1) * 2 ^ (p2_of c - 1) : ℕ) : ℚ) ≤
      ((rhoMax (c + t) : ℕ) : ℚ) := by
    exact_mod_cast rhoMax_add_ge c t ht
  push_cast at hR
  have hp3 : p2_of 3 = 5 := by decide
  rw [blockFactor_le_iff, hp3] at h3
  rw [blockFactor_le_iff] at h
  have hDc := tau_den_pos c
  have hDn := tau_den_pos (c + t)
  have h3t : (3 : ℚ) ^ t = 3 * 3 ^ (t - 1) := pow_eq_mul_pow_pred 3 ht
  have h2c : (2 : ℚ) ^ p2_of c = 2 * 2 ^ (p2_of c - 1) :=
    pow_eq_mul_pow_pred 2 (one_le_p2_of c)
  have hx : (0 : ℚ) < 3 ^ (t - 1) := by positivity
  have h3c : (0 : ℚ) < 3 ^ c := by positivity
  have hRc : (0 : ℚ) ≤ rhoMax c := by positivity
  -- 2^p2(n) ≤ 3^t 2^p2(c)
  have h' : (2 : ℚ) ^ p2_of (c + t) ≤ 3 ^ t * 2 ^ p2_of c := by
    have h'' : (3 : ℚ) ^ c * 2 ^ p2_of (c + t) ≤ 3 ^ c * (3 ^ t * 2 ^ p2_of c) := by
      have hh := h
      rw [pow_add] at hh
      linarith [hh]
    exact le_of_mul_le_mul_left h'' h3c
  -- d(n) ≤ 3^t d(c)
  have hDle : (2 : ℚ) ^ p2_of (c + t) - 3 ^ (c + t) ≤
      3 * 3 ^ (t - 1) * (2 ^ p2_of c - 3 ^ c) := by
    rw [pow_add, h3t]
    rw [h3t] at h'
    nlinarith
  -- 3 d(c) ≤ 2^(p2(c)-1)
  have h3D : 3 * (2 ^ p2_of c - 3 ^ c) ≤ (2 : ℚ) ^ (p2_of c - 1) := by
    rw [h2c] at h3 ⊢
    norm_num at h3
    nlinarith
  unfold rmax
  rw [div_add_one hDc.ne', div_le_div_iff₀ hDc hDn]
  rw [h3t] at hR
  nlinarith [mul_le_mul_of_nonneg_left hR hDc.le, mul_le_mul_of_nonneg_left hDle hRc,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3D hx.le) hDc.le,
    mul_le_mul_of_nonneg_right hDle hDc.le]

set_option linter.hashCommand false in
#guard [1, 2, 3].map widthBoundMax = [1, 0, 4]

/-- The upper record Orders are the Orders at which widthBoundMax is above every earlier
    value. -/
theorem upperRecord_iff_widthBoundMax (n : ℕ) :
    UpperRecord n ↔ ∀ a, 1 ≤ a → a < n → widthBoundMax a < widthBoundMax n := by
  constructor
  · intro hR a ha1 han
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · have hn : n = 2 ∨ n = 3 := by omega
      rcases hn with hn | hn
      · subst hn
        exfalso
        have := hR 1 le_rfl (by norm_num)
        have h2 : p2_of 2 = 4 := by decide
        have h1 : p2_of 1 = 2 := by decide
        rw [h2, h1] at this
        omega
      · subst hn
        have hw3 : widthBoundMax 3 = 4 := by decide
        have hw : widthBoundMax a ≤ 1 := by
          have ha : a = 1 ∨ a = 2 := by omega
          rcases ha with ha | ha
          · subst ha
            decide
          · subst ha
            decide
        omega
    · obtain ⟨c, hc1, hcn, hmax⟩ := exists_blockFactor_max (n := n - 1) (by omega)
      have hac : rmax a ≤ rmax c :=
        rmax_le_of_blockFactor_le hc1 ha1 fun k hk1 hka => hmax k hk1 (by omega)
      have hcn' : rmax c + 1 ≤ rmax n :=
        rmax_add_one_le (by omega) (hmax 3 (by norm_num) (by omega))
          ((upperRecord_iff_blockFactor n).mp hR c hc1 (by omega)).le
      have hw : (widthBoundMax a : ℚ) ≤ rmax a := (natCast_le_rmax_iff _ a).mpr le_rfl
      have hsucc : ((widthBoundMax a + 1 : ℕ) : ℚ) ≤ rmax n := by
        push_cast
        linarith
      exact (natCast_le_rmax_iff _ n).mp hsucc
  · intro h
    by_contra hR
    obtain ⟨a, ha1, han, hlt⟩ := exists_rmax_lt_of_not_upperRecord hR
    exact absurd (h a ha1 han) (widthBoundMax_le_of_rmax_le hlt.le).not_gt

end AcceleratedCollatz
