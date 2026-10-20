-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSmoothNextQ

/-!
  The Orders below a + b sorted by block factor, for odd q ≥ 3. Here a is the last
  lower and b the last upper record Order below some N ≥ 2 (`LastRecordsQ`; a = b = 1
  for N = 2, `lastRecordsQ_two`). Then N ≤ a + b (`le_add_of_lastRecordsQ`), and the
  next record Order of either kind is a + b (`eq_add_of_lowerRecordQ`,
  `eq_add_of_upperRecordQ`), so a and b are also the last ones below a + b
  (`lastRecordsQ_add`). Every N ≥ 2 has such a pair (`exists_lastRecordsQ`), only one
  (`lastRecordsQ_unique`), with a p2Q(b) + b = b p2Q(a) + 1 (`lastRecordsQ_det`), so a
  and b are coprime (`coprime_of_lastRecordsQ`). The block factor rises along
  k a mod (a + b) for k = 0, 1, …, a + b - 1 (`blockFactorQ_mul_mod_lt`), and every Order
  below a + b occurs there (`exists_mul_mod_eq`): the Orders below N, sorted by block
  factor, are the values of k a mod (a + b) below N, in the order of k.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- a is the last lower record Order below N, and b the last upper record Order
    below N. -/
structure LastRecordsQ (q a b N : ℕ) : Prop where
  one_le_lower : 1 ≤ a
  lower_lt : a < N
  lower : LowerRecordQ q a
  no_lower : ∀ x, a < x → x < N → ¬LowerRecordQ q x
  one_le_upper : 1 ≤ b
  upper_lt : b < N
  upper : UpperRecordQ q b
  no_upper : ∀ x, b < x → x < N → ¬UpperRecordQ q x

/-- Below 2 both last record Orders are 1. -/
theorem lastRecordsQ_two (q : ℕ) : LastRecordsQ q 1 1 2 where
  one_le_lower := le_rfl
  lower_lt := by norm_num
  lower := fun a h1 h2 => absurd h2 (by omega)
  no_lower := fun x h1 h2 => absurd h2 (by omega)
  one_le_upper := le_rfl
  upper_lt := by norm_num
  upper := fun a h1 h2 => absurd h2 (by omega)
  no_upper := fun x h1 h2 => absurd h2 (by omega)

/-- N ≤ a + b. -/
theorem le_add_of_lastRecordsQ (hodd : Odd q) (hq : 3 ≤ q) {a b N : ℕ}
    (h : LastRecordsQ q a b N) : N ≤ a + b := by
  by_contra hlt
  push Not at hlt
  have h1 := p2Q_add_of_lowerRecordQ hq h.lower h.no_lower h.one_le_upper hlt
  have h2 := p2Q_add_of_upperRecordQ hodd hq h.upper h.no_upper h.one_le_lower (by omega)
  rw [Nat.add_comm b a] at h2
  omega

/-- An Order N ≥ 2 is not both an upper and a lower record Order. -/
theorem not_lowerRecordQ_of_upperRecordQ (hq : 3 ≤ q) {N : ℕ} (hN : 2 ≤ N)
    (hU : UpperRecordQ q N) : ¬LowerRecordQ q N := by
  intro hL
  have h1 := (lowerRecordQ_iff_add hq N).mp hL 1 le_rfl (by omega)
  have h2 := (upperRecordQ_iff_add hq N).mp hU 1 le_rfl (by omega)
  omega

/-- A lower record Order N, with last record Orders a and b below it, is a + b. -/
theorem eq_add_of_lowerRecordQ (hq : 3 ≤ q) {a b N : ℕ} (h : LastRecordsQ q a b N)
    (hR : LowerRecordQ q N) : N = a + b := by
  have ha1 := h.one_le_lower
  have haN := h.lower_lt
  have hb1 := h.one_le_upper
  have hbN := h.upper_lt
  have hU := upperRecordQ_sub_of_lowerRecordQ hq ha1 haN h.lower hR h.no_lower
  have hle : N - a ≤ b := by
    by_contra hgt
    push Not at hgt
    exact h.no_upper (N - a) hgt (by omega) hU
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · omega
  · exfalso
    have hN := (lowerRecordQ_iff_add hq N).mp hR
    have h1 := hN a ha1 haN
    have h2 := hN b hb1 hbN
    have h3 := (lowerRecordQ_iff_add hq a).mp h.lower (N - b) (by omega) (by omega)
    have h4 := (upperRecordQ_iff_add hq b).mp h.upper (N - a) (by omega) hlt
    have he : a - (N - b) = b - (N - a) := by
      omega
    rw [he] at h3
    omega

/-- An upper record Order N, with last record Orders a and b below it, is a + b. -/
theorem eq_add_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {a b N : ℕ}
    (h : LastRecordsQ q a b N) (hR : UpperRecordQ q N) : N = a + b := by
  have ha1 := h.one_le_lower
  have haN := h.lower_lt
  have hb1 := h.one_le_upper
  have hbN := h.upper_lt
  have hL := lowerRecordQ_sub_of_upperRecordQ hodd hq hb1 hbN h.upper hR h.no_upper
  have hle : N - b ≤ a := by
    by_contra hgt
    push Not at hgt
    exact h.no_lower (N - b) hgt (by omega) hL
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · omega
  · exfalso
    have hN := (upperRecordQ_iff_add hq N).mp hR
    have h1 := hN b hb1 hbN
    have h2 := hN a ha1 haN
    have h3 := (upperRecordQ_iff_add hq b).mp h.upper (N - a) (by omega) (by omega)
    have h4 := (lowerRecordQ_iff_add hq a).mp h.lower (N - b) (by omega) hlt
    have he : b - (N - a) = a - (N - b) := by
      omega
    rw [he] at h3
    omega

/-- When N is no record Order, a and b are also the last record Orders below N + 1. -/
theorem lastRecordsQ_succ {a b N : ℕ} (h : LastRecordsQ q a b N) (hL : ¬LowerRecordQ q N)
    (hU : ¬UpperRecordQ q N) : LastRecordsQ q a b (N + 1) where
  one_le_lower := h.one_le_lower
  lower_lt := Nat.lt_succ_of_lt h.lower_lt
  lower := h.lower
  no_lower := by
    intro x hax hx
    rcases Nat.lt_or_ge x N with hxN | hxN
    · exact h.no_lower x hax hxN
    · have hx' : x = N := by
        omega
      rw [hx']
      exact hL
  one_le_upper := h.one_le_upper
  upper_lt := Nat.lt_succ_of_lt h.upper_lt
  upper := h.upper
  no_upper := by
    intro x hbx hx
    rcases Nat.lt_or_ge x N with hxN | hxN
    · exact h.no_upper x hbx hxN
    · have hx' : x = N := by
        omega
      rw [hx']
      exact hU

/-- When N is a lower record Order, N and b are the last record Orders below N + 1. -/
theorem lastRecordsQ_succ_lower (hq : 3 ≤ q) {a b N : ℕ} (h : LastRecordsQ q a b N)
    (hR : LowerRecordQ q N) : LastRecordsQ q N b (N + 1) where
  one_le_lower := le_trans h.one_le_lower (le_of_lt h.lower_lt)
  lower_lt := Nat.lt_succ_self N
  lower := hR
  no_lower := fun x h1 h2 => absurd h2 (by omega)
  one_le_upper := h.one_le_upper
  upper_lt := Nat.lt_succ_of_lt h.upper_lt
  upper := h.upper
  no_upper := by
    intro x hbx hx hUx
    rcases Nat.lt_or_ge x N with hxN | hxN
    · exact h.no_upper x hbx hxN hUx
    · have hx' : x = N := by
        omega
      rw [hx'] at hUx
      have h1 := h.one_le_lower
      have h2 := h.lower_lt
      exact not_lowerRecordQ_of_upperRecordQ hq (by omega) hUx hR

/-- When N is an upper record Order, a and N are the last record Orders below N + 1. -/
theorem lastRecordsQ_succ_upper (hq : 3 ≤ q) {a b N : ℕ} (h : LastRecordsQ q a b N)
    (hR : UpperRecordQ q N) : LastRecordsQ q a N (N + 1) where
  one_le_lower := h.one_le_lower
  lower_lt := Nat.lt_succ_of_lt h.lower_lt
  lower := h.lower
  no_lower := by
    intro x hax hx hLx
    rcases Nat.lt_or_ge x N with hxN | hxN
    · exact h.no_lower x hax hxN hLx
    · have hx' : x = N := by
        omega
      rw [hx'] at hLx
      have h1 := h.one_le_lower
      have h2 := h.lower_lt
      exact not_lowerRecordQ_of_upperRecordQ hq (by omega) hR hLx
  one_le_upper := le_trans h.one_le_upper (le_of_lt h.upper_lt)
  upper_lt := Nat.lt_succ_self N
  upper := hR
  no_upper := fun x h1 h2 => absurd h2 (by omega)

/-- a and b are also the last record Orders below a + b. -/
theorem lastRecordsQ_add (hodd : Odd q) (hq : 3 ≤ q) {a b N : ℕ} (h : LastRecordsQ q a b N) :
    LastRecordsQ q a b (a + b) := by
  have hall : ∀ K, N ≤ K → K ≤ a + b → LastRecordsQ q a b K := by
    intro K hNK
    induction K, hNK using Nat.le_induction with
    | base =>
      intro _
      exact h
    | succ K hNK ih =>
      intro hK
      have hK' := ih (by omega)
      apply lastRecordsQ_succ hK'
      · intro hR
        have := eq_add_of_lowerRecordQ hq hK' hR
        omega
      · intro hR
        have := eq_add_of_upperRecordQ hodd hq hK' hR
        omega
  exact hall (a + b) (le_add_of_lastRecordsQ hodd hq h) le_rfl

/-- The last record Orders below N are unique. -/
theorem lastRecordsQ_unique {a b a' b' N : ℕ} (h : LastRecordsQ q a b N)
    (h' : LastRecordsQ q a' b' N) : a = a' ∧ b = b' := by
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_trichotomy a a' with hlt | heq | hgt
    · exact absurd h'.lower (h.no_lower a' hlt h'.lower_lt)
    · exact heq
    · exact absurd h.lower (h'.no_lower a hgt h.lower_lt)
  · rcases Nat.lt_trichotomy b b' with hlt | heq | hgt
    · exact absurd h'.upper (h.no_upper b' hlt h'.upper_lt)
    · exact heq
    · exact absurd h.upper (h'.no_upper b hgt h.upper_lt)

/-- Every N ≥ 2 has last record Orders a and b below it, with
    a p2Q(b) + b = b p2Q(a) + 1. -/
theorem exists_lastRecordsQ_det (hodd : Odd q) (hq : 3 ≤ q) {N : ℕ} (hN : 2 ≤ N) :
    ∃ a b, LastRecordsQ q a b N ∧ a * p2Q q b + b = b * p2Q q a + 1 := by
  induction N, hN using Nat.le_induction with
  | base => exact ⟨1, 1, lastRecordsQ_two q, by omega⟩
  | succ N hN ih =>
    obtain ⟨a, b, h, hd⟩ := ih
    by_cases hL : LowerRecordQ q N
    · have hab := eq_add_of_lowerRecordQ hq h hL
      have hp := (lowerRecordQ_iff_add hq N).mp hL a h.one_le_lower h.lower_lt
      have hNa : N - a = b := by
        omega
      rw [hNa] at hp
      refine ⟨N, b, lastRecordsQ_succ_lower hq h hL, ?_⟩
      rw [hp, hab]
      linarith
    · by_cases hU : UpperRecordQ q N
      · have hab := eq_add_of_upperRecordQ hodd hq h hU
        have hp := (upperRecordQ_iff_add hq N).mp hU b h.one_le_upper h.upper_lt
        have hNb : N - b = a := by
          omega
        rw [hNb] at hp
        refine ⟨a, N, lastRecordsQ_succ_upper hq h hU, ?_⟩
        have hmul : a * (p2Q q N + 1) = a * (p2Q q b + p2Q q a) := by
          rw [hp]
        rw [hab] at hmul ⊢
        linarith
      · exact ⟨a, b, lastRecordsQ_succ h hL hU, hd⟩

/-- Every N ≥ 2 has last record Orders below it. -/
theorem exists_lastRecordsQ (hodd : Odd q) (hq : 3 ≤ q) {N : ℕ} (hN : 2 ≤ N) :
    ∃ a b, LastRecordsQ q a b N := by
  obtain ⟨a, b, h, _⟩ := exists_lastRecordsQ_det hodd hq hN
  exact ⟨a, b, h⟩

/-- a p2Q(b) + b = b p2Q(a) + 1. -/
theorem lastRecordsQ_det (hodd : Odd q) (hq : 3 ≤ q) {a b N : ℕ} (h : LastRecordsQ q a b N) :
    a * p2Q q b + b = b * p2Q q a + 1 := by
  have h1 := h.one_le_lower
  have h2 := h.lower_lt
  obtain ⟨a', b', h', hd⟩ := exists_lastRecordsQ_det hodd hq (N := N) (by omega)
  obtain ⟨ha, hb⟩ := lastRecordsQ_unique h h'
  rw [ha, hb]
  exact hd

/-- a and b are coprime. -/
theorem coprime_of_lastRecordsQ (hodd : Odd q) (hq : 3 ≤ q) {a b N : ℕ}
    (h : LastRecordsQ q a b N) : Nat.Coprime a b := by
  have hd := lastRecordsQ_det hodd hq h
  have hga : Nat.gcd a b ∣ a * p2Q q b + b :=
    Dvd.dvd.add (Dvd.dvd.mul_right (Nat.gcd_dvd_left a b) _) (Nat.gcd_dvd_right a b)
  have hgb : Nat.gcd a b ∣ b * p2Q q a := Dvd.dvd.mul_right (Nat.gcd_dvd_right a b) _
  rw [hd] at hga
  exact Nat.dvd_one.mp ((Nat.dvd_add_right hgb).mp hga)

/-- (k + 1) a mod M is k a mod M, plus a, mod M. -/
theorem succ_mul_mod (k a M : ℕ) : (k + 1) * a % M = (k * a % M + a) % M := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mod_add_mod]

/-- Adding a mod (a + b) raises the block factor of every Order below a + b except b. -/
theorem blockFactorQ_lt_add_mod (hodd : Odd q) (hq : 3 ≤ q) {a b N : ℕ}
    (h : LastRecordsQ q a b N) {x : ℕ} (hx : x < a + b) (hxb : x ≠ b) :
    blockFactorQ q x < blockFactorQ q ((x + a) % (a + b)) := by
  have hM := lastRecordsQ_add hodd hq h
  have ha1 := h.one_le_lower
  rcases Nat.lt_or_ge x b with hlt | hge
  · rw [Nat.mod_eq_of_lt (by omega)]
    rcases Nat.eq_zero_or_pos x with h0 | hpos
    · have hiff := blockFactorQ_lt_add_iff hodd hq 0 ha1
      rw [Nat.zero_add, p2Q_zero] at hiff
      rw [h0, Nat.zero_add]
      exact hiff.mpr (Nat.add_comm _ _)
    · have hadd := p2Q_add_of_lowerRecordQ hq hM.lower hM.no_lower hpos (by omega)
      rw [blockFactorQ_lt_add_iff hodd hq x ha1, Nat.add_comm x a]
      omega
  · have he : x + a = x - b + (a + b) := by
      omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hadd := p2Q_add_of_upperRecordQ hodd hq hM.upper hM.no_upper (i := x - b)
      (by omega) (by omega)
    have hiff := blockFactorQ_add_lt_iff hq (x - b) b
    rw [Nat.sub_add_cancel hge] at hiff
    rw [Nat.add_sub_cancel' hge] at hadd
    exact hiff.mpr (by omega)

/-- k a mod (a + b) is not b for k + 1 < a + b. -/
theorem mul_mod_ne_upper (hodd : Odd q) (hq : 3 ≤ q) {a b N : ℕ} (h : LastRecordsQ q a b N)
    {k : ℕ} (hk : k + 1 < a + b) : k * a % (a + b) ≠ b := by
  intro heq
  have h0 : (k + 1) * a % (a + b) = 0 := by
    rw [succ_mul_mod, heq, Nat.add_comm b a, Nat.mod_self]
  have hdvd : a + b ∣ (k + 1) * a := Nat.dvd_of_mod_eq_zero h0
  have hcop : Nat.Coprime (a + b) a := by
    rw [Nat.coprime_self_add_left]
    exact (coprime_of_lastRecordsQ hodd hq h).symm
  have hle := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hdvd)
  omega

/-- The block factor rises along k a mod (a + b), k = 0, 1, …, a + b - 1. -/
theorem blockFactorQ_mul_mod_lt (hodd : Odd q) (hq : 3 ≤ q) {a b N : ℕ}
    (h : LastRecordsQ q a b N) {k k' : ℕ} (hkk : k < k') (hk' : k' < a + b) :
    blockFactorQ q (k * a % (a + b)) < blockFactorQ q (k' * a % (a + b)) := by
  have ha1 := h.one_le_lower
  induction k' with
  | zero => omega
  | succ m ih =>
    have hstep : blockFactorQ q (m * a % (a + b)) < blockFactorQ q ((m + 1) * a % (a + b)) := by
      rw [succ_mul_mod]
      exact blockFactorQ_lt_add_mod hodd hq h (Nat.mod_lt _ (by omega))
        (mul_mod_ne_upper hodd hq h hk')
    rcases Nat.lt_or_ge k m with hlt | hge
    · exact lt_trans (ih hlt (by omega)) hstep
    · have hkm : k = m := by
        omega
      rw [hkm]
      exact hstep

/-- Every Order below a + b is k a mod (a + b) for some k below a + b. -/
theorem exists_mul_mod_eq (hodd : Odd q) (hq : 3 ≤ q) {a b N : ℕ} (h : LastRecordsQ q a b N)
    {i : ℕ} (hi : i < a + b) : ∃ k, k < a + b ∧ k * a % (a + b) = i := by
  have ha1 := h.one_le_lower
  have hb1 := h.one_le_upper
  have hcop : Nat.Coprime a (a + b) := by
    rw [Nat.coprime_self_add_right]
    exact coprime_of_lastRecordsQ hodd hq h
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  refine ⟨i * m % (a + b), Nat.mod_lt _ (by omega), ?_⟩
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_comm m a, Nat.mul_mod, hm, Nat.mul_one,
    Nat.mod_mod, Nat.mod_eq_of_lt hi]

end AcceleratedCollatz
