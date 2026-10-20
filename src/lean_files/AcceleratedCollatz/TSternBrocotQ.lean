-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TLastRecordsQ

/-!
  The record Orders on the Stern–Brocot walk towards log2 q, for odd q ≥ 3, in integers
  only. A point of the walk holds the last fraction below the target and the last one
  above it (`SBNode`), from 0/1 and 1/0 on (`sbRoot`); a step replaces one of them by
  their mediant p/n: the upper one when q^n < 2^p, that is when the mediant lies above
  log2 q, else the lower one (`sbStepQ`, `sbWalkQ`). The two fractions stay neighbours
  (`sbWalkQ_det`), the lower one below and the upper one above log2 q (`sbWalkQ_lo_lt`,
  `sbWalkQ_lt_hi`). The first p2Q(1) steps pass the integers (`sbWalkQ_int`,
  `sbWalkQ_int_end`). From there on the walk holds (p2Q(a) - 1)/a and p2Q(b)/b, with a
  and b the last lower and upper record Orders below a + b (`sbWalkQ_records`), and a + b
  is the next record Order: an upper one when p2Q(a + b) + 1 = p2Q(a) + p2Q(b), else a
  lower one (`record_add_of_lastRecordsQ`). So the upper record Orders n ≥ 1 are exactly
  the denominators of the fractions above log2 q on the walk
  (`upperRecordQ_iff_sbWalkQ`), with numerator p2Q(n) (`sbWalkQ_hiNum`), and the lower
  record Orders n ≥ 1 exactly the denominators of the fractions below it
  (`lowerRecordQ_iff_sbWalkQ`), from step p2Q(1) on with numerator p2Q(n) - 1
  (`sbWalkQ_loNum`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- A point of the Stern–Brocot walk: the last fraction below the target and the last
    fraction above it. -/
structure SBNode where
  /-- Numerator of the fraction below. -/
  loNum : ℕ
  /-- Denominator of the fraction below. -/
  loDen : ℕ
  /-- Numerator of the fraction above. -/
  hiNum : ℕ
  /-- Denominator of the fraction above. -/
  hiDen : ℕ
  deriving DecidableEq, Repr

/-- The root of the tree: between 0/1 and 1/0. -/
def sbRoot : SBNode := ⟨0, 1, 1, 0⟩

/-- One step towards log2 q: the mediant p/n of the two fractions replaces the upper one
    when q^n < 2^p, else the lower one. -/
def sbStepQ (q : ℕ) (s : SBNode) : SBNode :=
  if q ^ (s.loDen + s.hiDen) < 2 ^ (s.loNum + s.hiNum) then
    ⟨s.loNum, s.loDen, s.loNum + s.hiNum, s.loDen + s.hiDen⟩
  else
    ⟨s.loNum + s.hiNum, s.loDen + s.hiDen, s.hiNum, s.hiDen⟩

/-- The walk towards log2 q after k steps. -/
def sbWalkQ (q k : ℕ) : SBNode := (sbStepQ q)^[k] sbRoot

theorem sbWalkQ_succ (q k : ℕ) : sbWalkQ q (k + 1) = sbStepQ q (sbWalkQ q k) :=
  Function.iterate_succ_apply' _ _ _

theorem sbStepQ_of_lt {s : SBNode} (h : q ^ (s.loDen + s.hiDen) < 2 ^ (s.loNum + s.hiNum)) :
    sbStepQ q s = ⟨s.loNum, s.loDen, s.loNum + s.hiNum, s.loDen + s.hiDen⟩ := by
  simp only [sbStepQ, h, ↓reduceIte]

theorem sbStepQ_of_not_lt {s : SBNode}
    (h : ¬q ^ (s.loDen + s.hiDen) < 2 ^ (s.loNum + s.hiNum)) :
    sbStepQ q s = ⟨s.loNum + s.hiNum, s.loDen + s.hiDen, s.hiNum, s.hiDen⟩ := by
  simp only [sbStepQ, h, ↓reduceIte]

/-- A step keeps one denominator and replaces the other by the sum of the two. -/
theorem sbStepQ_den (q : ℕ) (s : SBNode) :
    ((sbStepQ q s).loDen = s.loDen ∧ (sbStepQ q s).hiDen = s.loDen + s.hiDen) ∨
      ((sbStepQ q s).loDen = s.loDen + s.hiDen ∧ (sbStepQ q s).hiDen = s.hiDen) := by
  by_cases h : q ^ (s.loDen + s.hiDen) < 2 ^ (s.loNum + s.hiNum)
  · rw [sbStepQ_of_lt h]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [sbStepQ_of_not_lt h]
    exact Or.inr ⟨rfl, rfl⟩

/-! ### The walk is a Stern–Brocot path towards log2 q -/

/-- The two fractions of the walk are neighbours: their cross difference is 1. -/
theorem sbWalkQ_det (q k : ℕ) :
    (sbWalkQ q k).loDen * (sbWalkQ q k).hiNum =
      (sbWalkQ q k).loNum * (sbWalkQ q k).hiDen + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sbWalkQ_succ]
    by_cases h : q ^ ((sbWalkQ q k).loDen + (sbWalkQ q k).hiDen) <
        2 ^ ((sbWalkQ q k).loNum + (sbWalkQ q k).hiNum)
    · rw [sbStepQ_of_lt h]
      change (sbWalkQ q k).loDen * ((sbWalkQ q k).loNum + (sbWalkQ q k).hiNum) =
        (sbWalkQ q k).loNum * ((sbWalkQ q k).loDen + (sbWalkQ q k).hiDen) + 1
      linarith
    · rw [sbStepQ_of_not_lt h]
      change ((sbWalkQ q k).loDen + (sbWalkQ q k).hiDen) * (sbWalkQ q k).hiNum =
        ((sbWalkQ q k).loNum + (sbWalkQ q k).hiNum) * (sbWalkQ q k).hiDen + 1
      linarith

/-- The fraction above lies above log2 q. -/
theorem sbWalkQ_lt_hi (q k : ℕ) : q ^ (sbWalkQ q k).hiDen < 2 ^ (sbWalkQ q k).hiNum := by
  induction k with
  | zero =>
    change q ^ 0 < 2 ^ 1
    norm_num
  | succ k ih =>
    rw [sbWalkQ_succ]
    by_cases h : q ^ ((sbWalkQ q k).loDen + (sbWalkQ q k).hiDen) <
        2 ^ ((sbWalkQ q k).loNum + (sbWalkQ q k).hiNum)
    · rw [sbStepQ_of_lt h]
      exact h
    · rw [sbStepQ_of_not_lt h]
      exact ih

theorem one_le_sbWalkQ_loDen (q k : ℕ) : 1 ≤ (sbWalkQ q k).loDen := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [sbWalkQ_succ]
    rcases sbStepQ_den q (sbWalkQ q k) with h | h
    · rw [h.1]
      exact ih
    · rw [h.1]
      omega

/-- For odd q ≥ 3 the fraction below lies below log2 q. -/
theorem sbWalkQ_lo_lt (hodd : Odd q) (hq : 3 ≤ q) (k : ℕ) :
    2 ^ (sbWalkQ q k).loNum < q ^ (sbWalkQ q k).loDen := by
  induction k with
  | zero =>
    change 2 ^ 0 < q ^ 1
    rw [pow_zero, pow_one]
    omega
  | succ k ih =>
    have h1 := one_le_sbWalkQ_loDen q k
    rw [sbWalkQ_succ]
    by_cases h : q ^ ((sbWalkQ q k).loDen + (sbWalkQ q k).hiDen) <
        2 ^ ((sbWalkQ q k).loNum + (sbWalkQ q k).hiNum)
    · rw [sbStepQ_of_lt h]
      exact ih
    · rw [sbStepQ_of_not_lt h]
      push Not at h
      exact lt_of_le_of_ne h (two_pow_ne_q_pow hodd hq
        (a := (sbWalkQ q k).loDen + (sbWalkQ q k).hiDen) (by omega))

/-! ### The integers -/

/-- Before step p2Q(1) the walk passes the integers below log2 q. -/
theorem sbWalkQ_int (hq : 3 ≤ q) : ∀ k, k < p2Q q 1 → sbWalkQ q k = ⟨k, 1, 1, 0⟩ := by
  intro k
  induction k with
  | zero =>
    intro _
    rfl
  | succ k ih =>
    intro hk
    have h : ¬q ^ (1 + 0) < 2 ^ (k + 1) := by
      rw [Nat.add_zero, q_pow_lt_two_pow_iff hq]
      omega
    rw [sbWalkQ_succ, ih (by omega)]
    exact sbStepQ_of_not_lt (s := ⟨k, 1, 1, 0⟩) h

/-- After p2Q(1) steps the walk lies between the two integers around log2 q. -/
theorem sbWalkQ_int_end (hq : 3 ≤ q) :
    sbWalkQ q (p2Q q 1) = ⟨p2Q q 1 - 1, 1, p2Q q 1, 1⟩ := by
  have hp := one_le_p2Q q 1
  obtain ⟨m, hm⟩ : ∃ m, p2Q q 1 = m + 1 := ⟨p2Q q 1 - 1, by omega⟩
  have h : q ^ (1 + 0) < 2 ^ (m + 1) := by
    rw [Nat.add_zero, q_pow_lt_two_pow_iff hq]
    omega
  have hw := sbWalkQ_int hq m (by omega)
  rw [hm, Nat.add_sub_cancel, sbWalkQ_succ, hw]
  exact sbStepQ_of_lt (s := ⟨m, 1, 1, 0⟩) h

/-! ### The record Orders -/

/-- With a and b the last lower and upper record Orders below a + b, the Order a + b is
    an upper record Order when p2Q(a + b) + 1 = p2Q(a) + p2Q(b), and a lower one when
    p2Q(a + b) = p2Q(a) + p2Q(b). -/
theorem record_add_of_lastRecordsQ (hodd : Odd q) (hq : 3 ≤ q) {a b : ℕ}
    (h : LastRecordsQ q a b (a + b)) :
    (p2Q q (a + b) + 1 = p2Q q a + p2Q q b → UpperRecordQ q (a + b)) ∧
      (p2Q q (a + b) = p2Q q a + p2Q q b → LowerRecordQ q (a + b)) := by
  have ha1 := h.one_le_lower
  have hb1 := h.one_le_upper
  have hsome : LowerRecordQ q (a + b) ∨ UpperRecordQ q (a + b) := by
    by_contra hnone
    push Not at hnone
    have hle := le_add_of_lastRecordsQ hodd hq (lastRecordsQ_succ h hnone.1 hnone.2)
    omega
  have hlow : LowerRecordQ q (a + b) → p2Q q (a + b) = p2Q q a + p2Q q b := by
    intro hL
    have hadd := (lowerRecordQ_iff_add hq (a + b)).mp hL a ha1 (by omega)
    rw [Nat.add_sub_cancel_left] at hadd
    exact hadd
  have hupp : UpperRecordQ q (a + b) → p2Q q (a + b) + 1 = p2Q q a + p2Q q b := by
    intro hU
    have hadd := (upperRecordQ_iff_add hq (a + b)).mp hU b hb1 (by omega)
    rw [Nat.add_sub_cancel] at hadd
    omega
  refine ⟨?_, ?_⟩
  · intro he
    rcases hsome with hL | hU
    · have := hlow hL
      omega
    · exact hU
  · intro he
    rcases hsome with hL | hU
    · exact hL
    · have := hupp hU
      omega

/-- The walk holds (p2Q(a) - 1)/a below and p2Q(b)/b above, with a and b the last lower
    and upper record Orders below a + b. -/
structure SBRecordsQ (q : ℕ) (s : SBNode) : Prop where
  /-- The fraction below is (p2Q(a) - 1)/a. -/
  lo : s.loNum + 1 = p2Q q s.loDen
  /-- The fraction above is p2Q(b)/b. -/
  hi : s.hiNum = p2Q q s.hiDen
  /-- a and b are the last lower and upper record Orders below a + b. -/
  last : LastRecordsQ q s.loDen s.hiDen (s.loDen + s.hiDen)

/-- A step of the walk keeps `SBRecordsQ`. -/
theorem SBRecordsQ.step (hodd : Odd q) (hq : 3 ≤ q) {s : SBNode} (h : SBRecordsQ q s) :
    SBRecordsQ q (sbStepQ q s) := by
  have hle := p2Q_add_le hq s.loDen s.hiDen
  have hle2 := p2Q_add_le_succ hq s.loDen s.hiDen
  have hrec := record_add_of_lastRecordsQ hodd hq h.last
  have hlo := h.lo
  have hhi := h.hi
  by_cases hlt : q ^ (s.loDen + s.hiDen) < 2 ^ (s.loNum + s.hiNum)
  · have h1 := (q_pow_lt_two_pow_iff hq).mp hlt
    have hP : p2Q q (s.loDen + s.hiDen) + 1 = p2Q q s.loDen + p2Q q s.hiDen := by
      omega
    have hU := hrec.1 hP
    rw [sbStepQ_of_lt hlt]
    refine ⟨hlo, ?_, ?_⟩
    · change s.loNum + s.hiNum = p2Q q (s.loDen + s.hiDen)
      omega
    · exact lastRecordsQ_add hodd hq (lastRecordsQ_succ_upper hq h.last hU)
  · have h1 : ¬p2Q q (s.loDen + s.hiDen) ≤ s.loNum + s.hiNum :=
      fun hc => hlt ((q_pow_lt_two_pow_iff hq).mpr hc)
    have hP : p2Q q (s.loDen + s.hiDen) = p2Q q s.loDen + p2Q q s.hiDen := by
      omega
    have hL := hrec.2 hP
    rw [sbStepQ_of_not_lt hlt]
    refine ⟨?_, hhi, ?_⟩
    · change s.loNum + s.hiNum + 1 = p2Q q (s.loDen + s.hiDen)
      omega
    · exact lastRecordsQ_add hodd hq (lastRecordsQ_succ_lower hq h.last hL)

/-- From step p2Q(1) on the walk holds (p2Q(a) - 1)/a and p2Q(b)/b, with a and b the last
    lower and upper record Orders below a + b. -/
theorem sbWalkQ_records (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    SBRecordsQ q (sbWalkQ q (p2Q q 1 + j)) := by
  induction j with
  | zero =>
    have hp := one_le_p2Q q 1
    rw [Nat.add_zero, sbWalkQ_int_end hq]
    exact ⟨Nat.sub_add_cancel hp, rfl, lastRecordsQ_two q⟩
  | succ j ih =>
    rw [← Nat.add_assoc, sbWalkQ_succ]
    exact ih.step hodd hq

/-- From step p2Q(1) on the fraction above is p2Q(b)/b. -/
theorem sbWalkQ_hiNum (hodd : Odd q) (hq : 3 ≤ q) {k : ℕ} (hk : p2Q q 1 ≤ k) :
    (sbWalkQ q k).hiNum = p2Q q (sbWalkQ q k).hiDen := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact (sbWalkQ_records hodd hq j).hi

/-- From step p2Q(1) on the fraction below is (p2Q(a) - 1)/a. -/
theorem sbWalkQ_loNum (hodd : Odd q) (hq : 3 ≤ q) {k : ℕ} (hk : p2Q q 1 ≤ k) :
    (sbWalkQ q k).loNum + 1 = p2Q q (sbWalkQ q k).loDen := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact (sbWalkQ_records hodd hq j).lo

/-- The sum of the two denominators grows at every step. -/
theorem add_two_le_sbWalkQ_den (hodd : Odd q) (hq : 3 ≤ q) (j : ℕ) :
    j + 2 ≤ (sbWalkQ q (p2Q q 1 + j)).loDen + (sbWalkQ q (p2Q q 1 + j)).hiDen := by
  induction j with
  | zero =>
    change 0 + 2 ≤ (sbWalkQ q (p2Q q 1)).loDen + (sbWalkQ q (p2Q q 1)).hiDen
    rw [sbWalkQ_int_end hq]
    exact le_rfl
  | succ j ih =>
    have hlast := (sbWalkQ_records hodd hq j).last
    have ha := hlast.one_le_lower
    have hb := hlast.one_le_upper
    rw [← Nat.add_assoc, sbWalkQ_succ]
    rcases sbStepQ_den q (sbWalkQ q (p2Q q 1 + j)) with h | h
    · rw [h.1, h.2]
      omega
    · rw [h.1, h.2]
      omega

/-- Every upper record Order below the sum of the two denominators has been the
    denominator of the fraction above. -/
theorem exists_sbWalkQ_hiDen (hodd : Odd q) (hq : 3 ≤ q) : ∀ (j n : ℕ), 1 ≤ n →
    n < (sbWalkQ q (p2Q q 1 + j)).loDen + (sbWalkQ q (p2Q q 1 + j)).hiDen →
    UpperRecordQ q n → ∃ i, i ≤ j ∧ (sbWalkQ q (p2Q q 1 + i)).hiDen = n := by
  intro j
  induction j with
  | zero =>
    intro n hn1 hn _
    rw [Nat.add_zero, sbWalkQ_int_end hq] at hn
    refine ⟨0, le_rfl, ?_⟩
    rw [Nat.add_zero, sbWalkQ_int_end hq]
    change 1 = n
    change n < 1 + 1 at hn
    omega
  | succ j ih =>
    intro n hn1 hn hU
    have hlast := (sbWalkQ_records hodd hq (j + 1)).last
    rcases Nat.lt_or_ge n
      ((sbWalkQ q (p2Q q 1 + j)).loDen + (sbWalkQ q (p2Q q 1 + j)).hiDen) with hlt | hge
    · obtain ⟨i, hi, hin⟩ := ih n hn1 hlt hU
      exact ⟨i, by omega, hin⟩
    · have hno := hlast.no_upper n
      have hb := (sbWalkQ_records hodd hq j).last.upper_lt
      rw [← Nat.add_assoc, sbWalkQ_succ] at hn hno
      rcases sbStepQ_den q (sbWalkQ q (p2Q q 1 + j)) with h | h
      · rw [h.1, h.2] at hn hno
        refine ⟨j + 1, le_rfl, ?_⟩
        rw [← Nat.add_assoc, sbWalkQ_succ, h.2]
        by_contra hne
        exact hno (by omega) hn hU
      · rw [h.1, h.2] at hn hno
        exact absurd hU (hno (by omega) hn)

/-- Every lower record Order below the sum of the two denominators has been the
    denominator of the fraction below. -/
theorem exists_sbWalkQ_loDen (hodd : Odd q) (hq : 3 ≤ q) : ∀ (j n : ℕ), 1 ≤ n →
    n < (sbWalkQ q (p2Q q 1 + j)).loDen + (sbWalkQ q (p2Q q 1 + j)).hiDen →
    LowerRecordQ q n → ∃ i, i ≤ j ∧ (sbWalkQ q (p2Q q 1 + i)).loDen = n := by
  intro j
  induction j with
  | zero =>
    intro n hn1 hn _
    rw [Nat.add_zero, sbWalkQ_int_end hq] at hn
    refine ⟨0, le_rfl, ?_⟩
    rw [Nat.add_zero, sbWalkQ_int_end hq]
    change 1 = n
    change n < 1 + 1 at hn
    omega
  | succ j ih =>
    intro n hn1 hn hL
    have hlast := (sbWalkQ_records hodd hq (j + 1)).last
    rcases Nat.lt_or_ge n
      ((sbWalkQ q (p2Q q 1 + j)).loDen + (sbWalkQ q (p2Q q 1 + j)).hiDen) with hlt | hge
    · obtain ⟨i, hi, hin⟩ := ih n hn1 hlt hL
      exact ⟨i, by omega, hin⟩
    · have hno := hlast.no_lower n
      have ha := (sbWalkQ_records hodd hq j).last.lower_lt
      rw [← Nat.add_assoc, sbWalkQ_succ] at hn hno
      rcases sbStepQ_den q (sbWalkQ q (p2Q q 1 + j)) with h | h
      · rw [h.1, h.2] at hn hno
        exact absurd hL (hno (by omega) hn)
      · rw [h.1, h.2] at hn hno
        refine ⟨j + 1, le_rfl, ?_⟩
        rw [← Nat.add_assoc, sbWalkQ_succ, h.1]
        by_contra hne
        exact hno (by omega) hn hL

/-- The upper record Orders n ≥ 1 are exactly the denominators of the fractions above
    log2 q on the Stern–Brocot walk towards it. -/
theorem upperRecordQ_iff_sbWalkQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    UpperRecordQ q n ↔ ∃ k, (sbWalkQ q k).hiDen = n := by
  constructor
  · intro hU
    have hden := add_two_le_sbWalkQ_den hodd hq n
    obtain ⟨i, _, hi⟩ := exists_sbWalkQ_hiDen hodd hq n n hn (by omega) hU
    exact ⟨p2Q q 1 + i, hi⟩
  · rintro ⟨k, hk⟩
    rcases Nat.lt_or_ge k (p2Q q 1) with hlt | hge
    · rw [sbWalkQ_int hq k hlt] at hk
      change 0 = n at hk
      omega
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
      rw [← hk]
      exact (sbWalkQ_records hodd hq j).last.upper

/-- The lower record Orders n ≥ 1 are exactly the denominators of the fractions below
    log2 q on the Stern–Brocot walk towards it. -/
theorem lowerRecordQ_iff_sbWalkQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    LowerRecordQ q n ↔ ∃ k, (sbWalkQ q k).loDen = n := by
  constructor
  · intro hL
    have hden := add_two_le_sbWalkQ_den hodd hq n
    obtain ⟨i, _, hi⟩ := exists_sbWalkQ_loDen hodd hq n n hn (by omega) hL
    exact ⟨p2Q q 1 + i, hi⟩
  · rintro ⟨k, hk⟩
    rcases Nat.lt_or_ge k (p2Q q 1) with hlt | hge
    · rw [sbWalkQ_int hq k hlt] at hk
      change 1 = n at hk
      rw [← hk]
      intro a ha1 ha
      omega
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
      rw [← hk]
      exact (sbWalkQ_records hodd hq j).last.lower

end AcceleratedCollatz
