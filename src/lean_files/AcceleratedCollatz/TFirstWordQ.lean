-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSmoothNextQ

/-!
  The first word of each Order in the q-family (paper sec:chain has q = 3).
  `firstWordQ q n` takes, after each odd step, every halving that keeps the level above
  1. For odd q ≥ 3 it is admissible of Order n (`firstWordQ_mem`), and for q ≥ 3 no
  admissible word of Order n is below it (`firstWordQ_le`). After a of its odd steps and
  the halvings that follow them it is p2Q(a) - 1 letters long (`take_firstWordQ`) and its
  level is twice the block factor of a (`seqProductQ_take_firstWordQ`); every other level
  before its final halving is at least 2 (`two_le_seqProductQ_take_firstWordQ`). So, from
  the end of its first part on, it is lower than at every earlier point exactly after
  p2Q(a) - 1 letters for the lower record Orders a ≤ n (`firstWordQ_low_iff`). Between
  two neighbouring lower record Orders a < b it reads the first word of Order b - a
  (`firstBodyQ_eq_append_firstWordQ`), and after the last one up to n the first word of
  the rest (`firstWordQ_eq_append_firstWordQ`). Together (`firstWordQ_blocks`): the first
  word of Order n ≥ 1 is its first part, then first words whose Orders are the gaps of
  the lower record Orders up to n and the rest (`FirstBlocksQ`), then a halving exactly
  when n is a lower record Order.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- p2Q is strictly increasing. -/
theorem p2Q_lt_succ (hq : 3 ≤ q) (k : ℕ) : p2Q q k < p2Q q (k + 1) := by
  have h1 := p2Q_spec_lower hq k
  have h2 := p2Q_spec hq (k + 1)
  have hp := one_le_p2Q q k
  have h3 : 2 ^ (p2Q q k - 1 + 1) ≤ q ^ (k + 1) := by
    rw [pow_succ, pow_succ]
    exact Nat.mul_le_mul h1 (by omega)
  have h4 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h3 h2)
  omega

theorem p2Q_lt_of_lt (hq : 3 ≤ q) {a b : ℕ} (h : a < b) : p2Q q a < p2Q q b :=
  lt_of_lt_of_le (p2Q_lt_succ hq a) (p2Q_mono hq h)

theorem two_le_p2Q (hq : 3 ≤ q) {a : ℕ} (ha : 1 ≤ a) : 2 ≤ p2Q q a := by
  have h := p2Q_lt_of_lt hq (Nat.lt_of_lt_of_le Nat.zero_lt_one ha)
  rw [p2Q_zero] at h
  exact h

/-- The first word of Order n without its final halving: after each odd step every
    halving that keeps the level above 1. -/
def firstBodyQ (q : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => firstBodyQ q n ++ true :: List.replicate (p2Q q (n + 1) - p2Q q n - 1) false

/-- The first word of Order n in the q-family. -/
def firstWordQ (q n : ℕ) : List Bool := firstBodyQ q n ++ [false]

theorem firstBodyQ_succ (q n : ℕ) : firstBodyQ q (n + 1) =
    firstBodyQ q n ++ true :: List.replicate (p2Q q (n + 1) - p2Q q n - 1) false :=
  rfl

/-- `firstBodyQ q n` has p2Q(n) - 1 letters. -/
theorem length_firstBodyQ (hq : 3 ≤ q) (n : ℕ) : (firstBodyQ q n).length + 1 = p2Q q n := by
  induction n with
  | zero =>
    rw [p2Q_zero]
    rfl
  | succ n ih =>
    have h := p2Q_lt_succ hq n
    rw [firstBodyQ_succ, List.length_append, List.length_cons, List.length_replicate]
    omega

theorem length_firstWordQ (hq : 3 ≤ q) (n : ℕ) : (firstWordQ q n).length = p2Q q n := by
  rw [firstWordQ, List.length_append, List.length_singleton, length_firstBodyQ hq]

theorem order_firstBodyQ (q n : ℕ) : order (firstBodyQ q n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firstBodyQ_succ, order_append, order_cons, order_replicate_false, ih]
    simp

theorem order_firstWordQ (q n : ℕ) : order (firstWordQ q n) = n := by
  have h : order [false] = 0 := rfl
  rw [firstWordQ, order_append, order_firstBodyQ, h, Nat.add_zero]

/-- `firstBodyQ q a` begins `firstBodyQ q n` for a ≤ n. -/
theorem firstBodyQ_prefix {a n : ℕ} (h : a ≤ n) : firstBodyQ q a <+: firstBodyQ q n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih =>
    rw [firstBodyQ_succ]
    exact ih.trans (List.prefix_append _ _)

/-- After a of its odd steps and the halvings that follow them, the first word of
    Order n ≥ a is p2Q(a) - 1 letters long. -/
theorem take_firstWordQ (hq : 3 ≤ q) {n a m : ℕ} (ha : a ≤ n) (hm : m + 1 = p2Q q a) :
    (firstWordQ q n).take m = firstBodyQ q a := by
  have hlen : (firstBodyQ q a).length = m := by
    have h := length_firstBodyQ hq a
    omega
  have hpre : firstBodyQ q a <+: firstWordQ q n :=
    (firstBodyQ_prefix ha).trans (List.prefix_append _ _)
  rw [← hlen]
  exact (List.prefix_iff_eq_take.mp hpre).symm

/-- A nonempty prefix of `firstBodyQ q n` ends in a part of the halvings after an odd
    step. -/
theorem take_firstBodyQ (hq : 3 ≤ q) {n : ℕ} : ∀ {j : ℕ}, 1 ≤ j →
    j ≤ (firstBodyQ q n).length →
    ∃ k r, k < n ∧ p2Q q k + r < p2Q q (k + 1) ∧ j = p2Q q k + r ∧
      (firstBodyQ q n).take j = firstBodyQ q k ++ true :: List.replicate r false := by
  induction n with
  | zero =>
    intro j hj1 hj
    simp only [firstBodyQ, List.length_nil] at hj
    omega
  | succ n ih =>
    intro j hj1 hj
    have hlen := length_firstBodyQ hq n
    have hlt := p2Q_lt_succ hq n
    rw [firstBodyQ_succ] at hj ⊢
    rw [List.length_append, List.length_cons, List.length_replicate] at hj
    rcases Nat.lt_or_ge (firstBodyQ q n).length j with hgt | hle
    · refine ⟨n, j - (firstBodyQ q n).length - 1, by omega, by omega, by omega, ?_⟩
      have hj' : j - (firstBodyQ q n).length = (j - (firstBodyQ q n).length - 1) + 1 := by
        omega
      rw [List.take_append, List.take_of_length_le (le_of_lt hgt), hj', List.take_succ_cons,
        List.take_replicate]
      congr 3
      omega
    · obtain ⟨k, r, hk, hr, hjr, htake⟩ := ih hj1 hle
      refine ⟨k, r, by omega, hr, hjr, ?_⟩
      rw [List.take_append_of_le_length hle, htake]

/-- Level and length of a prefix of the first word, as integers. -/
theorem seqProductQ_firstBodyQ_append (hq : 3 ≤ q) (k r : ℕ) :
    seqProductQ q (firstBodyQ q k ++ true :: List.replicate r false) * 2 ^ (p2Q q k + r) =
      (q : ℚ) ^ (k + 1) := by
  have h := seqProductQ_mul_pow q (firstBodyQ q k ++ true :: List.replicate r false)
  have hlen := length_firstBodyQ hq k
  have hl : (firstBodyQ q k ++ true :: List.replicate r false).length = p2Q q k + r := by
    rw [List.length_append, List.length_cons, List.length_replicate]
    omega
  have ho : order (firstBodyQ q k ++ true :: List.replicate r false) = k + 1 := by
    rw [order_append, order_cons, order_replicate_false, order_firstBodyQ]
    simp
  rw [hl, ho] at h
  exact h

/-- For odd q, the first word of Order k without its final halving, then an odd step and r
    halvings, has level above 1 when p2Q(k) + r < p2Q(k + 1). -/
theorem one_lt_seqProductQ_firstBodyQ_append (hodd : Odd q) (hq : 3 ≤ q) {k r : ℕ}
    (hr : p2Q q k + r < p2Q q (k + 1)) :
    1 < seqProductQ q (firstBodyQ q k ++ true :: List.replicate r false) := by
  have h := seqProductQ_firstBodyQ_append hq k r
  have hpow : (2 : ℚ) ^ (p2Q q k + r) < (q : ℚ) ^ (k + 1) := by
    have h1 := (two_pow_lt_q_pow_iff hodd hq (a := k + 1) (by omega)).mpr hr
    exact_mod_cast h1
  have hpos : (0 : ℚ) < 2 ^ (p2Q q k + r) := by positivity
  by_contra hle
  push Not at hle
  have := mul_le_mul_of_nonneg_right hle hpos.le
  linarith

/-- The first word of Order k without its final halving, then an odd step and r halvings,
    has level at least 2 when p2Q(k) + r + 1 < p2Q(k + 1). -/
theorem two_le_seqProductQ_firstBodyQ_append (hq : 3 ≤ q) {k r : ℕ}
    (hr : p2Q q k + r + 1 < p2Q q (k + 1)) :
    2 ≤ seqProductQ q (firstBodyQ q k ++ true :: List.replicate r false) := by
  have h := seqProductQ_firstBodyQ_append hq k r
  have hpow : (2 : ℚ) * 2 ^ (p2Q q k + r) ≤ (q : ℚ) ^ (k + 1) := by
    have h1 : 2 ^ (p2Q q k + r + 1) ≤ 2 ^ (p2Q q (k + 1) - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := p2Q_spec_lower hq (k + 1)
    have h3 : 2 * 2 ^ (p2Q q k + r) ≤ q ^ (k + 1) := by
      rw [pow_succ, mul_comm] at h1
      exact h1.trans h2
    exact_mod_cast h3
  have hpos : (0 : ℚ) < 2 ^ (p2Q q k + r) := by positivity
  by_contra hlt
  push Not at hlt
  have := mul_lt_mul_of_pos_right hlt hpos
  linarith

theorem blockFactorQ_lt_one (hq : 3 ≤ q) (n : ℕ) : blockFactorQ q n < 1 := by
  unfold blockFactorQ
  rw [div_lt_iff₀ (by positivity), one_mul]
  exact_mod_cast p2Q_spec hq n

/-- After n odd steps and the halvings that follow them the level is twice the block
    factor of n. -/
theorem seqProductQ_firstBodyQ (hq : 3 ≤ q) (n : ℕ) :
    seqProductQ q (firstBodyQ q n) = 2 * blockFactorQ q n := by
  have h := seqProductQ_mul_pow q (firstBodyQ q n)
  rw [order_firstBodyQ] at h
  unfold blockFactorQ
  rw [← length_firstBodyQ hq n, pow_succ, ← h]
  have hpos : (0 : ℚ) < 2 ^ (firstBodyQ q n).length := by positivity
  field_simp

theorem seqProductQ_firstWordQ (hq : 3 ≤ q) (n : ℕ) :
    seqProductQ q (firstWordQ q n) = blockFactorQ q n := by
  have hf : seqProductQ q [false] = 1 / 2 := by
    norm_num [seqProductQ, factorQ]
  rw [firstWordQ, seqProductQ_append, seqProductQ_firstBodyQ hq, hf]
  ring

/-- For odd q ≥ 3 the first word of Order n is admissible. -/
theorem firstWordQ_admissibleQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    AdmissibleQ q (firstWordQ q n) := by
  constructor
  · intro m hm1 hm
    rw [length_firstWordQ hq] at hm
    have hlen := length_firstBodyQ hq n
    have hle : m ≤ (firstBodyQ q n).length := by omega
    rw [firstWordQ, List.take_append_of_le_length hle]
    obtain ⟨k, r, _, hr, _, htake⟩ := take_firstBodyQ hq hm1 hle
    rw [htake]
    exact one_lt_seqProductQ_firstBodyQ_append hodd hq hr
  · rw [seqProductQ_firstWordQ hq]
    exact blockFactorQ_lt_one hq n

/-- For odd q ≥ 3 the first word of Order n is an admissible word of Order n. -/
theorem firstWordQ_mem (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) : firstWordQ q n ∈ admSetQ q n :=
  (mem_admSetQ (by omega) _ _).mpr ⟨firstWordQ_admissibleQ hodd hq n, order_firstWordQ q n⟩

/-! ### The first word is the least one -/

/-- Two words of one length, the first below the second: they part at a letter that is
    0 in the first and 1 in the second. -/
theorem exists_split_of_lt : ∀ {s t : List Bool}, s < t → s.length = t.length →
    ∃ p s' t', s = p ++ false :: s' ∧ t = p ++ true :: t' := by
  intro s
  induction s with
  | nil =>
    intro t hlt hlen
    have ht : t = [] := List.length_eq_zero_iff.mp hlen.symm
    rw [ht] at hlt
    exact absurd hlt (lt_irrefl _)
  | cons a s ih =>
    intro t hlt hlen
    cases t with
    | nil => simp at hlen
    | cons b t =>
      rw [List.cons_lt_cons_iff] at hlt
      rcases hlt with hab | ⟨hab, hlt'⟩
      · obtain ⟨ha, hb⟩ := Bool.lt_iff.mp hab
        rw [ha, hb]
        exact ⟨[], s, t, rfl, rfl⟩
      · have hlen' : s.length = t.length := by simpa using hlen
        obtain ⟨p, s', t', hs, ht⟩ := ih hlt' hlen'
        rw [hab, hs, ht]
        exact ⟨b :: p, s', t', rfl, rfl⟩

/-- An odd step of `firstBodyQ q n` comes after `firstBodyQ q k` for some k < n. -/
theorem firstBodyQ_eq_append_true : ∀ (n : ℕ) {p c : List Bool},
    firstBodyQ q n = p ++ true :: c → ∃ k, k < n ∧ p = firstBodyQ q k := by
  intro n
  induction n with
  | zero =>
    intro p c h
    simp [firstBodyQ] at h
  | succ n ih =>
    intro p c h
    rw [firstBodyQ_succ, List.append_eq_append_iff] at h
    rcases h with ⟨a', hp, ha⟩ | ⟨c', hb, hc⟩
    · cases a' with
      | nil =>
        rw [List.append_nil] at hp
        exact ⟨n, by omega, hp⟩
      | cons x a'' =>
        rw [List.cons_append, List.cons.injEq] at ha
        have hmem : true ∈ List.replicate (p2Q q (n + 1) - p2Q q n - 1) false := by
          rw [ha.2]
          simp
        exact absurd (List.eq_of_mem_replicate hmem) (by decide)
    · cases c' with
      | nil =>
        rw [List.append_nil] at hb
        exact ⟨n, by omega, hb.symm⟩
      | cons x c'' =>
        rw [List.cons_append, List.cons.injEq] at hc
        rw [← hc.1] at hb
        obtain ⟨k, hk, hpk⟩ := ih hb
        exact ⟨k, by omega, hpk⟩

/-- An odd step of the first word of Order n comes after `firstBodyQ q k` for some
    k < n. -/
theorem firstWordQ_eq_append_true {n : ℕ} {p t : List Bool}
    (h : firstWordQ q n = p ++ true :: t) : ∃ k, k < n ∧ p = firstBodyQ q k := by
  rw [firstWordQ, List.append_eq_append_iff] at h
  rcases h with ⟨a', _, ha⟩ | ⟨c', hb, hc⟩
  · cases a' with
    | nil => simp at ha
    | cons x a'' => simp at ha
  · cases c' with
    | nil => simp at hc
    | cons x c'' =>
      rw [List.cons_append, List.cons.injEq] at hc
      rw [← hc.1] at hb
      exact firstBodyQ_eq_append_true n hb

/-- No admissible word of Order n is below the first word. -/
theorem not_lt_firstWordQ (hq : 3 ≤ q) {n : ℕ} {s : List Bool} (hs : s ∈ admSetQ q n) :
    ¬s < firstWordQ q n := by
  intro hlt
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hlen : s.length = p2Q q n := by
    rw [admissibleQ_length (by omega) hA, hord]
  obtain ⟨p, s', t', hs', ht'⟩ :=
    exists_split_of_lt hlt (by rw [hlen, length_firstWordQ hq])
  obtain ⟨k, hk, hp⟩ := firstWordQ_eq_append_true ht'
  have hsk : s = firstWordQ q k ++ s' := by
    rw [hs', hp, firstWordQ, List.append_assoc]
    rfl
  have htake : s.take (p2Q q k) = firstWordQ q k := by
    rw [hsk]
    exact List.take_left' (length_firstWordQ hq k)
  have hkl : p2Q q k < s.length := by
    rw [hlen]
    exact p2Q_lt_of_lt hq hk
  have hgt := hA.prefix_gt (p2Q q k) (one_le_p2Q q k) hkl
  rw [htake, seqProductQ_firstWordQ hq] at hgt
  exact absurd hgt (not_lt.mpr (le_of_lt (blockFactorQ_lt_one hq k)))

/-- The first word of Order n is at most every admissible word of Order n. -/
theorem firstWordQ_le (hq : 3 ≤ q) {n : ℕ} {s : List Bool} (hs : s ∈ admSetQ q n) :
    firstWordQ q n ≤ s :=
  not_lt.mp (not_lt_firstWordQ hq hs)

/-! ### Its levels -/

/-- After a ≤ n odd steps and the halvings that follow them, the level of the first word
    of Order n is twice the block factor of a. -/
theorem seqProductQ_take_firstWordQ (hq : 3 ≤ q) {n a m : ℕ} (ha : a ≤ n)
    (hm : m + 1 = p2Q q a) :
    seqProductQ q ((firstWordQ q n).take m) = 2 * blockFactorQ q a := by
  rw [take_firstWordQ hq ha hm, seqProductQ_firstBodyQ hq]

/-- Every other level of the first word before its final halving is at least 2. -/
theorem two_le_seqProductQ_take_firstWordQ (hq : 3 ≤ q) {n m : ℕ} (hm1 : 1 ≤ m)
    (hm : m < p2Q q n) (hne : ∀ a, 1 ≤ a → a ≤ n → m + 1 ≠ p2Q q a) :
    2 ≤ seqProductQ q ((firstWordQ q n).take m) := by
  have hlenB := length_firstBodyQ hq n
  have hle : m ≤ (firstBodyQ q n).length := by omega
  obtain ⟨k, r, hk, hr, hmr, htake⟩ := take_firstBodyQ hq hm1 hle
  rw [firstWordQ, List.take_append_of_le_length hle, htake]
  apply two_le_seqProductQ_firstBodyQ_append hq
  have h := hne (k + 1) (by omega) (by omega)
  omega

/-- From the end of its first part on and before its final halving, the first word of
    Order n is lower than at every earlier such point exactly after p2Q(a) - 1 letters
    for the lower record Orders a ≤ n. -/
theorem firstWordQ_low_iff (hq : 3 ≤ q) {n m : ℕ} (hm1 : p2Q q 1 ≤ m + 1)
    (hm : m < p2Q q n) :
    (∀ j, p2Q q 1 ≤ j + 1 → j < m →
        seqProductQ q ((firstWordQ q n).take m) < seqProductQ q ((firstWordQ q n).take j)) ↔
      ∃ a, 1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a ∧ m + 1 = p2Q q a := by
  have hlenB := length_firstBodyQ hq n
  have hp1 := two_le_p2Q hq (a := 1) le_rfl
  have hprefix : ∀ {j : ℕ}, 1 ≤ j → j + 1 ≤ p2Q q n →
      ∃ k r, k < n ∧ p2Q q k + r < p2Q q (k + 1) ∧ j = p2Q q k + r ∧
        (firstWordQ q n).take j = firstBodyQ q k ++ true :: List.replicate r false := by
    intro j hj1 hj
    have hle : j ≤ (firstBodyQ q n).length := by omega
    obtain ⟨k, r, hk, hr, hjr, htake⟩ := take_firstBodyQ hq hj1 hle
    refine ⟨k, r, hk, hr, hjr, ?_⟩
    rw [firstWordQ, List.take_append_of_le_length hle, htake]
  constructor
  · intro hlow
    obtain ⟨k, r, hk, hr, hmr, htake⟩ := hprefix (j := m) (by omega) (by omega)
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hr) with hfull | hpart
    · refine ⟨k + 1, by omega, by omega, ?_, by omega⟩
      rw [lowerRecordQ_iff_blockFactorQ hq]
      intro b hb1 hbk
      have hpb := p2Q_mono hq hb1
      have hpbk := p2Q_lt_of_lt hq hbk
      have hj := hlow (p2Q q b - 1) (by omega) (by omega)
      rw [take_firstWordQ hq (a := k + 1) (by omega) (by omega),
        take_firstWordQ hq (a := b) (by omega) (by omega),
        seqProductQ_firstBodyQ hq, seqProductQ_firstBodyQ hq] at hj
      linarith
    · exfalso
      rcases Nat.eq_zero_or_pos k with hz | hk1
      · have h01 : p2Q q (0 + 1) = p2Q q 1 := rfl
        rw [hz, p2Q_zero] at hpart hmr
        omega
      · have hpk : p2Q q 1 ≤ p2Q q k := p2Q_mono hq hk1
        have hj := hlow (p2Q q 1 - 1) (by omega) (by omega)
        rw [htake, take_firstWordQ hq (a := 1) (by omega) (by omega),
          seqProductQ_firstBodyQ hq] at hj
        have h2 := two_le_seqProductQ_firstBodyQ_append hq hpart
        have h1 := blockFactorQ_lt_one hq 1
        linarith
  · rintro ⟨a, ha1, han, hR, hma⟩ j hj1 hjm
    have hpan := p2Q_mono hq han
    rw [take_firstWordQ hq han hma, seqProductQ_firstBodyQ hq]
    obtain ⟨k, r, hk, hr, hjr, htake⟩ := hprefix (j := j) (by omega) (by omega)
    rw [htake]
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hr) with hfull | hpart
    · have hka : k + 1 < a := by
        by_contra hge
        push Not at hge
        have := p2Q_mono hq hge
        omega
      have hbody :
          firstBodyQ q k ++ true :: List.replicate r false = firstBodyQ q (k + 1) := by
        rw [← htake]
        exact take_firstWordQ hq (by omega) (by omega)
      rw [hbody, seqProductQ_firstBodyQ hq]
      have := (lowerRecordQ_iff_blockFactorQ hq a).mp hR (k + 1) (by omega) hka
      linarith
    · have h2 := two_le_seqProductQ_firstBodyQ_append hq hpart
      have h1 := blockFactorQ_lt_one hq a
      linarith

/-! ### Its blocks -/

/-- `firstBodyQ q (a + m)` is `firstBodyQ q a` followed by `firstBodyQ q m`, when
    p2Q(a + i) + 1 = p2Q(a) + p2Q(i) for 1 ≤ i ≤ m. -/
theorem firstBodyQ_add (hq : 3 ≤ q) (a : ℕ) : ∀ m,
    (∀ i, 1 ≤ i → i ≤ m → p2Q q (a + i) + 1 = p2Q q a + p2Q q i) →
    firstBodyQ q (a + m) = firstBodyQ q a ++ firstBodyQ q m := by
  intro m
  induction m with
  | zero =>
    intro _
    exact (List.append_nil _).symm
  | succ m ih =>
    intro h
    have hm := ih (fun i hi1 him => h i hi1 (by omega))
    have h1 := h (m + 1) (by omega) le_rfl
    have h0 : p2Q q (a + m) + 1 = p2Q q a + p2Q q m := by
      rcases Nat.eq_zero_or_pos m with hz | hpos
      · rw [hz, p2Q_zero]
        rfl
      · exact h m hpos (by omega)
    have hlt := p2Q_lt_succ hq m
    rw [← Nat.add_assoc] at h1 ⊢
    have hc : p2Q q (a + m + 1) - p2Q q (a + m) - 1 = p2Q q (m + 1) - p2Q q m - 1 := by
      omega
    rw [firstBodyQ_succ, firstBodyQ_succ, hm, hc, List.append_assoc]

/-- Between two neighbouring lower record Orders a < b the first word reads the first
    word of Order b - a. -/
theorem firstBodyQ_eq_append_firstWordQ (hq : 3 ≤ q) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hRa : LowerRecordQ q a) (hRb : LowerRecordQ q b)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecordQ q x) :
    firstBodyQ q b = firstBodyQ q a ++ firstWordQ q (b - a) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
  have hbody := firstBodyQ_add hq a k (fun i hi1 hik =>
    p2Q_add_of_lowerRecordQ hq hRa hnone hi1 (by omega))
  have hadd := (lowerRecordQ_iff_add hq (a + (k + 1))).mp hRb a ha hab
  have h0 : p2Q q (a + k) + 1 = p2Q q a + p2Q q k := by
    rcases Nat.eq_zero_or_pos k with hz | hpos
    · rw [hz, p2Q_zero]
      rfl
    · exact p2Q_add_of_lowerRecordQ hq hRa hnone hpos (by omega)
  have hlt := p2Q_lt_succ hq k
  rw [Nat.add_sub_cancel_left] at hadd ⊢
  rw [← Nat.add_assoc] at hadd ⊢
  have hc : p2Q q (a + k + 1) - p2Q q (a + k) - 1 = (p2Q q (k + 1) - p2Q q k - 1) + 1 := by
    omega
  rw [firstBodyQ_succ, hbody, firstWordQ, firstBodyQ_succ, hc, List.replicate_succ']
  simp only [List.append_assoc, List.cons_append]

/-- After a lower record Order a with no lower record Order from a + 1 to n, the first
    word of Order n reads the first word of Order n - a. -/
theorem firstWordQ_eq_append_firstWordQ (hq : 3 ≤ q) {a n : ℕ} (han : a < n)
    (hRa : LowerRecordQ q a) (hnone : ∀ x, a < x → x ≤ n → ¬LowerRecordQ q x) :
    firstWordQ q n = firstBodyQ q a ++ firstWordQ q (n - a) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = a + m := ⟨n - a, by omega⟩
  have hnone' : ∀ x, a < x → x < a + m + 1 → ¬LowerRecordQ q x :=
    fun x hax hxb => hnone x hax (by omega)
  have hbody := firstBodyQ_add hq a m (fun i hi1 him =>
    p2Q_add_of_lowerRecordQ hq hRa hnone' hi1 (by omega))
  rw [Nat.add_sub_cancel_left, firstWordQ, hbody, firstWordQ, List.append_assoc]

/-- Below every m ≥ 2 there is a last lower record Order. -/
theorem exists_last_lowerRecordQ (q : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    ∃ a, 1 ≤ a ∧ a < m ∧ LowerRecordQ q a ∧ ∀ x, a < x → x < m → ¬LowerRecordQ q x := by
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨1, le_rfl, by omega, ?_, ?_⟩
    · intro a ha1 ha
      omega
    · intro x hx1 hx2 _
      omega
  | succ m hm ih =>
    obtain ⟨a, ha1, ham, hRa, hnone⟩ := ih
    by_cases hR : LowerRecordQ q m
    · refine ⟨m, by omega, by omega, hR, ?_⟩
      intro x hx1 hx2 _
      omega
    · refine ⟨a, ha1, by omega, hRa, ?_⟩
      intro x hax hxm
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hxm) with heq | hlt
      · rw [heq]
        exact hR
      · exact hnone x hax hlt

/-- The blocks of a first word after its first part: every block is the first word of
    its Order, of Order at least 1; with the 1 of the first part the Orders add up to m;
    the Order read before each block is a lower record Order below m, and every lower
    record Order from 1 to m - 1 occurs there. -/
structure FirstBlocksQ (q : ℕ) (bs : List (List Bool)) (m : ℕ) : Prop where
  /-- Every block is the first word of its Order, of Order at least 1. -/
  first : ∀ b ∈ bs, 1 ≤ order b ∧ b = firstWordQ q (order b)
  /-- With the 1 of the first part the Orders add up to m. -/
  sum : 1 + (bs.map order).sum = m
  /-- The Orders read before the blocks are the lower record Orders from 1 to m - 1. -/
  cuts : ∀ a, (∃ i, i < bs.length ∧ a = 1 + ((bs.take i).map order).sum) ↔
    (1 ≤ a ∧ a < m ∧ LowerRecordQ q a)

theorem firstBlocksQ_nil (q : ℕ) : FirstBlocksQ q [] 1 where
  first := by
    intro b hb
    simp at hb
  sum := by
    simp
  cuts := by
    intro a
    constructor
    · rintro ⟨i, hi, _⟩
      simp at hi
    · rintro ⟨ha1, ha, _⟩
      omega

/-- One more block: after the last lower record Order a below m, the first word of
    Order m - a. -/
theorem FirstBlocksQ.snoc {bs : List (List Bool)} {a m : ℕ} (h : FirstBlocksQ q bs a)
    (ha1 : 1 ≤ a) (ham : a < m) (hRa : LowerRecordQ q a)
    (hnone : ∀ x, a < x → x < m → ¬LowerRecordQ q x) :
    FirstBlocksQ q (bs ++ [firstWordQ q (m - a)]) m where
  first := by
    intro b hb
    rcases List.mem_append.mp hb with hb' | hb'
    · exact h.first b hb'
    · rw [List.mem_singleton.mp hb', order_firstWordQ]
      exact ⟨by omega, rfl⟩
  sum := by
    have hs := h.sum
    rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      order_firstWordQ]
    omega
  cuts := by
    intro x
    rw [List.length_append, List.length_singleton]
    constructor
    · rintro ⟨i, hi, hx⟩
      rcases Nat.lt_or_ge i bs.length with hlt | hge
      · rw [List.take_append_of_le_length (le_of_lt hlt)] at hx
        obtain ⟨hx1, hxa, hRx⟩ := (h.cuts x).mp ⟨i, hlt, hx⟩
        exact ⟨hx1, by omega, hRx⟩
      · have hi' : i = bs.length := by omega
        rw [hi', List.take_left' rfl, h.sum] at hx
        rw [hx]
        exact ⟨ha1, ham, hRa⟩
    · rintro ⟨hx1, hxm, hRx⟩
      rcases Nat.lt_trichotomy x a with hlt | heq | hgt
      · obtain ⟨i, hi, hx⟩ := (h.cuts x).mpr ⟨hx1, hlt, hRx⟩
        refine ⟨i, by omega, ?_⟩
        rw [List.take_append_of_le_length (le_of_lt hi)]
        exact hx
      · refine ⟨bs.length, by omega, ?_⟩
        rw [List.take_left' rfl, h.sum]
        exact heq
      · exact absurd hRx (hnone x hgt hxm)

/-- Up to a lower record Order m ≥ 1 the first word is its first part followed by first
    words, cut at the lower record Orders below m. -/
theorem firstBodyQ_blocks (hq : 3 ≤ q) : ∀ m, 1 ≤ m → LowerRecordQ q m →
    ∃ bs : List (List Bool),
      firstBodyQ q m = firstBodyQ q 1 ++ bs.flatten ∧ FirstBlocksQ q bs m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm1 hRm
    rcases Nat.eq_or_lt_of_le hm1 with heq | hlt
    · refine ⟨[], ?_, ?_⟩
      · rw [← heq, List.flatten_nil, List.append_nil]
      · rw [← heq]
        exact firstBlocksQ_nil q
    · obtain ⟨a, ha1, ham, hRa, hnone⟩ := exists_last_lowerRecordQ q hlt
      obtain ⟨bs, hbody, hbs⟩ := ih a ham ha1 hRa
      refine ⟨bs ++ [firstWordQ q (m - a)], ?_, hbs.snoc ha1 ham hRa hnone⟩
      rw [firstBodyQ_eq_append_firstWordQ hq ha1 ham hRa hRm hnone, hbody,
        List.flatten_append, List.flatten_singleton, List.append_assoc]

/-- The first word of Order n ≥ 1 is its first part (the first odd step and its
    halvings), then first words cut at the lower record Orders below n
    (`FirstBlocksQ`), then a tail that is [0] exactly when n is a lower record Order. -/
theorem firstWordQ_blocks (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (bs : List (List Bool)) (t : List Bool),
      firstWordQ q n = firstBodyQ q 1 ++ (bs.flatten ++ t) ∧ FirstBlocksQ q bs n ∧
      (t = [false] ↔ LowerRecordQ q n) ∧ (t = [] ∨ t = [false]) := by
  by_cases hR : LowerRecordQ q n
  · obtain ⟨bs, hbody, hbs⟩ := firstBodyQ_blocks hq n hn hR
    refine ⟨bs, [false], ?_, hbs, ⟨fun _ => hR, fun _ => rfl⟩, Or.inr rfl⟩
    rw [firstWordQ, hbody, List.append_assoc]
  · have hn2 : 2 ≤ n := by
      rcases Nat.eq_or_lt_of_le hn with heq | hlt
      · exfalso
        apply hR
        rw [← heq]
        intro a ha1 ha
        omega
      · exact hlt
    obtain ⟨a, ha1, han, hRa, hnone⟩ := exists_last_lowerRecordQ q hn2
    obtain ⟨bs, hbody, hbs⟩ := firstBodyQ_blocks hq a ha1 hRa
    have hnone' : ∀ x, a < x → x ≤ n → ¬LowerRecordQ q x := by
      intro x hax hxn
      rcases Nat.eq_or_lt_of_le hxn with heq | hlt
      · rw [heq]
        exact hR
      · exact hnone x hax hlt
    have htail : ([] : List Bool) = [false] ↔ LowerRecordQ q n := by
      constructor
      · intro h
        exact absurd h (by simp)
      · intro h
        exact absurd h hR
    refine ⟨bs ++ [firstWordQ q (n - a)], [], ?_, hbs.snoc ha1 han hRa hnone, htail,
      Or.inl rfl⟩
    rw [firstWordQ_eq_append_firstWordQ hq han hRa hnone', hbody, List.flatten_append,
      List.flatten_singleton, List.append_nil, List.append_assoc]

end AcceleratedCollatz
