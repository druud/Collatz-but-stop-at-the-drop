-- SPDX-License-Identifier: MIT
import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The sweep map of the q-family (odd q ≥ 3), its start variant and its cut variant

Self-contained extract of the AcceleratedCollatz Lean 4 project; depends on
Mathlib only.

A word is a `List Bool` (`true` = factor q/2, `false` = factor 1/2); its level
after j steps is the product of the first j factors (`lvlQ`, exact rationals).
`AdmissibleQ q s`: the level stays > 1 on every proper nonempty prefix and ends
< 1. `order s` = the number of 1s; `admSetQ q n` = the admissible words of
Order n, of length `p2Q q n = Nat.log 2 (q ^ n) + 1`. The sweep `sweepQ q`
sorts the steps by their endpoint level, highest first. The start sweep
`startSweepQ q` sorts them by the level at which they start, lowest first. The
cut sweep `cutSweepQ q` is the start sweep of a word without its final step,
followed by a halving; for a word that ends in a halving, a rearrangement of its
steps (`cutSweepQ_perm`).

Sections:
1. Words and Order.
2. The q-family: levels, `AdmissibleQ`, `admSetQ`, `admissibleQ_length`.
3. The sweep and the inclusion `sweepQ_mem_admSetQ` (unconditional).
4. The integer sweep of Thomas and Williams, Sweeping up Zeta (2018), and the
   hypothesis `SweepBijective` (their Thm 6.3, for two letters).
5. Weights (`exists_weightsQ`), `sweepQ_eq_sweepZ`, and the bijection
   `sweepQ_bijOn` under `SweepBijective`.
6. Record Orders: `UpperRecordQ`, `LowerRecordQ`, and both by the block factor
   q^o / 2^p2Q(o) (`upperRecordQ_iff_blockFactorQ`, `lowerRecordQ_iff_blockFactorQ`).
7. The start sweep: its prefixes (`exists_startSweepQ_prefix_set`) and the word of
   n odd steps followed by halvings (`startSweepQ_upDownQ_not_mem`).
8. The start sweep as the sweep of a flipped word
   (`startSweepQ_eq_sweepQ_of_upperRecordQ`): it maps the admissible words of Order n
   to admissible words exactly at the upper record Orders
   (`mapsTo_startSweepQ_iff`, unconditional), and under `SweepBijective` it
   permutes them exactly there (`startSweepQ_bijOn_iff`).
9. The cut sweep: the inclusion `cutSweepQ_mem_admSetQ` (unconditional, every
   Order); at an Order that is no lower record it is not onto and not one-to-one
   (`not_surjOn_cutSweepQ`, `not_injOn_cutSweepQ`, unconditional); under
   `SweepBijective` it permutes the admissible words exactly at the lower record
   Orders (`cutSweepQ_bijOn_iff`).
10. The start sweep at every Order: it is the sweep of the reversed word
   (`startSweepQ_eq_sweepQ_reverse`), and under `SweepBijective` it is one-to-one on
   the admissible words of every Order (`startSweepQ_injOn`).
-/

namespace SweepQ

/-! ## 1. Words and Order -/

/-- Order: the number of 1s. -/
def order (s : List Bool) : ℕ := (s.filter id).length

/-- Order is additive under concatenation. -/
theorem order_append (a b : List Bool) : order (a ++ b) = order a + order b := by
  simp [order, List.filter_append]

theorem order_take_le (s : List Bool) (m : ℕ) : order (s.take m) ≤ order s := by
  have h := order_append (s.take m) (s.drop m)
  rw [List.take_append_drop] at h
  omega

theorem order_eq_count_true (s : List Bool) : order s = s.count true := by
  unfold order
  induction s with
  | nil => simp
  | cons b t ih =>
    cases b
    · simp [ih]
    · simp [ih]

/-- All words of length k. -/
def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBits k).flatMap (fun l => [false :: l, true :: l])

/-- `allBits k` holds exactly the words of length k. -/
theorem mem_allBits : ∀ (k : ℕ) (l : List Bool), l ∈ allBits k ↔ l.length = k
  | 0, l => by
    cases l with
    | nil =>
      simp [allBits]
    | cons b t =>
      simp [allBits]
  | k + 1, l => by
    cases l with
    | nil =>
      simp [allBits]
    | cons b t =>
      simp only [allBits, List.mem_flatMap, List.mem_cons, List.cons.injEq,
        List.not_mem_nil, or_false, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨a, ha, h⟩
        rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact (mem_allBits k _).mp ha
        · exact (mem_allBits k _).mp ha
      · intro h
        refine ⟨t, (mem_allBits k t).mpr h, ?_⟩
        cases b
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩

/-! ## 2. The q-family -/

variable {q : ℕ}

/-- q/2 for an odd step, 1/2 for a halving. -/
def factorQ (q : ℕ) (b : Bool) : ℚ := if b then (q : ℚ) / 2 else 1 / 2

/-- Product of the factors of a word. -/
def seqProductQ (q : ℕ) (s : List Bool) : ℚ := (s.map (factorQ q)).prod

/-- Level of s after j steps. -/
def lvlQ (q : ℕ) (s : List Bool) (j : ℕ) : ℚ := seqProductQ q (s.take j)

/-- An admissible word of the q-family. -/
structure AdmissibleQ (q : ℕ) (s : List Bool) : Prop where
  /-- Every proper nonempty prefix has level > 1. -/
  prefix_gt : ∀ m, 1 ≤ m → m < s.length → 1 < seqProductQ q (s.take m)
  /-- The whole word has level < 1. -/
  lt_one : seqProductQ q s < 1

/-- `AdmissibleQ` is decidable. -/
instance (q : ℕ) (s : List Bool) : Decidable (AdmissibleQ q s) :=
  decidable_of_iff
    ((∀ m, 1 ≤ m → m < s.length → 1 < seqProductQ q (s.take m)) ∧ seqProductQ q s < 1)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

/-- Length of an admissible word of Order n: the least p with q^n < 2^p. -/
def p2Q (q n : ℕ) : ℕ := Nat.log 2 (q ^ n) + 1

/-- Admissible words of Order n in the q-family. -/
def admSetQ (q n : ℕ) : Finset (List Bool) :=
  (allBits (p2Q q n)).toFinset.filter (fun s => AdmissibleQ q s ∧ order s = n)

theorem seqProductQ_append (q : ℕ) (a b : List Bool) :
    seqProductQ q (a ++ b) = seqProductQ q a * seqProductQ q b := by
  simp [seqProductQ, List.map_append, List.prod_append]

/-- The product of a word times 2^length is q^Order. -/
theorem seqProductQ_mul_pow (q : ℕ) (l : List Bool) :
    seqProductQ q l * 2 ^ l.length = (q : ℚ) ^ order l := by
  induction l with
  | nil => simp [seqProductQ, order]
  | cons b t ih =>
    cases b with
    | true =>
      have hord : order (true :: t) = order t + 1 := by
        unfold order
        simp
      have hprod : seqProductQ q (true :: t) = (q : ℚ) / 2 * seqProductQ q t := by
        simp [seqProductQ, factorQ]
      rw [hprod, hord, List.length_cons, pow_succ, pow_succ, ← ih]
      ring
    | false =>
      have hord : order (false :: t) = order t := by
        unfold order
        simp
      have hprod : seqProductQ q (false :: t) = 1 / 2 * seqProductQ q t := by
        simp [seqProductQ, factorQ]
      rw [hprod, hord, List.length_cons, pow_succ, ← ih]
      ring

theorem lvlQ_zero (q : ℕ) (s : List Bool) : lvlQ q s 0 = 1 := by
  simp [lvlQ, seqProductQ]

theorem lvlQ_succ (q : ℕ) (s : List Bool) {p : ℕ} {b : Bool} (h : s[p]? = some b) :
    lvlQ q s (p + 1) = lvlQ q s p * factorQ q b := by
  unfold lvlQ
  rw [List.take_add_one, h, seqProductQ_append]
  simp [seqProductQ]

/-- lvlQ q s j times 2^j is q to the Order of the first j steps. -/
theorem lvlQ_mul_pow (q : ℕ) {s : List Bool} {j : ℕ} (hj : j ≤ s.length) :
    lvlQ q s j * 2 ^ j = (q : ℚ) ^ order (s.take j) := by
  have hlen : (s.take j).length = j := by
    simp [hj]
  unfold lvlQ
  rw [← seqProductQ_mul_pow, hlen]

/-- For q ≥ 2 an admissible word ends with a halving. -/
theorem admissibleQ_last_false {q : ℕ} (hq : 2 ≤ q) {s : List Bool} (hA : AdmissibleQ q s)
    (hne : s ≠ []) : s.getLast hne = false := by
  by_contra hlast
  simp only [Bool.not_eq_false] at hlast
  have hsplit : s = s.dropLast ++ [s.getLast hne] :=
    (List.dropLast_append_getLast hne).symm
  have hfull : seqProductQ q s = seqProductQ q s.dropLast * ((q : ℚ) / 2) := by
    rw [hsplit, seqProductQ_append, List.dropLast_concat]
    simp [seqProductQ, factorQ, hlast]
  have hq2 : (1 : ℚ) ≤ (q : ℚ) / 2 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  have hlt := hA.lt_one
  rw [hfull] at hlt
  have hdlen : s.dropLast.length = s.length - 1 := by simp
  have hlen : s.length ≥ 1 := List.length_pos_of_ne_nil hne
  rcases Nat.lt_or_ge s.length 2 with hlt2 | hge2
  · have hz : s.dropLast.length = 0 := by omega
    have hdl : s.dropLast = [] := List.length_eq_zero_iff.mp hz
    rw [hdl] at hlt
    simp only [seqProductQ, List.map_nil, List.prod_nil, one_mul] at hlt
    linarith
  · have hdltake : s.dropLast = s.take s.dropLast.length := by
      simp [List.dropLast_eq_take]
    have hprefix : 1 < seqProductQ q s.dropLast := by
      rw [hdltake]
      exact hA.prefix_gt s.dropLast.length (by omega) (by omega)
    nlinarith

/-- For q ≥ 2 an admissible word of Order n has length p2Q q n. -/
theorem admissibleQ_length {q : ℕ} (hq : 2 ≤ q) {s : List Bool} (hA : AdmissibleQ q s) :
    s.length = p2Q q (order s) := by
  have hne : s ≠ [] := by
    intro hcontra
    have h := hA.lt_one
    rw [hcontra] at h
    simp [seqProductQ] at h
  have hlast := admissibleQ_last_false hq hA hne
  have hsplit : s = s.dropLast ++ [false] := by
    rw [← hlast]
    exact (List.dropLast_append_getLast hne).symm
  have hdlen : s.dropLast.length = s.length - 1 := by simp
  have hdord : order s.dropLast = order s := by
    conv_rhs => rw [hsplit]
    unfold order
    simp
  have hnpos : s.length ≥ 1 := List.length_pos_of_ne_nil hne
  have hub : q ^ order s < 2 ^ s.length := by
    have heq := seqProductQ_mul_pow q s
    have h2pos : (0 : ℚ) < 2 ^ s.length := by positivity
    have hstep := mul_lt_mul_of_pos_right hA.lt_one h2pos
    rw [heq, one_mul] at hstep
    exact_mod_cast hstep
  rcases Nat.lt_or_ge s.length 2 with hlt2 | hge2
  · have hz : s.dropLast.length = 0 := by omega
    have hdl : s.dropLast = [] := List.length_eq_zero_iff.mp hz
    have hord0 : order s = 0 := by
      rw [← hdord, hdl]
      rfl
    have hl1 : s.length = 1 := by omega
    rw [hl1, hord0]
    simp [p2Q]
  · have hdltake : s.dropLast = s.take s.dropLast.length := by
      simp [List.dropLast_eq_take]
    have hlb_raw : 1 < seqProductQ q s.dropLast := by
      rw [hdltake]
      exact hA.prefix_gt s.dropLast.length (by omega) (by omega)
    have hlb : 2 ^ (s.length - 1) ≤ q ^ order s := by
      have heq := seqProductQ_mul_pow q s.dropLast
      rw [hdord, hdlen] at heq
      have h2pos : (0 : ℚ) < 2 ^ (s.length - 1) := by positivity
      have hstep := mul_lt_mul_of_pos_right hlb_raw h2pos
      rw [heq, one_mul] at hstep
      exact_mod_cast hstep.le
    have hub' : q ^ order s < 2 ^ (s.length - 1 + 1) := by
      rw [Nat.sub_add_cancel hnpos]
      exact hub
    have hlog : Nat.log 2 (q ^ order s) = s.length - 1 :=
      Nat.log_eq_of_pow_le_of_lt_pow hlb hub'
    unfold p2Q
    omega

/-- Membership in `admSetQ q n`. -/
theorem mem_admSetQ {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (s : List Bool) :
    s ∈ admSetQ q n ↔ AdmissibleQ q s ∧ order s = n := by
  simp only [admSetQ, Finset.mem_filter, List.mem_toFinset, mem_allBits]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    rw [admissibleQ_length hq h.1, h.2]

/-! ## 3. The sweep and the inclusion -/

/-- Step indices of s, sorted by endpoint level, highest first. -/
def sweepIdxQ (q : ℕ) (s : List Bool) : List ℕ :=
  (List.range s.length).mergeSort (fun i k => decide (lvlQ q s (k + 1) ≤ lvlQ q s (i + 1)))

/-- Sweep map: the steps of s in the order of `sweepIdxQ`. -/
def sweepQ (q : ℕ) (s : List Bool) : List Bool := (sweepIdxQ q s).map (fun i => s.getD i false)

theorem sweepIdxQ_perm (q : ℕ) (s : List Bool) : (sweepIdxQ q s).Perm (List.range s.length) :=
  List.mergeSort_perm _ _

theorem sweepIdxQ_nodup (q : ℕ) (s : List Bool) : (sweepIdxQ q s).Nodup :=
  (sweepIdxQ_perm q s).nodup_iff.mpr List.nodup_range

theorem mem_sweepIdxQ {s : List Bool} {i : ℕ} : i ∈ sweepIdxQ q s ↔ i < s.length := by
  rw [(sweepIdxQ_perm q s).mem_iff, List.mem_range]

theorem sweepIdxQ_pairwise (q : ℕ) (s : List Bool) :
    (sweepIdxQ q s).Pairwise (fun i k => lvlQ q s (k + 1) ≤ lvlQ q s (i + 1)) := by
  have h := List.pairwise_mergeSort
    (le := fun i k => decide (lvlQ q s (k + 1) ≤ lvlQ q s (i + 1)))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hbc hab)
    (fun a b => by
      rcases le_total (lvlQ q s (b + 1)) (lvlQ q s (a + 1)) with h | h
      · simp [h]
      · simp [h])
    (List.range s.length)
  exact h.imp (fun hab => by simpa using hab)

theorem map_getD_range (s : List Bool) :
    (List.range s.length).map (fun i => s.getD i false) = s := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

/-- The sweep permutes the steps. -/
theorem sweepQ_perm (q : ℕ) (s : List Bool) : (sweepQ q s).Perm s := by
  have h := (sweepIdxQ_perm q s).map (fun i => s.getD i false)
  rw [map_getD_range] at h
  exact h

theorem length_sweepQ (q : ℕ) (s : List Bool) : (sweepQ q s).length = s.length :=
  (sweepQ_perm q s).length_eq

theorem seqProductQ_sweepQ (q : ℕ) (s : List Bool) :
    seqProductQ q (sweepQ q s) = seqProductQ q s :=
  ((sweepQ_perm q s).map (factorQ q)).prod_eq

theorem order_sweepQ (q : ℕ) (s : List Bool) : order (sweepQ q s) = order s :=
  ((sweepQ_perm q s).filter id).length_eq

/-- Levels after different step counts differ. -/
theorem lvlQ_ne_of_ne (hodd : Odd q) {s : List Bool} {i k : ℕ} (hi : i ≤ s.length)
    (hk : k ≤ s.length) (hne : i ≠ k) : lvlQ q s i ≠ lvlQ q s k := by
  intro heq
  have key : ∀ {a b : ℕ}, a ≤ s.length → b ≤ s.length → a < b → lvlQ q s a = lvlQ q s b →
      False := by
    intro a b ha hb hab he
    have h1 := lvlQ_mul_pow q ha
    have h2 := lvlQ_mul_pow q hb
    have hsplit : (2 : ℚ) ^ b = 2 ^ a * 2 ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    have hq : ((q ^ order (s.take b) : ℕ) : ℚ) =
        ((q ^ order (s.take a) * 2 ^ (b - a) : ℕ) : ℚ) := by
      push_cast
      rw [← h1, ← h2, ← he, hsplit]
      ring
    have hn : q ^ order (s.take b) = q ^ order (s.take a) * 2 ^ (b - a) := by
      exact_mod_cast hq
    have hoddp : (q ^ order (s.take b)) % 2 = 1 :=
      Nat.odd_iff.mp (hodd.pow)
    have heven : (q ^ order (s.take a) * 2 ^ (b - a)) % 2 = 0 := by
      have hba : b - a = (b - a - 1) + 1 := by omega
      rw [hba, pow_succ]
      simp [← mul_assoc, Nat.mul_mod_left]
    omega
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key hi hk h heq
  · exact key hk hi h heq.symm

/-- The steps whose endpoint levels reach t > 1, and no others, multiply to more than 1. -/
theorem prod_gt_one_of_upperQ (hq0 : 0 < q) (s : List Bool) (T : Finset ℕ) {t : ℚ} (ht : 1 < t)
    (hT : ∀ i ∈ T, i < s.length ∧ t ≤ lvlQ q s (i + 1))
    (hN : ∀ i < s.length, i ∉ T → lvlQ q s (i + 1) < t) (hne : T.Nonempty) :
    1 < ∏ i ∈ T, factorQ q (s.getD i false) := by
  let g : ℕ → ℚ := fun m => ∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hfac : ∀ i, 0 < factorQ q (s.getD i false) := by
    intro i
    unfold factorQ
    split_ifs
    · exact div_pos hq0' (by norm_num)
    · norm_num
  have hg_succ_mem : ∀ m, m ∈ T → g (m + 1) = g m * factorQ q (s.getD m false) := by
    intro m hm
    change ∏ i ∈ (Finset.range (m + 1)).filter (· ∈ T), factorQ q (s.getD i false) =
      (∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)) *
        factorQ q (s.getD m false)
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hm, ↓reduceIte]
    rw [Finset.prod_insert (by simp), mul_comm]
  have hg_succ_not : ∀ m, m ∉ T → g (m + 1) = g m := by
    intro m hm
    change ∏ i ∈ (Finset.range (m + 1)).filter (· ∈ T), factorQ q (s.getD i false) =
      ∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hm, ↓reduceIte]
  have hg_empty : ∀ m, (∀ i ∈ T, m ≤ i) → g m = 1 := by
    intro m hm
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have := hm i hi.2
    omega
  have inv : ∀ m ≤ s.length,
      lvlQ q s m < g m * t ∧ ((∃ i ∈ T, i < m) → 1 < g m) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [lvlQ_zero q, hg_empty 0 (fun i _ => Nat.zero_le i), one_mul]
        exact ht
      · rintro ⟨i, _, hi⟩
        omega
    | succ m ih =>
      intro hm
      obtain ⟨ihA, ihJ⟩ := ih (by omega)
      have hlt : m < s.length := by omega
      have hget : s[m]? = some (s.getD m false) := by
        simp [List.getD_eq_getElem?_getD, hlt]
      have hstep := lvlQ_succ q s hget
      by_cases hmT : m ∈ T
      · rw [hg_succ_mem m hmT]
        have hA : lvlQ q s (m + 1) < g m * factorQ q (s.getD m false) * t := by
          rw [hstep]
          have hf := hfac m
          nlinarith
        refine ⟨hA, fun _ => ?_⟩
        have ht_le := (hT m hmT).2
        have hpos : 0 < t := by linarith
        by_contra hle
        push Not at hle
        nlinarith
      · rw [hg_succ_not m hmT]
        have hlow := hN m hlt hmT
        by_cases hex : ∃ i ∈ T, i < m
        · have h1 := ihJ hex
          refine ⟨by nlinarith, fun _ => h1⟩
        · push Not at hex
          rw [hg_empty m hex]
          refine ⟨by linarith, ?_⟩
          rintro ⟨i, hi, him⟩
          have := hex i hi
          have hne' : i ≠ m := fun h => hmT (h ▸ hi)
          omega
  obtain ⟨_, hJ⟩ := inv s.length le_rfl
  obtain ⟨i, hi⟩ := hne
  have hfilter : (Finset.range s.length).filter (· ∈ T) = T := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨(hT k h).1, h⟩
  have h1 := hJ ⟨i, hi, (hT i hi).1⟩
  change 1 < ∏ i ∈ (Finset.range s.length).filter (· ∈ T), factorQ q (s.getD i false) at h1
  rwa [hfilter] at h1

/-- The sweep maps admissible words of Order n to admissible words of Order n. -/
theorem sweepQ_mem_admSetQ (hodd : Odd q) (hq2 : 2 ≤ q) {n : ℕ} {s : List Bool}
    (hs : s ∈ admSetQ q n) :
    sweepQ q s ∈ admSetQ q n := by
  rw [mem_admSetQ hq2 n] at hs ⊢
  obtain ⟨hA, hord⟩ := hs
  refine ⟨⟨?_, ?_⟩, by rw [order_sweepQ, hord]⟩
  · intro m hm1 hmL
    rw [length_sweepQ] at hmL
    set l := sweepIdxQ q s with hl
    have hnd : l.Nodup := sweepIdxQ_nodup q s
    have hpw := sweepIdxQ_pairwise q s
    have hlen : l.length = s.length := by
      rw [(sweepIdxQ_perm q s).length_eq, List.length_range]
    have hsplit : (l.take m ++ l.drop m).Nodup := by
      rw [List.take_append_drop]
      exact hnd
    obtain ⟨hnd1, _, hdisj⟩ := List.nodup_append.mp hsplit
    set T := (l.take m).toFinset with hTdef
    have hprod : seqProductQ q ((sweepQ q s).take m) = ∏ i ∈ T, factorQ q (s.getD i false) := by
      rw [List.prod_toFinset _ hnd1]
      unfold sweepQ seqProductQ
      rw [← List.map_take, List.map_map]
      rfl
    rw [hprod]
    have hmemT : ∀ i ∈ T, i < s.length := by
      intro i hi
      rw [List.mem_toFinset] at hi
      exact mem_sweepIdxQ.mp (List.mem_of_mem_take hi)
    have hbelow : ∀ i ∈ T, ∀ k, k < s.length → k ∉ T → lvlQ q s (k + 1) < lvlQ q s (i + 1) := by
      intro i hi k hk hkT
      rw [List.mem_toFinset] at hi hkT
      have hkl : k ∈ l := mem_sweepIdxQ.mpr hk
      rw [← List.take_append_drop m l, List.mem_append] at hkl
      have hkd : k ∈ l.drop m := hkl.resolve_left hkT
      have hle := hpw.rel_of_mem_take_of_mem_drop hi hkd
      have hik : i ≠ k := hdisj i hi k hkd
      have hi' := mem_sweepIdxQ.mp (List.mem_of_mem_take hi)
      exact lt_of_le_of_ne hle (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
    have hne : T.Nonempty := by
      rw [List.toFinset_nonempty_iff, ← List.length_pos_iff]
      rw [List.length_take]
      omega
    have hgt1 : ∀ i ∈ T, 1 < lvlQ q s (i + 1) := by
      intro i hi
      have hiL := hmemT i hi
      by_cases hlast : i + 1 < s.length
      · exact hA.prefix_gt (i + 1) (by omega) hlast
      · exfalso
        have hdrop : (l.drop m).length ≠ 0 := by
          rw [List.length_drop]
          omega
        obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos
          (Nat.pos_of_ne_zero hdrop))
        have hkL : k < s.length := mem_sweepIdxQ.mp (List.mem_of_mem_drop hk)
        have hkT : k ∉ T := by
          rw [List.mem_toFinset]
          intro hkt
          exact hdisj k hkt k hk rfl
        have hlt := hbelow i hi k hkL hkT
        have hik : k ≠ i := by
          intro h
          exact hkT (h ▸ hi)
        have hk1 : k + 1 < s.length := by omega
        have hkgt := hA.prefix_gt (k + 1) (by omega) hk1
        have hend : lvlQ q s (i + 1) < 1 := by
          have heq : i + 1 = s.length := by omega
          rw [heq]
          unfold lvlQ
          rw [List.take_length]
          exact hA.lt_one
        change 1 < lvlQ q s (k + 1) at hkgt
        linarith
    apply prod_gt_one_of_upperQ (by omega) s T (t := T.inf' hne (fun i => lvlQ q s (i + 1)))
    · rw [Finset.lt_inf'_iff]
      exact hgt1
    · exact fun i hi => ⟨hmemT i hi, Finset.inf'_le _ hi⟩
    · intro k hk hkT
      rw [Finset.lt_inf'_iff]
      exact fun i hi => hbelow i hi k hk hkT
    · exact hne
  · rw [seqProductQ_sweepQ]
    exact hA.lt_one

/-! ## 4. The integer sweep of Thomas and Williams -/

/-- Integer level of w after m steps: weight a1 per odd step, a2 per halving. -/
def lvlZ (a1 a2 : ℤ) (w : List Bool) (m : ℕ) : ℤ :=
  ((w.take m).map (fun b => if b then a1 else a2)).sum

/-- Sort key of step i in the sweep of Thomas and Williams: negative endpoint levels
    first, then endpoint level, then index, all descending. -/
def twKey (a1 a2 : ℤ) (w : List Bool) (i : ℕ) : Lex (Bool × Lex (ℤ × ℕ)) :=
  toLex (decide (lvlZ a1 a2 w (i + 1) < 0), toLex (lvlZ a1 a2 w (i + 1), i))

/-- Step indices of w in the order of `twKey`, largest first. -/
def sweepIdxZ (a1 a2 : ℤ) (w : List Bool) : List ℕ :=
  (List.range w.length).mergeSort (fun i k => decide (twKey a1 a2 w k ≤ twKey a1 a2 w i))

/-- Integer sweep: the steps of w in the order of `sweepIdxZ`. -/
def sweepZ (a1 a2 : ℤ) (w : List Bool) : List Bool :=
  (sweepIdxZ a1 a2 w).map (fun i => w.getD i false)

/-- Dyck words: e1 odd steps, e2 halvings, no integer level below 0. -/
def dyckSet (a1 a2 : ℤ) (e1 e2 : ℕ) : Set (List Bool) :=
  {w | w.count true = e1 ∧ w.count false = e2 ∧ ∀ m ≤ w.length, 0 ≤ lvlZ a1 a2 w m}

/-- Words with e1 odd steps and e2 halvings. -/
def contentSet (e1 e2 : ℕ) : Set (List Bool) :=
  {w | w.count true = e1 ∧ w.count false = e2}

/-- A Dyck word is a word of its content. -/
theorem dyckSet_subset_contentSet (a1 a2 : ℤ) (e1 e2 : ℕ) :
    dyckSet a1 a2 e1 e2 ⊆ contentSet e1 e2 :=
  fun _ h => ⟨h.1, h.2.1⟩

/-- Thomas and Williams, Sweeping up Zeta (2018), Thm 6.3, for two letters. -/
def SweepBijective : Prop :=
  ∀ (a1 a2 : ℤ) (e1 e2 : ℕ),
    Set.BijOn (sweepZ a1 a2) (contentSet e1 e2) (contentSet e1 e2)

theorem sum_map_weights (a1 a2 : ℤ) (l : List Bool) :
    (l.map (fun b => if b then a1 else a2)).sum =
      a1 * order l + a2 * ((l.length : ℤ) - order l) := by
  induction l with
  | nil => simp [order]
  | cons b t ih =>
    cases b with
    | true =>
      have hord : order (true :: t) = order t + 1 := by
        unfold order
        simp
      rw [List.map_cons, List.sum_cons, ih, hord, List.length_cons]
      simp only [↓reduceIte]
      push_cast
      ring
    | false =>
      have hord : order (false :: t) = order t := by
        unfold order
        simp
      rw [List.map_cons, List.sum_cons, ih, hord, List.length_cons]
      push_cast
      ring

theorem lvlZ_weights (c d : ℤ) {s : List Bool} {m : ℕ} (hm : m ≤ s.length) :
    lvlZ (c - d) (-d) s m = c * order (s.take m) - d * m := by
  unfold lvlZ
  rw [sum_map_weights]
  have hlen : (s.take m).length = m := by
    simp [hm]
  rw [hlen]
  ring

theorem sweepIdxZ_perm (a1 a2 : ℤ) (w : List Bool) :
    (sweepIdxZ a1 a2 w).Perm (List.range w.length) :=
  List.mergeSort_perm _ _

theorem sweepIdxZ_nodup (a1 a2 : ℤ) (w : List Bool) : (sweepIdxZ a1 a2 w).Nodup :=
  (sweepIdxZ_perm a1 a2 w).nodup_iff.mpr List.nodup_range

theorem sweepIdxZ_pairwise (a1 a2 : ℤ) (w : List Bool) :
    (sweepIdxZ a1 a2 w).Pairwise (fun i k => twKey a1 a2 w k ≤ twKey a1 a2 w i) := by
  have h := List.pairwise_mergeSort
    (le := fun i k => decide (twKey a1 a2 w k ≤ twKey a1 a2 w i))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hbc hab)
    (fun a b => by
      rcases le_total (twKey a1 a2 w b) (twKey a1 a2 w a) with h | h
      · simp [h]
      · simp [h])
    (List.range w.length)
  exact h.imp (fun hab => by simpa using hab)

theorem lvlZ_append_false (a1 a2 : ℤ) {w : List Bool} {m : ℕ} (hm : m ≤ w.length) :
    lvlZ a1 a2 (w ++ [false]) m = lvlZ a1 a2 w m := by
  unfold lvlZ
  rw [List.take_append_of_le_length hm]

theorem lvlZ_zero (a1 a2 : ℤ) (w : List Bool) : lvlZ a1 a2 w 0 = 0 := by
  simp [lvlZ]

theorem count_true_add_count_false (l : List Bool) :
    l.count true + l.count false = l.length := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | true =>
      simp only [List.count_cons, List.length_cons]
      simp
      omega
    | false =>
      simp only [List.count_cons, List.length_cons]
      simp
      omega

/-! ## 5. Weights and the bijection -/

/-! ### Powers of 2 and q -/

theorem one_le_p2Q (q a : ℕ) : 1 ≤ p2Q q a := by
  unfold p2Q
  omega

theorem q_pow_lt_two_pow_iff (hq : 3 ≤ q) {a k : ℕ} : q ^ a < 2 ^ k ↔ p2Q q a ≤ k := by
  unfold p2Q
  rw [← Nat.log_lt_iff_lt_pow (by norm_num) (pow_ne_zero _ (by omega))]
  omega

theorem p2Q_spec (hq : 3 ≤ q) (a : ℕ) : q ^ a < 2 ^ p2Q q a :=
  (q_pow_lt_two_pow_iff hq).mpr le_rfl

theorem p2Q_spec_lower (hq : 3 ≤ q) (a : ℕ) : 2 ^ (p2Q q a - 1) ≤ q ^ a := by
  unfold p2Q
  simp only [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 (pow_ne_zero _ (by omega))

theorem two_pow_ne_q_pow (hodd : Odd q) (hq : 3 ≤ q) {a k : ℕ} (ha : 1 ≤ a) :
    2 ^ k ≠ q ^ a := by
  intro h
  rcases k with _ | k
  · have h1 : 1 < q ^ a := Nat.one_lt_pow (by omega) (by omega)
    rw [pow_zero] at h
    omega
  · have hoddp : (q ^ a) % 2 = 1 := Nat.odd_iff.mp hodd.pow
    have heven : (2 ^ (k + 1)) % 2 = 0 := by
      rw [pow_succ]
      simp
    omega

theorem two_pow_lt_q_pow_iff (hodd : Odd q) (hq : 3 ≤ q) {a k : ℕ} (ha : 1 ≤ a) :
    2 ^ k < q ^ a ↔ k < p2Q q a := by
  constructor
  · intro h
    by_contra hk
    push Not at hk
    have := (q_pow_lt_two_pow_iff hq).mpr hk
    omega
  · intro h
    rcases lt_or_ge (2 ^ k) (q ^ a) with h1 | h1
    · exact h1
    · exfalso
      rcases h1.lt_or_eq with h2 | h2
      · have := (q_pow_lt_two_pow_iff hq).mp h2
        omega
      · exact two_pow_ne_q_pow hodd hq ha h2.symm

theorem q_pow_mul_lt_iff (hq : 3 ≤ q) {a x y : ℕ} :
    q ^ a * 2 ^ x < 2 ^ y ↔ x + p2Q q a ≤ y := by
  by_cases hxy : x ≤ y
  · obtain ⟨e, rfl⟩ : ∃ e, y = x + e := ⟨y - x, by omega⟩
    rw [pow_add, mul_comm (2 ^ x), Nat.mul_lt_mul_right (by positivity),
      q_pow_lt_two_pow_iff hq]
    omega
  · have h1 : 2 ^ y < 2 ^ x := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ x ≤ q ^ a * 2 ^ x := Nat.le_mul_of_pos_left _ (by positivity)
    constructor
    · intro h
      omega
    · intro h
      omega

theorem lt_q_pow_mul_iff (hodd : Odd q) (hq : 3 ≤ q) {a x y : ℕ} (ha : 1 ≤ a) :
    2 ^ y < q ^ a * 2 ^ x ↔ y < x + p2Q q a := by
  by_cases hxy : x ≤ y
  · obtain ⟨e, rfl⟩ : ∃ e, y = x + e := ⟨y - x, by omega⟩
    rw [pow_add, mul_comm (2 ^ x), Nat.mul_lt_mul_right (by positivity),
      two_pow_lt_q_pow_iff hodd hq ha]
    omega
  · have h1 : 2 ^ y < 2 ^ x := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ x ≤ q ^ a * 2 ^ x := Nat.le_mul_of_pos_left _ (by positivity)
    constructor
    · intro _
      omega
    · intro _
      omega

/-- (p2(a) - 1)/a < p2(b)/b, cross-multiplied. -/
theorem p2Q_sub_one_mul_lt (hq : 3 ≤ q) {a b : ℕ} (ha : 1 ≤ a) :
    (p2Q q a - 1) * b < a * p2Q q b := by
  have h1 : (2 ^ (p2Q q a - 1)) ^ b ≤ (q ^ a) ^ b := Nat.pow_le_pow_left (p2Q_spec_lower hq a) b
  have h2 : (q ^ b) ^ a < (2 ^ p2Q q b) ^ a :=
    Nat.pow_lt_pow_left (p2Q_spec hq b) (by omega)
  have h1' : 2 ^ ((p2Q q a - 1) * b) ≤ q ^ (a * b) := by
    rw [pow_mul, pow_mul]
    exact h1
  have h2' : q ^ (a * b) < 2 ^ (a * p2Q q b) := by
    rw [mul_comm a b, pow_mul, mul_comm a, pow_mul]
    exact h2
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h1' h2')

/-- Integer weights c, d strictly between (p2(a) - 1)/a and p2(a)/a for 1 ≤ a ≤ n + 1. -/
theorem exists_weightsQ (hq : 3 ≤ q) (n : ℕ) : ∃ c d : ℤ, 0 < d ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
    d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a := by
  have hS : (Finset.Icc 1 (n + 1)).Nonempty := ⟨1, by simp⟩
  set lo := (Finset.Icc 1 (n + 1)).sup' hS (fun a => ((p2Q q a : ℚ) - 1) / a) with hlo
  set hi := (Finset.Icc 1 (n + 1)).inf' hS (fun a => (p2Q q a : ℚ) / a) with hhi
  have hlohi : lo < hi := by
    rw [hlo, Finset.sup'_lt_iff]
    intro a ha
    rw [hhi, Finset.lt_inf'_iff]
    intro b hb
    simp only [Finset.mem_Icc] at ha hb
    have hapos : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
    have hbpos : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [div_lt_div_iff₀ hapos hbpos]
    have hn := p2Q_sub_one_mul_lt hq (b := b) (by omega : 1 ≤ a)
    have hp := one_le_p2Q q a
    have hq : (((p2Q q a - 1) * b : ℕ) : ℚ) < ((a * p2Q q b : ℕ) : ℚ) := by
      exact_mod_cast hn
    push_cast [Nat.cast_sub hp] at hq
    linarith
  set r := (lo + hi) / 2 with hr
  have hrlo : lo < r := by
    rw [hr]
    linarith
  have hrhi : r < hi := by
    rw [hr]
    linarith
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hrq : r = (r.num : ℚ) / r.den := (Rat.num_div_den r).symm
  refine ⟨r.num, r.den, by exact_mod_cast r.den_pos, fun a ha1 ha2 => ?_⟩
  have haS : a ∈ Finset.Icc 1 (n + 1) := by simp [ha1, ha2]
  have hapos : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  have hl : ((p2Q q a : ℚ) - 1) / a < r :=
    lt_of_le_of_lt (Finset.le_sup' (fun a => ((p2Q q a : ℚ) - 1) / a) haS) hrlo
  have hh : r < (p2Q q a : ℚ) / a :=
    lt_of_lt_of_le hrhi (Finset.inf'_le (fun a => (p2Q q a : ℚ) / a) haS)
  rw [div_lt_iff₀ hapos, hrq, div_mul_eq_mul_div, lt_div_iff₀ hden] at hl
  rw [lt_div_iff₀ hapos, hrq, div_mul_eq_mul_div, div_lt_iff₀ hden] at hh
  constructor
  · have hq : ((r.den * ((p2Q q a : ℤ) - 1) : ℤ) : ℚ) < ((r.num * a : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hq
  · have hq : ((r.num * a : ℤ) : ℚ) < ((r.den * p2Q q a : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hq

/-- The weights order the lattice points of Order n like the 3-smooth levels. -/
theorem q_pow_lt_iff_weights (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {o o' j j' : ℕ} (ho : o ≤ n) (ho' : o' ≤ n) :
    q ^ o * 2 ^ j' < q ^ o' * 2 ^ j ↔ c * o - d * j < c * o' - d * j' := by
  rcases le_or_gt o' o with hle | hlt
  · obtain ⟨a, rfl⟩ : ∃ a, o = o' + a := ⟨o - o', by omega⟩
    have hcancel : q ^ (o' + a) * 2 ^ j' < q ^ o' * 2 ^ j ↔ q ^ a * 2 ^ j' < 2 ^ j := by
      rw [pow_add, mul_assoc, Nat.mul_lt_mul_left (by positivity)]
    rw [hcancel]
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rw [ha0, pow_zero, one_mul, Nat.pow_lt_pow_iff_right (by norm_num)]
      push_cast
      constructor
      · intro h
        have : (j' : ℤ) < j := by exact_mod_cast h
        nlinarith
      · intro h
        by_contra hj
        push Not at hj
        have : (j : ℤ) ≤ j' := by exact_mod_cast hj
        nlinarith
    · rw [q_pow_mul_lt_iff hq]
      obtain ⟨h1, h2⟩ := hcd a (by omega) (by omega)
      push_cast
      constructor
      · intro h
        have hz : (p2Q q a : ℤ) ≤ (j : ℤ) - j' := by omega
        have := mul_le_mul_of_nonneg_left hz (le_of_lt hd)
        nlinarith
      · intro h
        by_contra hz
        have hz' : (j : ℤ) - j' ≤ (p2Q q a : ℤ) - 1 := by omega
        have := mul_le_mul_of_nonneg_left hz' (le_of_lt hd)
        nlinarith
  · obtain ⟨a, rfl⟩ : ∃ a, o' = o + a := ⟨o' - o, by omega⟩
    have hcancel : q ^ o * 2 ^ j' < q ^ (o + a) * 2 ^ j ↔ 2 ^ j' < q ^ a * 2 ^ j := by
      rw [pow_add, mul_assoc, Nat.mul_lt_mul_left (by positivity)]
    rw [hcancel, lt_q_pow_mul_iff hodd hq (by omega)]
    obtain ⟨h1, h2⟩ := hcd a (by omega) (by omega)
    push_cast
    constructor
    · intro h
      have hz : (j' : ℤ) - j ≤ (p2Q q a : ℤ) - 1 := by omega
      have := mul_le_mul_of_nonneg_left hz (le_of_lt hd)
      nlinarith
    · intro h
      by_contra hz
      have hz' : (p2Q q a : ℤ) ≤ (j' : ℤ) - j := by omega
      have := mul_le_mul_of_nonneg_left hz' (le_of_lt hd)
      nlinarith

/-- Levels of an admissible word of Order n compare like their integer levels. -/
theorem lvlQ_lt_iff_lvlZ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {s : List Bool} (hs : order s = n) {i k : ℕ} (hi : i ≤ s.length) (hk : k ≤ s.length) :
    lvlQ q s i < lvlQ q s k ↔ lvlZ (c - d) (-d) s i < lvlZ (c - d) (-d) s k := by
  rw [lvlZ_weights c d hi, lvlZ_weights c d hk]
  have hoi : order (s.take i) ≤ n := hs ▸ order_take_le s i
  have hok : order (s.take k) ≤ n := hs ▸ order_take_le s k
  rw [← q_pow_lt_iff_weights hodd hq hd hcd hoi hok]
  have h1 := lvlQ_mul_pow q hi
  have h2 := lvlQ_mul_pow q hk
  have hp1 : (0 : ℚ) < 2 ^ i := by positivity
  have hp2 : (0 : ℚ) < 2 ^ k := by positivity
  have hcast : (q ^ order (s.take i) * 2 ^ k < q ^ order (s.take k) * 2 ^ i) ↔
      ((q : ℚ) ^ order (s.take i) * 2 ^ k < q ^ order (s.take k) * 2 ^ i) := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  rw [hcast, ← h1, ← h2]
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h (mul_pos hp1 hp2)
    nlinarith
  · intro h
    by_contra hle
    push Not at hle
    have := mul_le_mul_of_nonneg_right hle (le_of_lt (mul_pos hp1 hp2))
    nlinarith

/-- An admissible word ends with its final halving. -/
theorem exists_eq_append_falseQ (hq : 3 ≤ q) {n : ℕ} {s : List Bool} (hs : s ∈ admSetQ q n) :
    ∃ w, s = w ++ [false] := by
  have hA := ((mem_admSetQ (by omega) _ s).mp hs).1
  have hne : s ≠ [] := by
    intro h
    have := hA.lt_one
    rw [h] at this
    simp [seqProductQ] at this
  refine ⟨s.dropLast, ?_⟩
  have h := (List.dropLast_append_getLast hne).symm
  rw [admissibleQ_last_false (by omega) hA hne] at h
  exact h

/-- Without its final halving, an admissible word has positive integer levels. -/
theorem lvlZ_posQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ w.length) : 0 < lvlZ (c - d) (-d) w m := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hlen : (w ++ [false]).length = w.length + 1 := by simp
  have hgt : 1 < lvlQ q (w ++ [false]) m := hA.prefix_gt m hm1 (by omega)
  have hlt : lvlQ q (w ++ [false]) 0 < lvlQ q (w ++ [false]) m := by
    rw [lvlQ_zero q]
    exact hgt
  rw [lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (by omega) (by omega), lvlZ_zero,
    lvlZ_append_false _ _ hm] at hlt
  exact hlt

/-- Without its final halving, an admissible word of Order n is a Dyck word. -/
theorem dropLast_mem_dyckSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    w ∈ dyckSet (c - d) (-d) n (w.length - n) := by
  have hord := ((mem_admSetQ (by omega) _ _).mp hs).2
  have htrue : w.count true = n := by
    rw [← hord, order_eq_count_true, List.count_append]
    simp
  refine ⟨htrue, ?_, ?_⟩
  · have h := count_true_add_count_false w
    omega
  · intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, lvlZ_zero]
    · exact le_of_lt (lvlZ_posQ hodd hq hd hcd hs hpos hm)

/-- The sweep of an admissible word sorts like the integer sweep of its Dyck part. -/
theorem sweepIdxQ_eq (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    sweepIdxQ q (w ++ [false]) = sweepIdxZ (c - d) (-d) w ++ [w.length] := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  set s := w ++ [false] with hsdef
  have hlen : s.length = w.length + 1 := by simp [hsdef]
  have hmemZ : ∀ {i}, i ∈ sweepIdxZ (c - d) (-d) w → i < w.length := by
    intro i hi
    rw [(sweepIdxZ_perm _ _ w).mem_iff, List.mem_range] at hi
    exact hi
  apply List.Perm.eq_of_pairwise (le := fun i k => lvlQ q s (k + 1) < lvlQ q s (i + 1))
  · intro a b _ _ hab hba
    exact (lt_asymm hab hba).elim
  · refine ((sweepIdxQ_pairwise q s).and (sweepIdxQ_nodup q s)).imp_of_mem ?_
    intro a b ha hb h
    have ha' := mem_sweepIdxQ.mp ha
    have hb' := mem_sweepIdxQ.mp hb
    exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
  · rw [List.pairwise_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · refine ((sweepIdxZ_pairwise _ _ w).and (sweepIdxZ_nodup _ _ w)).imp_of_mem ?_
      intro a b ha hb h
      have ha' := hmemZ ha
      have hb' := hmemZ hb
      have hpa := lvlZ_posQ hodd hq hd hcd hs (m := a + 1) (by omega) (by omega)
      have hpb := lvlZ_posQ hodd hq hd hcd hs (m := b + 1) (by omega) (by omega)
      have hkey := h.1
      unfold twKey at hkey
      have hfa : decide (lvlZ (c - d) (-d) w (a + 1) < 0) = false := by
        simp only [decide_eq_false_iff_not, not_lt]
        exact le_of_lt hpa
      have hfb : decide (lvlZ (c - d) (-d) w (b + 1) < 0) = false := by
        simp only [decide_eq_false_iff_not, not_lt]
        exact le_of_lt hpb
      rw [hfa, hfb, Prod.Lex.toLex_le_toLex] at hkey
      simp only [lt_self_iff_false, true_and, false_or] at hkey
      rw [Prod.Lex.toLex_le_toLex] at hkey
      have hiff := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := s) (i := b + 1) (k := a + 1)
        (by omega) (by omega)
      rw [lvlZ_append_false _ _ (by omega), lvlZ_append_false _ _ (by omega)] at hiff
      rcases hkey with hlt | ⟨heq, _⟩
      · exact hiff.mpr hlt
      · exfalso
        have hiff' := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := s) (i := a + 1) (k := b + 1)
          (by omega) (by omega)
        rw [lvlZ_append_false _ _ (by omega), lvlZ_append_false _ _ (by omega)] at hiff'
        have hne := lvlQ_ne_of_ne hodd (s := s) (i := a + 1) (k := b + 1) (by omega) (by omega)
          (by omega)
        rcases lt_or_gt_of_ne hne with h1 | h1
        · have := hiff'.mp h1
          omega
        · have := hiff.mp h1
          omega
    · intro a ha b hb
      rw [List.mem_singleton] at hb
      rw [hb]
      have ha' := hmemZ ha
      have hgt : 1 < lvlQ q s (a + 1) := hA.prefix_gt (a + 1) (by omega) (by omega)
      have hend : lvlQ q s (w.length + 1) < 1 := by
        rw [← hlen]
        unfold lvlQ
        rw [List.take_length]
        exact hA.lt_one
      linarith
  · have h := (sweepIdxZ_perm (c - d) (-d) w).append_right [w.length]
    have h2 := sweepIdxQ_perm q s
    rw [hlen, List.range_succ] at h2
    exact h2.trans h.symm

/-- The sweep of an admissible word is the integer sweep of its Dyck part, then the
    final halving. -/
theorem sweepQ_eq_sweepZ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    sweepQ q (w ++ [false]) = sweepZ (c - d) (-d) w ++ [false] := by
  unfold sweepQ sweepZ
  rw [sweepIdxQ_eq hodd hq hd hcd hs, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi' : i < w.length := by
      rw [(sweepIdxZ_perm _ _ w).mem_iff, List.mem_range] at hi
      exact hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
  · simp

/-- Under Thomas and Williams, Thm 6.3, the sweep permutes the admissible words of
    each Order. -/
theorem sweepQ_bijOn (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) (n : ℕ) :
    Set.BijOn (sweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) := by
  obtain ⟨c, d, hd, hcd⟩ := exists_weightsQ hq n
  have hmaps : Set.MapsTo (sweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) :=
    fun s hs => sweepQ_mem_admSetQ hodd (by omega) hs
  refine ((admSetQ q n).finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).mp ?_
  intro s hs s' hs' heq
  have hs1 : s ∈ admSetQ q n := hs
  have hs1' : s' ∈ admSetQ q n := hs'
  obtain ⟨w, rfl⟩ := exists_eq_append_falseQ hq hs1
  obtain ⟨w', rfl⟩ := exists_eq_append_falseQ hq hs1'
  rw [sweepQ_eq_sweepZ hodd hq hd hcd hs1, sweepQ_eq_sweepZ hodd hq hd hcd hs1'] at heq
  have hZ := List.append_cancel_right heq
  have hl1 := admissibleQ_length (by omega) ((mem_admSetQ (by omega) _ _).mp hs1).1
  have hl2 := admissibleQ_length (by omega) ((mem_admSetQ (by omega) _ _).mp hs1').1
  rw [((mem_admSetQ (by omega) _ _).mp hs1).2] at hl1
  rw [((mem_admSetQ (by omega) _ _).mp hs1').2] at hl2
  have hlen : w.length = w'.length := by
    simp only [List.length_append, List.length_singleton] at hl1 hl2
    omega
  have hw := dropLast_mem_dyckSetQ hodd hq hd hcd hs1
  have hw' := dropLast_mem_dyckSetQ hodd hq hd hcd hs1'
  rw [← hlen] at hw'
  have hcw := dyckSet_subset_contentSet _ _ _ _ hw
  have hcw' := dyckSet_subset_contentSet _ _ _ _ hw'
  rw [(hTW (c - d) (-d) n (w.length - n)).injOn hcw hcw' hZ]

/-! ## 6. Record Orders -/

/-- Upper record Order: p2Q(n)/n is below p2Q(a)/a for every 1 ≤ a < n.
    Orders 0 and 1 qualify: there is no such a. -/
def UpperRecordQ (q n : ℕ) : Prop :=
  ∀ a, 1 ≤ a → a < n → a * p2Q q n < n * p2Q q a

/-- Lower record Order: (p2Q(n) - 1)/n is above (p2Q(a) - 1)/a for every 1 ≤ a < n.
    Orders 0 and 1 qualify: there is no such a. -/
def LowerRecordQ (q n : ℕ) : Prop :=
  ∀ a, 1 ≤ a → a < n → n * (p2Q q a - 1) < a * (p2Q q n - 1)

/-- p2Q(a + b) ≤ p2Q(a) + p2Q(b). -/
theorem p2Q_add_le (hq : 3 ≤ q) (a b : ℕ) : p2Q q (a + b) ≤ p2Q q a + p2Q q b := by
  rw [← q_pow_lt_two_pow_iff hq, pow_add, pow_add]
  exact Nat.mul_lt_mul'' (p2Q_spec hq a) (p2Q_spec hq b)

/-- p2Q(a) + p2Q(b) ≤ p2Q(a + b) + 1. -/
theorem p2Q_add_le_succ (hq : 3 ≤ q) (a b : ℕ) : p2Q q a + p2Q q b ≤ p2Q q (a + b) + 1 := by
  have h1 : 2 ^ (p2Q q a - 1) * 2 ^ (p2Q q b - 1) ≤ q ^ a * q ^ b :=
    Nat.mul_le_mul (p2Q_spec_lower hq a) (p2Q_spec_lower hq b)
  rw [← pow_add, ← pow_add] at h1
  have h2 : 2 ^ (p2Q q a - 1 + (p2Q q b - 1)) < 2 ^ p2Q q (a + b) :=
    lt_of_le_of_lt h1 (p2Q_spec hq (a + b))
  have h3 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  have ha := one_le_p2Q q a
  have hb := one_le_p2Q q b
  omega

/-- Block factor of Order o: q^o / 2^p2Q(o), the level change across a block. -/
def blockFactorQ (q o : ℕ) : ℚ := (q : ℚ) ^ o / 2 ^ p2Q q o

/-- Block factors compare like the cross products q^a 2^p2Q(c) and q^c 2^p2Q(a). -/
theorem blockFactorQ_lt_iff (q a c : ℕ) :
    blockFactorQ q a < blockFactorQ q c ↔ q ^ a * 2 ^ p2Q q c < q ^ c * 2 ^ p2Q q a := by
  unfold blockFactorQ
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

/-- The block factor falls from a to a + b exactly when p2Q is additive at (a, b). -/
theorem blockFactorQ_add_lt_iff (hq : 3 ≤ q) (a b : ℕ) :
    blockFactorQ q (a + b) < blockFactorQ q a ↔ p2Q q (a + b) = p2Q q a + p2Q q b := by
  have hle := p2Q_add_le hq a b
  rw [blockFactorQ_lt_iff, pow_add, mul_assoc, Nat.mul_lt_mul_left (pow_pos (by omega) _),
    q_pow_mul_lt_iff hq]
  omega

/-- For b ≥ 1 the block factor rises from a to a + b exactly when p2Q(a + b) is one
    less than p2Q(a) + p2Q(b). -/
theorem blockFactorQ_lt_add_iff (hodd : Odd q) (hq : 3 ≤ q) (a : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    blockFactorQ q a < blockFactorQ q (a + b) ↔ p2Q q (a + b) + 1 = p2Q q a + p2Q q b := by
  have hle := p2Q_add_le_succ hq a b
  rw [blockFactorQ_lt_iff, pow_add, mul_assoc, Nat.mul_lt_mul_left (pow_pos (by omega) _),
    lt_q_pow_mul_iff hodd hq hb]
  omega

/-- Lower record Orders: p2Q(n) = p2Q(a) + p2Q(n - a) at every split. -/
theorem lowerRecordQ_iff_add (hq : 3 ≤ q) (n : ℕ) :
    LowerRecordQ q n ↔ ∀ a, 1 ≤ a → a < n → p2Q q n = p2Q q a + p2Q q (n - a) := by
  constructor
  · intro hR a ha1 han
    obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have h1 := hR a ha1 han
    have h2 := hR b (by omega) (by omega)
    have hle := p2Q_add_le hq a b
    have hA := one_le_p2Q q a
    have hB := one_le_p2Q q b
    by_contra hne
    have hP : p2Q q (a + b) - 1 ≤ (p2Q q a - 1) + (p2Q q b - 1) := by
      omega
    have h3 := Nat.mul_le_mul_left (a + b) hP
    nlinarith
  · intro hB a ha1 han
    obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
    have h1 := hB a ha1 han
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : (p2Q q a - 1) * b < a * p2Q q b := p2Q_sub_one_mul_lt hq ha1
    have hA := one_le_p2Q q a
    have hP : p2Q q (a + b) - 1 = (p2Q q a - 1) + p2Q q b := by
      omega
    rw [hP]
    nlinarith

/-- Upper record Orders: p2Q(n) + 1 = p2Q(a) + p2Q(n - a) at every split. -/
theorem upperRecordQ_iff_add (hq : 3 ≤ q) (n : ℕ) :
    UpperRecordQ q n ↔ ∀ a, 1 ≤ a → a < n → p2Q q n + 1 = p2Q q a + p2Q q (n - a) := by
  constructor
  · intro hR a ha1 han
    obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have h1 := hR a ha1 han
    have h2 := hR b (by omega) (by omega)
    have hle := p2Q_add_le_succ hq a b
    by_contra hne
    have hP : p2Q q a + p2Q q b ≤ p2Q q (a + b) := by
      omega
    have h3 := Nat.mul_le_mul_left (a + b) hP
    nlinarith
  · intro hB a ha1 han
    obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
    have h1 := hB a ha1 han
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : (p2Q q b - 1) * a < b * p2Q q a := p2Q_sub_one_mul_lt hq (by omega)
    have hB1 := one_le_p2Q q b
    have hP : p2Q q (a + b) = p2Q q a + (p2Q q b - 1) := by
      omega
    rw [hP]
    nlinarith

/-- Lower record Orders are the Orders whose block factor is below every earlier one. -/
theorem lowerRecordQ_iff_blockFactorQ (hq : 3 ≤ q) (n : ℕ) :
    LowerRecordQ q n ↔ ∀ a, 1 ≤ a → a < n → blockFactorQ q n < blockFactorQ q a := by
  rw [lowerRecordQ_iff_add hq]
  constructor
  · intro h a ha1 han
    have hb := blockFactorQ_add_lt_iff hq a (n - a)
    rw [Nat.add_sub_of_le han.le] at hb
    exact hb.mpr (h a ha1 han)
  · intro h a ha1 han
    have hb := blockFactorQ_add_lt_iff hq a (n - a)
    rw [Nat.add_sub_of_le han.le] at hb
    exact hb.mp (h a ha1 han)

/-- Upper record Orders are the Orders whose block factor is above every earlier one. -/
theorem upperRecordQ_iff_blockFactorQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    UpperRecordQ q n ↔ ∀ a, 1 ≤ a → a < n → blockFactorQ q a < blockFactorQ q n := by
  rw [upperRecordQ_iff_add hq]
  constructor
  · intro h a ha1 han
    have hb := blockFactorQ_lt_add_iff hodd hq a (b := n - a) (by omega)
    rw [Nat.add_sub_of_le han.le] at hb
    exact hb.mpr (h a ha1 han)
  · intro h a ha1 han
    have hb := blockFactorQ_lt_add_iff hodd hq a (b := n - a) (by omega)
    rw [Nat.add_sub_of_le han.le] at hb
    exact hb.mp (h a ha1 han)

/-! ## 7. The start sweep -/

/-- Step indices of s, sorted by starting level, lowest first. -/
def startIdxQ (q : ℕ) (s : List Bool) : List ℕ :=
  (List.range s.length).mergeSort (fun i k => decide (lvlQ q s i ≤ lvlQ q s k))

/-- Start sweep: the steps of s in the order of `startIdxQ`. -/
def startSweepQ (q : ℕ) (s : List Bool) : List Bool :=
  (startIdxQ q s).map (fun i => s.getD i false)

theorem startIdxQ_perm (q : ℕ) (s : List Bool) : (startIdxQ q s).Perm (List.range s.length) :=
  List.mergeSort_perm _ _

theorem startIdxQ_nodup (q : ℕ) (s : List Bool) : (startIdxQ q s).Nodup :=
  (startIdxQ_perm q s).nodup_iff.mpr List.nodup_range

theorem mem_startIdxQ {s : List Bool} {i : ℕ} : i ∈ startIdxQ q s ↔ i < s.length := by
  rw [(startIdxQ_perm q s).mem_iff, List.mem_range]

theorem length_startIdxQ (q : ℕ) (s : List Bool) : (startIdxQ q s).length = s.length := by
  rw [(startIdxQ_perm q s).length_eq, List.length_range]

theorem startIdxQ_pairwise (q : ℕ) (s : List Bool) :
    (startIdxQ q s).Pairwise (fun i k => lvlQ q s i ≤ lvlQ q s k) := by
  have h := List.pairwise_mergeSort
    (le := fun i k => decide (lvlQ q s i ≤ lvlQ q s k))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc)
    (fun a b => by
      rcases le_total (lvlQ q s a) (lvlQ q s b) with h | h
      · simp [h]
      · simp [h])
    (List.range s.length)
  exact h.imp (fun hab => by simpa using hab)

/-- The start sweep permutes the steps. -/
theorem startSweepQ_perm (q : ℕ) (s : List Bool) : (startSweepQ q s).Perm s := by
  have h := (startIdxQ_perm q s).map (fun i => s.getD i false)
  rw [map_getD_range] at h
  exact h

theorem length_startSweepQ (q : ℕ) (s : List Bool) : (startSweepQ q s).length = s.length :=
  (startSweepQ_perm q s).length_eq

theorem seqProductQ_startSweepQ (q : ℕ) (s : List Bool) :
    seqProductQ q (startSweepQ q s) = seqProductQ q s :=
  ((startSweepQ_perm q s).map (factorQ q)).prod_eq

/-! ### Levels -/

theorem factorQ_pos (hq0 : 0 < q) (b : Bool) : 0 < factorQ q b := by
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  unfold factorQ
  split_ifs
  · exact div_pos hq0' (by norm_num)
  · norm_num

theorem seqProductQ_pos (hq0 : 0 < q) (s : List Bool) : 0 < seqProductQ q s := by
  induction s with
  | nil =>
    simp [seqProductQ]
  | cons b t ih =>
    have hcons : seqProductQ q (b :: t) = factorQ q b * seqProductQ q t := by
      simp [seqProductQ]
    rw [hcons]
    exact mul_pos (factorQ_pos hq0 b) ih

theorem lvlQ_pos (hq0 : 0 < q) (s : List Bool) (j : ℕ) : 0 < lvlQ q s j :=
  seqProductQ_pos hq0 _

theorem lvlQ_length (q : ℕ) (s : List Bool) : lvlQ q s s.length = seqProductQ q s := by
  unfold lvlQ
  rw [List.take_length]

/-- Levels compare like the cross products of their powers of q and 2. -/
theorem lvlQ_lt_iff (q : ℕ) {s : List Bool} {i j : ℕ} (hi : i ≤ s.length)
    (hj : j ≤ s.length) :
    lvlQ q s i < lvlQ q s j ↔
      q ^ order (s.take i) * 2 ^ j < q ^ order (s.take j) * 2 ^ i := by
  have h1 := lvlQ_mul_pow q hi
  have h2 := lvlQ_mul_pow q hj
  have hp1 : (0 : ℚ) < 2 ^ i := by positivity
  have hp2 : (0 : ℚ) < 2 ^ j := by positivity
  have hcast : (q ^ order (s.take i) * 2 ^ j < q ^ order (s.take j) * 2 ^ i) ↔
      ((q : ℚ) ^ order (s.take i) * 2 ^ j < q ^ order (s.take j) * 2 ^ i) := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  rw [hcast, ← h1, ← h2]
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h (mul_pos hp1 hp2)
    nlinarith
  · intro h
    by_contra hle
    push Not at hle
    have := mul_le_mul_of_nonneg_right hle (le_of_lt (mul_pos hp1 hp2))
    nlinarith

/-- The steps u ≤ i < v multiply the level at u to the level at v. -/
theorem lvlQ_mul_prod_Ico (q : ℕ) (s : List Bool) {u v : ℕ} (huv : u ≤ v)
    (hv : v ≤ s.length) :
    lvlQ q s u * ∏ i ∈ Finset.Ico u v, factorQ q (s.getD i false) = lvlQ q s v := by
  induction v, huv using Nat.le_induction with
  | base =>
    simp
  | succ v huv ih =>
    have hlt : v < s.length := by omega
    have hget : s[v]? = some (s.getD v false) := by
      simp [List.getD_eq_getElem?_getD, hlt]
    rw [Finset.prod_Ico_succ_top huv, ← mul_assoc, ih (by omega), lvlQ_succ q s hget]

/-! ### Prefixes of the start sweep -/

/-- A set of steps that start below all other steps is a prefix of the start sweep. -/
theorem toFinset_take_startIdxQ {s : List Bool} {T : Finset ℕ}
    (hT : ∀ i ∈ T, i < s.length)
    (hlow : ∀ i ∈ T, ∀ k, k < s.length → k ∉ T → lvlQ q s i < lvlQ q s k) :
    ((startIdxQ q s).take T.card).toFinset = T := by
  set l := startIdxQ q s with hl
  have hnd : l.Nodup := startIdxQ_nodup q s
  have hpw := startIdxQ_pairwise q s
  have hlen : l.length = s.length := length_startIdxQ q s
  have hTsub : T ⊆ Finset.range s.length := fun i hi => Finset.mem_range.mpr (hT i hi)
  have hcardle : T.card ≤ s.length := by
    have := Finset.card_le_card hTsub
    rwa [Finset.card_range] at this
  have hsplit : (l.take T.card ++ l.drop T.card).Nodup := by
    rw [List.take_append_drop]
    exact hnd
  obtain ⟨hnd1, _, hdisj⟩ := List.nodup_append.mp hsplit
  have hcard : (l.take T.card).toFinset.card = T.card := by
    rw [List.toFinset_card_of_nodup hnd1, List.length_take]
    omega
  have hsub : (l.take T.card).toFinset ⊆ T := by
    intro i hi
    rw [List.mem_toFinset] at hi
    by_contra hiT
    have hex : ∃ k ∈ T, k ∉ (l.take T.card).toFinset := by
      by_contra hall
      push Not at hall
      have hsubT : T ⊆ (l.take T.card).toFinset := hall
      have heq := Finset.eq_of_subset_of_card_le hsubT (le_of_eq hcard)
      exact hiT (heq ▸ List.mem_toFinset.mpr hi)
    obtain ⟨k, hkT, hkn⟩ := hex
    rw [List.mem_toFinset] at hkn
    have hkl : k ∈ l := mem_startIdxQ.mpr (hT k hkT)
    rw [← List.take_append_drop T.card l, List.mem_append] at hkl
    have hkd : k ∈ l.drop T.card := hkl.resolve_left hkn
    have hle := hpw.rel_of_mem_take_of_mem_drop hi hkd
    have hiL : i < s.length := mem_startIdxQ.mp (List.mem_of_mem_take hi)
    have hlt := hlow k hkT i hiL hiT
    linarith
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

/-- The level of a prefix of the start sweep: the product over its set of steps. -/
theorem seqProductQ_take_startSweepQ {s : List Bool} {T : Finset ℕ}
    (hT : ∀ i ∈ T, i < s.length)
    (hlow : ∀ i ∈ T, ∀ k, k < s.length → k ∉ T → lvlQ q s i < lvlQ q s k) :
    seqProductQ q ((startSweepQ q s).take T.card) = ∏ i ∈ T, factorQ q (s.getD i false) := by
  have hnd1 : ((startIdxQ q s).take T.card).Nodup :=
    (startIdxQ_nodup q s).sublist (List.take_sublist _ _)
  have hfin := toFinset_take_startIdxQ hT hlow
  conv_rhs => rw [← hfin]
  rw [List.prod_toFinset _ hnd1]
  unfold startSweepQ seqProductQ
  rw [← List.map_take, List.map_map]
  rfl

/-- Every prefix of the start sweep is the set of steps that start below the others. -/
theorem exists_startSweepQ_prefix_set (hodd : Odd q) (s : List Bool) {m : ℕ} (hm : m ≤ s.length) :
    ∃ T : Finset ℕ, T.card = m ∧ (∀ i ∈ T, i < s.length) ∧
      (∀ i ∈ T, ∀ k, k < s.length → k ∉ T → lvlQ q s i < lvlQ q s k) ∧
      seqProductQ q ((startSweepQ q s).take m) = ∏ i ∈ T, factorQ q (s.getD i false) := by
  set l := startIdxQ q s with hl
  have hnd : l.Nodup := startIdxQ_nodup q s
  have hpw := startIdxQ_pairwise q s
  have hlen : l.length = s.length := length_startIdxQ q s
  have hsplit : (l.take m ++ l.drop m).Nodup := by
    rw [List.take_append_drop]
    exact hnd
  obtain ⟨hnd1, _, hdisj⟩ := List.nodup_append.mp hsplit
  have hcard : (l.take m).toFinset.card = m := by
    rw [List.toFinset_card_of_nodup hnd1, List.length_take]
    omega
  have hT : ∀ i ∈ (l.take m).toFinset, i < s.length := by
    intro i hi
    rw [List.mem_toFinset] at hi
    exact mem_startIdxQ.mp (List.mem_of_mem_take hi)
  have hlow : ∀ i ∈ (l.take m).toFinset, ∀ k, k < s.length → k ∉ (l.take m).toFinset →
      lvlQ q s i < lvlQ q s k := by
    intro i hi k hk hkT
    rw [List.mem_toFinset] at hi hkT
    have hkl : k ∈ l := mem_startIdxQ.mpr hk
    rw [← List.take_append_drop m l, List.mem_append] at hkl
    have hkd : k ∈ l.drop m := hkl.resolve_left hkT
    have hle := hpw.rel_of_mem_take_of_mem_drop hi hkd
    have hik : i ≠ k := hdisj i hi k hkd
    have hi' := mem_startIdxQ.mp (List.mem_of_mem_take hi)
    exact lt_of_le_of_ne hle (lvlQ_ne_of_ne hodd (by omega) (by omega) hik)
  refine ⟨(l.take m).toFinset, hcard, hT, hlow, ?_⟩
  have h := seqProductQ_take_startSweepQ hT hlow
  rwa [hcard] at h

/-! ### The word of n odd steps followed by halvings -/

theorem lt_p2Q (hq : 3 ≤ q) (n : ℕ) : n < p2Q q n := by
  have h1 : 2 ^ n ≤ q ^ n := Nat.pow_le_pow_left (by omega) n
  have h2 := p2Q_spec hq n
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h1 h2)

/-- p2Q(a) + c ≤ p2Q(a + c). -/
theorem p2Q_add_ge (hq : 3 ≤ q) (a c : ℕ) : p2Q q a + c ≤ p2Q q (a + c) := by
  have h1 : 2 ^ (p2Q q a - 1) * 2 ^ c ≤ q ^ a * q ^ c :=
    Nat.mul_le_mul (p2Q_spec_lower hq a) (Nat.pow_le_pow_left (by omega) c)
  rw [← pow_add, ← pow_add] at h1
  have h2 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp
    (lt_of_le_of_lt h1 (p2Q_spec hq (a + c)))
  have hp := one_le_p2Q q a
  omega

/-- n odd steps, then halvings up to the length p2Q(n). -/
def upDownQ (q n : ℕ) : List Bool :=
  List.replicate n true ++ List.replicate (p2Q q n - n) false

theorem length_upDownQ (hq : 3 ≤ q) (n : ℕ) : (upDownQ q n).length = p2Q q n := by
  have := lt_p2Q hq n
  simp only [upDownQ, List.length_append, List.length_replicate]
  omega

theorem order_take_upDownQ (q n j : ℕ) : order ((upDownQ q n).take j) = min j n := by
  unfold upDownQ order
  rw [List.take_append, List.filter_append, List.length_append, List.take_replicate,
    List.take_replicate, List.length_replicate]
  simp

theorem order_upDownQ (hq : 3 ≤ q) (n : ℕ) : order (upDownQ q n) = n := by
  have h := order_take_upDownQ q n (upDownQ q n).length
  rw [List.take_length, length_upDownQ hq] at h
  have := lt_p2Q hq n
  omega

/-- The word of n odd steps followed by halvings is admissible. -/
theorem upDownQ_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    upDownQ q n ∈ admSetQ q n := by
  rw [mem_admSetQ (by omega)]
  have hlen := length_upDownQ hq n
  refine ⟨⟨?_, ?_⟩, order_upDownQ hq n⟩
  · intro m hm1 hmL
    rw [hlen] at hmL
    have h0 : lvlQ q (upDownQ q n) 0 < lvlQ q (upDownQ q n) m := by
      rw [lvlQ_lt_iff q (by omega) (by omega), order_take_upDownQ, order_take_upDownQ]
      simp only [Nat.zero_min, pow_zero, one_mul, mul_one]
      rcases Nat.le_total m n with hmn | hnm
      · rw [min_eq_left hmn]
        exact Nat.pow_lt_pow_left (by omega) (by omega)
      · rw [min_eq_right hnm]
        have hn1 : 1 ≤ n := by
          by_contra h0
          have hn0 : n = 0 := by omega
          rw [hn0] at hmL
          simp [p2Q] at hmL
          omega
        exact (two_pow_lt_q_pow_iff hodd hq hn1).mpr hmL
    rw [lvlQ_zero] at h0
    exact h0
  · have h := seqProductQ_mul_pow q (upDownQ q n)
    rw [hlen, order_upDownQ hq] at h
    have hspec : (q : ℚ) ^ n < 2 ^ p2Q q n := by exact_mod_cast p2Q_spec hq n
    have hpos : (0 : ℚ) < 2 ^ p2Q q n := by positivity
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_right hge hpos.le
    linarith

/-- At an Order that is no upper record, the start sweep of the word of n odd steps
    followed by halvings is not admissible. -/
theorem startSweepQ_upDownQ_not_mem (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : ¬UpperRecordQ q n) : startSweepQ q (upDownQ q n) ∉ admSetQ q n := by
  rw [upperRecordQ_iff_add hq] at hR
  push Not at hR
  obtain ⟨a, ha1, han, hne⟩ := hR
  obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
  rw [Nat.add_sub_cancel_left] at hne
  have hb1 : 1 ≤ b := by omega
  have hadd : p2Q q (a + b) = p2Q q a + p2Q q b := by
    have h1 := p2Q_add_le hq a b
    have h2 := p2Q_add_le_succ hq a b
    omega
  have hq0 : 0 < q := by omega
  have hqpos : ∀ e : ℕ, 0 < q ^ e := fun e => pow_pos hq0 e
  set w := upDownQ q (a + b) with hw
  have hlen : w.length = p2Q q a + p2Q q b := by
    rw [hw, length_upDownQ hq, hadd]
  have hbp := lt_p2Q hq b
  have hap := lt_p2Q hq a
  set T : Finset ℕ := Finset.range b ∪ Finset.Ico (b + p2Q q a) w.length with hTdef
  have hdisj : Disjoint (Finset.range b) (Finset.Ico (b + p2Q q a) w.length) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico] at hi'
    omega
  have hcard : T.card = p2Q q b := by
    rw [hTdef, Finset.card_union_of_disjoint hdisj, Finset.card_range, Nat.card_Ico, hlen]
    omega
  have hmem : ∀ i, i ∈ T ↔ i < b ∨ (b + p2Q q a ≤ i ∧ i < w.length) := by
    intro i
    rw [hTdef, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  have hT : ∀ i ∈ T, i < w.length := by
    intro i hi
    rcases (hmem i).mp hi with h | h
    · omega
    · exact h.2
  have hlow : ∀ i ∈ T, ∀ k, k < w.length → k ∉ T → lvlQ q w i < lvlQ q w k := by
    intro i hi k hk hkT
    rw [hmem] at hkT
    push Not at hkT
    obtain ⟨hkb, hk2⟩ := hkT
    have hkj : k < b + p2Q q a := by
      by_contra h
      have := hk2 (by omega)
      omega
    rw [lvlQ_lt_iff q (hT i hi).le hk.le, hw, order_take_upDownQ, order_take_upDownQ]
    rcases (hmem i).mp hi with hib | ⟨hij, hiL⟩
    · rw [min_eq_left (by omega : i ≤ a + b)]
      obtain ⟨e, he⟩ : ∃ e, min k (a + b) = i + e := ⟨min k (a + b) - i, by omega⟩
      have he1 : 1 ≤ e := by omega
      rw [he, pow_add, mul_assoc, Nat.mul_lt_mul_left (hqpos i),
        lt_q_pow_mul_iff hodd hq he1]
      rcases Nat.le_total k (a + b) with hkn | hnk
      · have := lt_p2Q hq e
        omega
      · have hge := p2Q_add_ge hq a (b - i)
        have hae : a + (b - i) = e := by omega
        rw [hae] at hge
        omega
    · rw [min_eq_right (by omega : a + b ≤ i)]
      obtain ⟨e, he⟩ : ∃ e, a + b = min k (a + b) + e := ⟨a + b - min k (a + b), by omega⟩
      conv_lhs => rw [he]
      rw [pow_add, mul_assoc, Nat.mul_lt_mul_left (hqpos _), q_pow_mul_lt_iff hq]
      rcases Nat.le_total k (a + b) with hkn | hnk
      · have hge := p2Q_add_ge hq e (a - e)
        have hae : e + (a - e) = a := by omega
        rw [hae] at hge
        omega
      · have he0 : e = 0 := by omega
        rw [he0]
        simp only [p2Q, pow_zero, Nat.log_one_right]
        omega
  have hprod : (∏ i ∈ T, factorQ q (w.getD i false)) < 1 := by
    have h1 := lvlQ_mul_prod_Ico q w (Nat.zero_le b) (by omega)
    have h2 := lvlQ_mul_prod_Ico q w (u := b + p2Q q a) (v := w.length) (by omega) le_rfl
    rw [lvlQ_zero, one_mul, ← Finset.range_eq_Ico] at h1
    have e1 := lvlQ_mul_pow q (s := w) (j := b) (by omega)
    have e2 := lvlQ_mul_pow q (s := w) (j := w.length) le_rfl
    have e3 := lvlQ_mul_pow q (s := w) (j := b + p2Q q a) (by omega)
    rw [hw, order_take_upDownQ, ← hw] at e1 e2 e3
    rw [min_eq_left (by omega : b ≤ a + b)] at e1
    rw [min_eq_right (by omega : a + b ≤ w.length)] at e2
    rw [min_eq_right (by omega : a + b ≤ b + p2Q q a)] at e3
    have hsplit : (2 : ℚ) ^ b * 2 ^ w.length = 2 ^ (b + p2Q q a) * 2 ^ p2Q q b := by
      rw [← pow_add, ← pow_add, hlen]
      congr 1
      omega
    have hspec : (q : ℚ) ^ b < 2 ^ p2Q q b := by exact_mod_cast p2Q_spec hq b
    have hqn : (0 : ℚ) < (q : ℚ) ^ (a + b) := by positivity
    have hj0 : 0 < lvlQ q w (b + p2Q q a) := lvlQ_pos hq0 w _
    have hlt : lvlQ q w b * lvlQ q w w.length < lvlQ q w (b + p2Q q a) := by
      have hC : (0 : ℚ) < 2 ^ b * 2 ^ w.length := by positivity
      apply lt_of_mul_lt_mul_right _ hC.le
      calc lvlQ q w b * lvlQ q w w.length * (2 ^ b * 2 ^ w.length)
          = lvlQ q w b * 2 ^ b * (lvlQ q w w.length * 2 ^ w.length) := by ring
        _ = (q : ℚ) ^ (a + b) * (q : ℚ) ^ b := by rw [e1, e2, mul_comm]
        _ < (q : ℚ) ^ (a + b) * 2 ^ p2Q q b := mul_lt_mul_of_pos_left hspec hqn
        _ = lvlQ q w (b + p2Q q a) * 2 ^ (b + p2Q q a) * 2 ^ p2Q q b := by rw [e3]
        _ = lvlQ q w (b + p2Q q a) * (2 ^ b * 2 ^ w.length) := by rw [hsplit, mul_assoc]
    rw [hTdef, Finset.prod_union hdisj, h1]
    apply lt_of_mul_lt_mul_left _ hj0.le
    rw [mul_one]
    calc lvlQ q w (b + p2Q q a) * (lvlQ q w b *
          ∏ i ∈ Finset.Ico (b + p2Q q a) w.length, factorQ q (w.getD i false))
        = lvlQ q w b * (lvlQ q w (b + p2Q q a) *
          ∏ i ∈ Finset.Ico (b + p2Q q a) w.length, factorQ q (w.getD i false)) := by ring
      _ = lvlQ q w b * lvlQ q w w.length := by rw [h2]
      _ < lvlQ q w (b + p2Q q a) := hlt
  intro hin
  have hA := ((mem_admSetQ (by omega) _ _).mp hin).1
  have hpL : p2Q q b < (startSweepQ q w).length := by
    rw [length_startSweepQ, hlen]
    omega
  have hgt := hA.prefix_gt (p2Q q b) (one_le_p2Q q b) hpL
  rw [← hcard, seqProductQ_take_startSweepQ hT hlow] at hgt
  linarith

/-! ## 8. The start sweep as the sweep of a flipped word -/

/-! ### The flip around a point -/

/-- The two halves of s around the point k, each reversed. -/
def peakFlip (s : List Bool) (k : ℕ) : List Bool := (s.take k).reverse ++ (s.drop k).reverse

/-- Step i of `peakFlip s k` is step `flipIdx s.length k i` of s. -/
def flipIdx (L k i : ℕ) : ℕ := if i < k then k - 1 - i else L + k - 1 - i

theorem flipIdx_lt {L k i : ℕ} (hk : k ≤ L) (hi : i < L) : flipIdx L k i < L := by
  unfold flipIdx
  split_ifs
  · omega
  · omega

theorem flipIdx_flipIdx {L k i : ℕ} (hi : i < L) :
    flipIdx L k (flipIdx L k i) = i := by
  unfold flipIdx
  split_ifs
  · omega
  · omega
  · omega
  · omega

theorem peakFlip_perm (s : List Bool) (k : ℕ) : (peakFlip s k).Perm s := by
  have h := ((s.take k).reverse_perm).append ((s.drop k).reverse_perm)
  rw [List.take_append_drop] at h
  exact h

theorem length_peakFlip (s : List Bool) (k : ℕ) : (peakFlip s k).length = s.length :=
  (peakFlip_perm s k).length_eq

theorem seqProductQ_perm (q : ℕ) {l l' : List Bool} (h : l.Perm l') :
    seqProductQ q l = seqProductQ q l' :=
  (h.map (factorQ q)).prod_eq

theorem order_perm {l l' : List Bool} (h : l.Perm l') : order l = order l' :=
  (h.filter id).length_eq

theorem getD_peakFlip {s : List Bool} {k i : ℕ} (hk : k ≤ s.length) (hi : i < s.length) :
    (peakFlip s k).getD i false = s.getD (flipIdx s.length k i) false := by
  unfold peakFlip flipIdx
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hlt : (s.take k).reverse.length = k := by
    simp [hk]
  have hl : (s.take k).length = k := by
    simp [hk]
  split_ifs with hik
  · have hlt' : k - 1 - i < k := by omega
    rw [List.getElem?_append_left (by omega), List.getElem?_reverse (by omega),
      List.getElem?_take, hl]
    simp only [hlt', ↓reduceIte]
  · have hid : i - k < (s.drop k).length := by
      rw [List.length_drop]
      omega
    rw [List.getElem?_append_right (by omega), hlt, List.getElem?_reverse hid,
      List.getElem?_drop, List.length_drop]
    congr 2
    omega

/-- The steps u ≤ i < v multiply the level at u to the level at v. -/
theorem lvlQ_mul_seqProductQ_drop (q : ℕ) (s : List Bool) {u v : ℕ} (huv : u ≤ v) :
    lvlQ q s u * seqProductQ q ((s.take v).drop u) = lvlQ q s v := by
  unfold lvlQ
  rw [← seqProductQ_append]
  have h : s.take u = (s.take v).take u := by
    rw [List.take_take, min_eq_left huv]
  rw [h, List.take_append_drop]

/-- After m ≤ k steps the flip is at the level of the point k over that of k - m. -/
theorem lvlQ_peakFlip_le {s : List Bool} {k m : ℕ} (hk : k ≤ s.length) (hm : m ≤ k) :
    lvlQ q (peakFlip s k) m * lvlQ q s (k - m) = lvlQ q s k := by
  have hl : (s.take k).length = k := by
    simp [hk]
  have htake : (peakFlip s k).take m = ((s.take k).drop (k - m)).reverse := by
    unfold peakFlip
    rw [List.take_append_of_le_length (by simp [hk, hm]), List.take_reverse, hl]
  have h := lvlQ_mul_seqProductQ_drop q s (Nat.sub_le k m)
  rw [← h, mul_comm]
  congr 1
  unfold lvlQ
  rw [htake]
  exact seqProductQ_perm q (List.reverse_perm _)

/-- After m ≥ k steps the flip is at the level of the point k times that of the whole
    word, over that of the point length + k - m. -/
theorem lvlQ_peakFlip_ge {s : List Bool} {k m : ℕ} (hk : k ≤ s.length) (hkm : k ≤ m)
    (hm : m ≤ s.length) :
    lvlQ q (peakFlip s k) m * lvlQ q s (s.length + k - m) =
      lvlQ q s k * lvlQ q s s.length := by
  have hl : (s.take k).reverse.length = k := by
    simp [hk]
  have htake : (peakFlip s k).take m =
      (s.take k).reverse ++ (s.drop (s.length + k - m)).reverse := by
    unfold peakFlip
    rw [List.take_append, List.take_of_length_le (by omega), hl, List.take_reverse,
      List.drop_drop, List.length_drop]
    congr 3
    omega
  have hsplit : lvlQ q s (s.length + k - m) * seqProductQ q (s.drop (s.length + k - m)) =
      lvlQ q s s.length := by
    unfold lvlQ
    rw [← seqProductQ_append, List.take_append_drop, List.take_length]
  have hfl : lvlQ q (peakFlip s k) m =
      lvlQ q s k * seqProductQ q (s.drop (s.length + k - m)) := by
    unfold lvlQ
    rw [htake, seqProductQ_append, seqProductQ_perm q (List.reverse_perm _),
      seqProductQ_perm q (List.reverse_perm (s.drop (s.length + k - m)))]
  rw [hfl, ← hsplit]
  ring

/-! ### The start sweep as the sweep of the flip -/

/-- From G Y = F X and G < F: X < Y. -/
theorem lt_of_mul_eq_mul {F G X Y : ℚ} (hG : 0 < G) (hX : 0 < X) (h : G * Y = F * X)
    (hlt : G < F) : X < Y := by
  by_contra hle
  push Not at hle
  have h1 : G * Y ≤ G * X := mul_le_mul_of_nonneg_left hle hG.le
  have h2 : G * X < F * X := mul_lt_mul_of_pos_right hlt hX
  linarith

theorem perm_map_flipIdx {L k : ℕ} (hk : k ≤ L) :
    ((List.range L).map (flipIdx L k)).Perm (List.range L) := by
  have hnd : ((List.range L).map (flipIdx L k)).Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro x hx y hy hxy
    rw [List.mem_range] at hx hy
    rw [← flipIdx_flipIdx (k := k) hx, ← flipIdx_flipIdx (k := k) hy, hxy]
  rw [List.perm_ext_iff_of_nodup hnd List.nodup_range]
  intro a
  rw [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact flipIdx_lt hk (List.mem_range.mp hi)
  · intro ha
    exact ⟨flipIdx L k a, List.mem_range.mpr (flipIdx_lt hk ha), flipIdx_flipIdx ha⟩

/-- The start sweep of s is the sweep of its flip around k, when across k the order of
    two levels does not change with a factor of the level of the whole word. -/
theorem startSweepQ_eq_sweepQ_peakFlip (hodd : Odd q) (hq0 : 0 < q) {s : List Bool} {k : ℕ}
    (hk : k ≤ s.length)
    (h1 : ∀ i j, i < k → k ≤ j → j < s.length →
      lvlQ q s i * lvlQ q s s.length < lvlQ q s j → lvlQ q s i < lvlQ q s j)
    (h2 : ∀ i j, i < k → k ≤ j → j < s.length →
      lvlQ q s j < lvlQ q s i * lvlQ q s s.length → lvlQ q s j < lvlQ q s i) :
    startSweepQ q s = sweepQ q (peakFlip s k) := by
  set fl := peakFlip s k with hfl
  have hlen : fl.length = s.length := length_peakFlip s k
  have hpos : ∀ (t : List Bool) (j : ℕ), 0 < lvlQ q t j := fun t j => lvlQ_pos hq0 t j
  have hend : ∀ i, i < s.length → lvlQ q fl (i + 1) * lvlQ q s (flipIdx s.length k i) =
      if i < k then lvlQ q s k else lvlQ q s k * lvlQ q s s.length := by
    intro i hi
    unfold flipIdx
    split_ifs with hik
    · have h := lvlQ_peakFlip_le (q := q) hk (m := i + 1) (by omega)
      have hsub : k - (i + 1) = k - 1 - i := by omega
      rw [hsub] at h
      exact h
    · have h := lvlQ_peakFlip_ge (q := q) hk (m := i + 1) (by omega) (by omega)
      have hsub : s.length + k - (i + 1) = s.length + k - 1 - i := by omega
      rw [hsub] at h
      exact h
  have hidx : startIdxQ q s = (sweepIdxQ q fl).map (flipIdx s.length k) := by
    apply List.Perm.eq_of_pairwise (le := fun i j => lvlQ q s i < lvlQ q s j)
    · intro a b _ _ hab hba
      exact (lt_asymm hab hba).elim
    · refine ((startIdxQ_pairwise q s).and (startIdxQ_nodup q s)).imp_of_mem ?_
      intro a b ha hb h
      have ha' := mem_startIdxQ.mp ha
      have hb' := mem_startIdxQ.mp hb
      exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) h.2)
    · rw [List.pairwise_map]
      refine ((sweepIdxQ_pairwise q fl).and (sweepIdxQ_nodup q fl)).imp_of_mem ?_
      intro a b ha hb h
      have ha' : a < s.length := hlen ▸ mem_sweepIdxQ.mp ha
      have hb' : b < s.length := hlen ▸ mem_sweepIdxQ.mp hb
      have hstrict : lvlQ q fl (b + 1) < lvlQ q fl (a + 1) :=
        lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
      have hea := hend a ha'
      have heb := hend b hb'
      have hfa := flipIdx_lt hk ha'
      have hfb := flipIdx_lt hk hb'
      by_cases hak : a < k
      · by_cases hbk : b < k
        · simp only [hak, ↓reduceIte] at hea
          simp only [hbk, ↓reduceIte] at heb
          exact lt_of_mul_eq_mul (hpos _ _) (hpos _ _) (heb.trans hea.symm) hstrict
        · simp only [hak, ↓reduceIte] at hea
          simp only [hbk, ↓reduceIte] at heb
          have hfa' : flipIdx s.length k a < k := by
            unfold flipIdx
            simp only [hak, ↓reduceIte]
            omega
          have hfb' : k ≤ flipIdx s.length k b := by
            unfold flipIdx
            simp only [hbk, ↓reduceIte]
            omega
          have hX : lvlQ q s (flipIdx s.length k a) * lvlQ q s s.length <
              lvlQ q s (flipIdx s.length k b) := by
            apply lt_of_mul_eq_mul (hpos fl (b + 1)) (mul_pos (hpos _ _) (hpos _ _)) _ hstrict
            rw [heb, ← hea]
            ring
          exact h1 _ _ hfa' hfb' hfb hX
      · by_cases hbk : b < k
        · simp only [hak, ↓reduceIte] at hea
          simp only [hbk, ↓reduceIte] at heb
          have hfa' : k ≤ flipIdx s.length k a := by
            unfold flipIdx
            simp only [hak, ↓reduceIte]
            omega
          have hfb' : flipIdx s.length k b < k := by
            unfold flipIdx
            simp only [hbk, ↓reduceIte]
            omega
          have hX : lvlQ q s (flipIdx s.length k a) <
              lvlQ q s (flipIdx s.length k b) * lvlQ q s s.length := by
            apply lt_of_mul_eq_mul (hpos fl (b + 1)) (hpos _ _) _ hstrict
            rw [hea, ← heb]
            ring
          exact h2 _ _ hfb' hfa' hfa hX
        · simp only [hak, ↓reduceIte] at hea
          simp only [hbk, ↓reduceIte] at heb
          exact lt_of_mul_eq_mul (hpos _ _) (hpos _ _) (heb.trans hea.symm) hstrict
    · have hp1 := (sweepIdxQ_perm q fl).map (flipIdx s.length k)
      rw [hlen] at hp1
      exact (startIdxQ_perm q s).trans ((hp1.trans (perm_map_flipIdx hk)).symm)
  unfold startSweepQ sweepQ
  rw [hidx, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < s.length := hlen ▸ mem_sweepIdxQ.mp hi
  exact (getD_peakFlip hk hi').symm

/-! ### Words that are rotations of each other -/

/-- Two flips that agree come from two words that are rotations of each other. -/
theorem exists_rotation_of_peakFlip_eq {s t : List Bool} {k m : ℕ}
    (h : peakFlip s k = peakFlip t m) : ∃ z u, s = z ++ u ∧ t = u ++ z := by
  have hrev := congrArg List.reverse h
  unfold peakFlip at hrev
  rw [List.reverse_append, List.reverse_reverse, List.reverse_reverse, List.reverse_append,
    List.reverse_reverse, List.reverse_reverse, List.append_eq_append_iff] at hrev
  rcases hrev with ⟨a, h1, h2⟩ | ⟨c, h1, h2⟩
  · refine ⟨a, t.take m ++ s.drop k, ?_, ?_⟩
    · rw [← List.append_assoc, ← h2, List.take_append_drop]
    · rw [List.append_assoc, ← h1, List.take_append_drop]
  · refine ⟨s.take k ++ t.drop m, c, ?_, ?_⟩
    · rw [List.append_assoc, ← h1, List.take_append_drop]
    · rw [← List.append_assoc, ← h2, List.take_append_drop]

/-- Two admissible words that are rotations of each other are equal. -/
theorem append_comm_of_admissibleQ {z u : List Bool} (h1 : AdmissibleQ q (z ++ u))
    (h2 : AdmissibleQ q (u ++ z)) : z ++ u = u ++ z := by
  rcases List.eq_nil_or_concat' z with hz | hz
  · rw [hz]
    simp
  rcases List.eq_nil_or_concat' u with hu | hu
  · rw [hu]
    simp
  exfalso
  have hzl : 1 ≤ z.length := by
    obtain ⟨_, _, rfl⟩ := hz
    simp
  have hul : 1 ≤ u.length := by
    obtain ⟨_, _, rfl⟩ := hu
    simp
  have hzL : z.length < (z ++ u).length := by
    rw [List.length_append]
    omega
  have huL : u.length < (u ++ z).length := by
    rw [List.length_append]
    omega
  have hz1 := h1.prefix_gt z.length hzl hzL
  have hu1 := h2.prefix_gt u.length hul huL
  rw [List.take_left] at hz1 hu1
  have hlt := h1.lt_one
  rw [seqProductQ_append] at hlt
  nlinarith

/-! ### Upper record Orders -/

theorem order_take_mono (s : List Bool) {i j : ℕ} (hij : i ≤ j) :
    order (s.take i) ≤ order (s.take j) := by
  have h := order_take_le (s.take j) i
  rwa [List.take_take, min_eq_left hij] at h

/-- lvl j < lvl i times the level of the whole word, as cross products. -/
theorem lvlQ_lt_mul_iff (q : ℕ) {s : List Bool} {i j : ℕ} (hi : i ≤ s.length)
    (hj : j ≤ s.length) :
    lvlQ q s j < lvlQ q s i * lvlQ q s s.length ↔
      q ^ order (s.take j) * 2 ^ i * 2 ^ s.length <
        q ^ order (s.take i) * q ^ order s * 2 ^ j := by
  have h1 := lvlQ_mul_pow q hi
  have h2 := lvlQ_mul_pow q hj
  have h3 := lvlQ_mul_pow q (s := s) (j := s.length) le_rfl
  rw [List.take_length] at h3
  have hp : (0 : ℚ) < 2 ^ i * 2 ^ j * 2 ^ s.length := by positivity
  have hcast : (q ^ order (s.take j) * 2 ^ i * 2 ^ s.length <
      q ^ order (s.take i) * q ^ order s * 2 ^ j) ↔
      ((q : ℚ) ^ order (s.take j) * 2 ^ i * 2 ^ s.length <
        q ^ order (s.take i) * q ^ order s * 2 ^ j) := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  have hL : lvlQ q s j * (2 ^ i * 2 ^ j * 2 ^ s.length) =
      (q : ℚ) ^ order (s.take j) * 2 ^ i * 2 ^ s.length := by
    rw [← h2]
    ring
  have hR : lvlQ q s i * lvlQ q s s.length * (2 ^ i * 2 ^ j * 2 ^ s.length) =
      (q : ℚ) ^ order (s.take i) * q ^ order s * 2 ^ j := by
    rw [← h1, ← h3]
    ring
  rw [hcast, ← hL, ← hR]
  exact (mul_lt_mul_iff_of_pos_right hp).symm

/-- At an upper record Order no point before the end of an admissible word lies below an
    earlier point by less than the level of the whole word. -/
theorem lvlQ_lt_mul_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : UpperRecordQ q n) {s : List Bool} (hs : s ∈ admSetQ q n) {i j : ℕ} (hij : i < j)
    (hj : j < s.length) (hlt : lvlQ q s j < lvlQ q s i) :
    lvlQ q s j < lvlQ q s i * lvlQ q s s.length := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hlen : s.length = p2Q q n := by
    rw [admissibleQ_length (by omega) hA, hord]
  have hq0 : 0 < q := by omega
  have hmono := order_take_mono s hij.le
  have hjn : order (s.take j) ≤ n := hord ▸ order_take_le s j
  obtain ⟨a, ha⟩ : ∃ a, order (s.take j) = order (s.take i) + a :=
    ⟨order (s.take j) - order (s.take i), by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hlt' := (lvlQ_lt_iff q (by omega) (by omega)).mp hlt
  rw [ha, pow_add, pow_add] at hlt'
  have hqa : q ^ a < 2 ^ d := by
    have hc : 0 < q ^ order (s.take i) * 2 ^ i := by positivity
    by_contra hge
    push Not at hge
    have := Nat.mul_le_mul_left (q ^ order (s.take i) * 2 ^ i) hge
    nlinarith
  rw [lvlQ_lt_mul_iff q (by omega) (by omega), ha, hord, hlen]
  have hkey : q ^ a * 2 ^ p2Q q n < q ^ n * 2 ^ d := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · have hn1 : 1 ≤ n := by
        by_contra h0
        have hn0 : n = 0 := by omega
        rw [hn0] at hlen
        simp [p2Q] at hlen
        omega
      rw [ha0, pow_zero, one_mul, lt_q_pow_mul_iff hodd hq hn1]
      omega
    · rcases Nat.lt_or_ge a n with han | han
      · have hbf := (upperRecordQ_iff_blockFactorQ hodd hq n).mp hR a hapos han
        rw [blockFactorQ_lt_iff] at hbf
        have hpa := (q_pow_lt_two_pow_iff hq).mp hqa
        have hpow : 2 ^ p2Q q a ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hpa
        calc q ^ a * 2 ^ p2Q q n < q ^ n * 2 ^ p2Q q a := hbf
          _ ≤ q ^ n * 2 ^ d := Nat.mul_le_mul_left _ hpow
      · exfalso
        have hi0 : order (s.take i) = 0 := by omega
        have hli := lvlQ_mul_pow q (s := s) (j := i) (by omega)
        rw [hi0, pow_zero] at hli
        have h2i : (1 : ℚ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        have hipos := lvlQ_pos hq0 s i
        have hle1 : lvlQ q s i ≤ 1 := by
          nlinarith
        have hgt : 1 < lvlQ q s (i + d) := hA.prefix_gt (i + d) (by omega) hj
        linarith
  calc q ^ (order (s.take i) + a) * 2 ^ i * 2 ^ p2Q q n
      = q ^ order (s.take i) * 2 ^ i * (q ^ a * 2 ^ p2Q q n) := by
        rw [pow_add]
        ring
    _ < q ^ order (s.take i) * 2 ^ i * (q ^ n * 2 ^ d) :=
        Nat.mul_lt_mul_of_pos_left hkey (by positivity)
    _ = q ^ order (s.take i) * q ^ n * 2 ^ (i + d) := by
        rw [pow_add]
        ring

/-- A word has a highest point. -/
theorem exists_peak (q : ℕ) (s : List Bool) :
    ∃ k, k ≤ s.length ∧ ∀ j, j ≤ s.length → lvlQ q s j ≤ lvlQ q s k := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range (s.length + 1)) (lvlQ q s)
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  rw [Finset.mem_range] at hk
  exact ⟨k, by omega, fun j hj => hmax j (Finset.mem_range.mpr (by omega))⟩

/-- At an upper record Order the flip of an admissible word around its highest point is
    admissible. -/
theorem peakFlip_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hR : UpperRecordQ q n)
    {s : List Bool} (hs : s ∈ admSetQ q n) {k : ℕ} (hk : k ≤ s.length)
    (hmax : ∀ j, j ≤ s.length → lvlQ q s j ≤ lvlQ q s k) : peakFlip s k ∈ admSetQ q n := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hq0 : 0 < q := by omega
  rw [mem_admSetQ (by omega)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m hm1 hmL
    rw [length_peakFlip] at hmL
    change 1 < lvlQ q (peakFlip s k) m
    rcases Nat.le_total m k with hmk | hkm
    · have h := lvlQ_peakFlip_le (q := q) hk hmk
      have hlt : lvlQ q s (k - m) < lvlQ q s k :=
        lt_of_le_of_ne (hmax _ (by omega)) (lvlQ_ne_of_ne hodd (by omega) hk (by omega))
      have hp := lvlQ_pos hq0 s (k - m)
      by_contra hle
      push Not at hle
      nlinarith
    · rcases Nat.eq_or_lt_of_le hkm with hkm' | hkm'
      · have h := lvlQ_peakFlip_le (q := q) hk (le_of_eq hkm'.symm)
        have hlt : lvlQ q s (k - m) < lvlQ q s k :=
          lt_of_le_of_ne (hmax _ (by omega)) (lvlQ_ne_of_ne hodd (by omega) hk (by omega))
        have hp := lvlQ_pos hq0 s (k - m)
        by_contra hle
        push Not at hle
        nlinarith
      · have h := lvlQ_peakFlip_ge (q := q) hk hkm hmL.le
        have hp1 : k < s.length + k - m := by omega
        have hp2 : s.length + k - m < s.length := by omega
        have hlt : lvlQ q s (s.length + k - m) < lvlQ q s k :=
          lt_of_le_of_ne (hmax _ hp2.le) (lvlQ_ne_of_ne hodd hp2.le hk (by omega))
        have hup := lvlQ_lt_mul_of_upperRecordQ hodd hq hR hs hp1 hp2 hlt
        have hp := lvlQ_pos hq0 s (s.length + k - m)
        by_contra hle
        push Not at hle
        nlinarith
  · rw [seqProductQ_perm q (peakFlip_perm s k)]
    exact hA.lt_one
  · rw [order_perm (peakFlip_perm s k), hord]

/-- At an upper record Order the start sweep of an admissible word is the sweep of its
    flip around any of its points. -/
theorem startSweepQ_eq_sweepQ_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : UpperRecordQ q n) {s : List Bool} (hs : s ∈ admSetQ q n) {k : ℕ} (hk : k ≤ s.length) :
    startSweepQ q s = sweepQ q (peakFlip s k) := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hq0 : 0 < q := by omega
  have hE : lvlQ q s s.length < 1 := by
    rw [lvlQ_length]
    exact hA.lt_one
  apply startSweepQ_eq_sweepQ_peakFlip hodd hq0 hk
  · intro i j hik hkj hj hlt
    by_contra hge
    push Not at hge
    have hne := lvlQ_ne_of_ne hodd (s := s) (i := j) (k := i) hj.le (by omega) (by omega)
    have hup := lvlQ_lt_mul_of_upperRecordQ hodd hq hR hs (by omega : i < j) hj
      (lt_of_le_of_ne hge hne)
    linarith
  · intro i j hik hkj hj hlt
    have hp := lvlQ_pos hq0 s i
    nlinarith

/-- At an upper record Order the start sweep maps admissible words to admissible words. -/
theorem startSweepQ_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hR : UpperRecordQ q n)
    {s : List Bool} (hs : s ∈ admSetQ q n) : startSweepQ q s ∈ admSetQ q n := by
  obtain ⟨k, hk, hmax⟩ := exists_peak q s
  rw [startSweepQ_eq_sweepQ_of_upperRecordQ hodd hq hR hs hk]
  exact sweepQ_mem_admSetQ hodd (by omega) (peakFlip_mem_admSetQ hodd hq hR hs hk hmax)

/-- The start sweep maps the admissible words of Order n to admissible words exactly at
    the upper record Orders. -/
theorem mapsTo_startSweepQ_iff (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    Set.MapsTo (startSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) ↔
      UpperRecordQ q n := by
  constructor
  · intro h
    by_contra hR
    exact startSweepQ_upDownQ_not_mem hodd hq hR (h (upDownQ_mem_admSetQ hodd hq n))
  · intro hR s hs
    exact startSweepQ_mem_admSetQ hodd hq hR hs

/-- Under Thomas and Williams, Thm 6.3, the start sweep permutes the admissible words of
    an upper record Order. -/
theorem startSweepQ_bijOn (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) {n : ℕ}
    (hR : UpperRecordQ q n) :
    Set.BijOn (startSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) := by
  have hmaps := (mapsTo_startSweepQ_iff hodd hq n).mpr hR
  refine ((admSetQ q n).finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).mp ?_
  intro s hs t ht heq
  have hs1 : s ∈ admSetQ q n := hs
  have ht1 : t ∈ admSetQ q n := ht
  obtain ⟨k, hk, hkmax⟩ := exists_peak q s
  obtain ⟨m, hm, hmmax⟩ := exists_peak q t
  rw [startSweepQ_eq_sweepQ_of_upperRecordQ hodd hq hR hs1 hk,
    startSweepQ_eq_sweepQ_of_upperRecordQ hodd hq hR ht1 hm] at heq
  have hfl := (sweepQ_bijOn hodd hq hTW n).injOn
    (peakFlip_mem_admSetQ hodd hq hR hs1 hk hkmax)
    (peakFlip_mem_admSetQ hodd hq hR ht1 hm hmmax) heq
  obtain ⟨z, u, rfl, rfl⟩ := exists_rotation_of_peakFlip_eq hfl
  exact append_comm_of_admissibleQ ((mem_admSetQ (by omega) _ _).mp hs1).1
    ((mem_admSetQ (by omega) _ _).mp ht1).1

/-- Under Thomas and Williams, Thm 6.3, the start sweep permutes the admissible words of
    Order n exactly at the upper record Orders. -/
theorem startSweepQ_bijOn_iff (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) (n : ℕ) :
    Set.BijOn (startSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) ↔
      UpperRecordQ q n :=
  ⟨fun h => (mapsTo_startSweepQ_iff hodd hq n).mp h.mapsTo, startSweepQ_bijOn hodd hq hTW⟩

/-! ## 9. The cut sweep -/

/-- Cut sweep: the start sweep of s without its final step, then a halving. -/
def cutSweepQ (q : ℕ) (s : List Bool) : List Bool := startSweepQ q s.dropLast ++ [false]

theorem cutSweepQ_append_false (q : ℕ) (w : List Bool) :
    cutSweepQ q (w ++ [false]) = startSweepQ q w ++ [false] := by
  unfold cutSweepQ
  rw [List.dropLast_concat]

theorem cutSweepQ_perm (q : ℕ) (w : List Bool) :
    (cutSweepQ q (w ++ [false])).Perm (w ++ [false]) := by
  rw [cutSweepQ_append_false]
  exact (startSweepQ_perm q w).append_right [false]

theorem lvlQ_append_left (q : ℕ) {w t : List Bool} {m : ℕ} (hm : m ≤ w.length) :
    lvlQ q (w ++ t) m = lvlQ q w m := by
  unfold lvlQ
  rw [List.take_append_of_le_length hm]

/-- The inner points of the cut part of an admissible word have level above 1. -/
theorem one_lt_lvlQ_cut (hq : 3 ≤ q) {n : ℕ} {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ w.length) : 1 < lvlQ q w j := by
  have hA := ((mem_admSetQ (by omega) _ _).mp hs).1
  have hjL : j < (w ++ [false]).length := by
    rw [List.length_append, List.length_singleton]
    omega
  have h := hA.prefix_gt j hj1 hjL
  rwa [List.take_append_of_le_length hj] at h

theorem order_cut {n : ℕ} (hq : 3 ≤ q) {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    order w = n := by
  have h := ((mem_admSetQ (by omega) _ _).mp hs).2
  unfold order at h ⊢
  simpa using h

theorem length_cut {n : ℕ} (hq : 3 ≤ q) {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    w.length + 1 = p2Q q n := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have h := admissibleQ_length (by omega) hA
  rw [hord, List.length_append, List.length_singleton] at h
  exact h

/-! ### The cut sweep of an admissible word is admissible -/

/-- The steps that start below c, and no others, multiply to at least c or to at least
    the level of the whole word. -/
theorem min_le_prod_of_lower (hq0 : 0 < q) (s : List Bool) (T : Finset ℕ) {c : ℚ}
    (hT : ∀ i ∈ T, i < s.length ∧ lvlQ q s i < c)
    (hN : ∀ i < s.length, i ∉ T → c ≤ lvlQ q s i) :
    min (lvlQ q s s.length) c ≤ ∏ i ∈ T, factorQ q (s.getD i false) := by
  let g : ℕ → ℚ := fun m => ∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)
  have hg_succ_mem : ∀ m, m ∈ T → g (m + 1) = g m * factorQ q (s.getD m false) := by
    intro m hm
    change ∏ i ∈ (Finset.range (m + 1)).filter (· ∈ T), factorQ q (s.getD i false) =
      (∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)) *
        factorQ q (s.getD m false)
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hm, ↓reduceIte]
    rw [Finset.prod_insert (by simp), mul_comm]
  have hg_succ_not : ∀ m, m ∉ T → g (m + 1) = g m := by
    intro m hm
    change ∏ i ∈ (Finset.range (m + 1)).filter (· ∈ T), factorQ q (s.getD i false) =
      ∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hm, ↓reduceIte]
  have inv : ∀ m ≤ s.length, min (lvlQ q s m) c ≤ g m := by
    intro m
    induction m with
    | zero =>
      intro _
      have hg0 : g 0 = 1 := by
        change ∏ i ∈ (Finset.range 0).filter (· ∈ T), factorQ q (s.getD i false) = 1
        simp
      rw [lvlQ_zero, hg0]
      exact min_le_left _ _
    | succ m ih =>
      intro hm
      have ihm := ih (by omega)
      have hlt : m < s.length := by omega
      have hget : s[m]? = some (s.getD m false) := by
        simp [List.getD_eq_getElem?_getD, hlt]
      have hstep := lvlQ_succ q s hget
      have hf := factorQ_pos hq0 (s.getD m false)
      by_cases hmT : m ∈ T
      · rw [hg_succ_mem m hmT, hstep]
        have hlow := (hT m hmT).2
        rw [min_eq_left hlow.le] at ihm
        exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right ihm hf.le)
      · rw [hg_succ_not m hmT]
        have hhigh := hN m hlt hmT
        rw [min_eq_right hhigh] at ihm
        exact (min_le_right _ _).trans ihm
  have hfilter : (Finset.range s.length).filter (· ∈ T) = T := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨(hT k h).1, h⟩
  have h1 := inv s.length le_rfl
  change min (lvlQ q s s.length) c ≤
    ∏ i ∈ (Finset.range s.length).filter (· ∈ T), factorQ q (s.getD i false) at h1
  rwa [hfilter] at h1

/-- A proper prefix of the start sweep of the cut part of an admissible word: its set T
    of steps, a step k outside T, and the bound of `min_le_prod_of_lower` at the level
    at which k starts. -/
theorem exists_startSweepQ_prefix_bound (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {w : List Bool}
    (hs : w ++ [false] ∈ admSetQ q n) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < w.length) :
    ∃ (T : Finset ℕ) (k : ℕ), T.card = m ∧ 0 ∈ T ∧ k ∉ T ∧ 1 ≤ k ∧ k < w.length ∧
      (∀ i ∈ T, i < w.length ∧ lvlQ q w i < lvlQ q w k) ∧
      min (lvlQ q w w.length) (lvlQ q w k) ≤ seqProductQ q ((startSweepQ q w).take m) := by
  obtain ⟨T, hcard, hT, hlow, hprod⟩ := exists_startSweepQ_prefix_set hodd w hm.le
  have hq0 : 0 < q := by omega
  set C := Finset.range w.length \ T with hC
  have hCne : C.Nonempty := by
    rw [← Finset.card_pos, hC, Finset.card_sdiff_of_subset
      (fun i hi => Finset.mem_range.mpr (hT i hi)), Finset.card_range]
    omega
  obtain ⟨k, hkC, hk⟩ := Finset.exists_mem_eq_inf' hCne (lvlQ q w)
  rw [hC, Finset.mem_sdiff, Finset.mem_range] at hkC
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have h0T : 0 ∈ T := by
    by_contra h0
    obtain ⟨i, hi⟩ := hTne
    have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)
    have hlt := hlow i hi 0 (by omega) h0
    rw [lvlQ_zero] at hlt
    have hgt := one_lt_lvlQ_cut hq hs (j := i) (by omega) (hT i hi).le
    linarith
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    exact hkC.2 (hk0 ▸ h0T)
  have hTk : ∀ i ∈ T, i < w.length ∧ lvlQ q w i < lvlQ q w k :=
    fun i hi => ⟨hT i hi, hlow i hi k hkC.1 hkC.2⟩
  have hN : ∀ i < w.length, i ∉ T → lvlQ q w k ≤ lvlQ q w i := by
    intro i hi hiT
    have hiC : i ∈ C := by
      rw [hC, Finset.mem_sdiff, Finset.mem_range]
      exact ⟨hi, hiT⟩
    rw [← hk]
    exact Finset.inf'_le _ hiC
  refine ⟨T, k, hcard, h0T, hkC.2, hk1, hkC.1, hTk, ?_⟩
  rw [hprod]
  exact min_le_prod_of_lower hq0 w T hTk hN

/-- The cut sweep maps admissible words of Order n to admissible words of Order n. -/
theorem cutSweepQ_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {s : List Bool}
    (hs : s ∈ admSetQ q n) : cutSweepQ q s ∈ admSetQ q n := by
  obtain ⟨w, rfl⟩ := exists_eq_append_falseQ hq hs
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  rw [mem_admSetQ (by omega)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m hm1 hmL
    rw [(cutSweepQ_perm q w).length_eq, List.length_append, List.length_singleton] at hmL
    have hmw : m ≤ (startSweepQ q w).length := by
      rw [length_startSweepQ]
      omega
    rw [cutSweepQ_append_false, List.take_append_of_le_length hmw]
    have hE : 1 < lvlQ q w w.length := one_lt_lvlQ_cut hq hs (by omega) le_rfl
    rcases Nat.lt_or_ge m w.length with hlt | hge
    · obtain ⟨T, k, _, _, _, hk1, hkL, _, hmin⟩ :=
        exists_startSweepQ_prefix_bound hodd hq hs hm1 hlt
      have hk := one_lt_lvlQ_cut hq hs hk1 hkL.le
      exact lt_of_lt_of_le (lt_min hE hk) hmin
    · have hwm : (startSweepQ q w).length ≤ m := by
        rw [length_startSweepQ]
        omega
      rw [List.take_of_length_le hwm, seqProductQ_startSweepQ, ← lvlQ_length]
      exact hE
  · rw [seqProductQ_perm q (cutSweepQ_perm q w)]
    exact hA.lt_one
  · rw [order_perm (cutSweepQ_perm q w), hord]

/-! ### Lower record Orders -/

/-- The sweep of an admissible word keeps the final halving last. -/
theorem sweepQ_append_false (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {t : List Bool}
    (hs : t ++ [false] ∈ admSetQ q n) :
    sweepQ q (t ++ [false]) = sweepQ q t ++ [false] := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  set s := t ++ [false] with hsdef
  have hlen : s.length = t.length + 1 := by simp [hsdef]
  have hlvl : ∀ m, m ≤ t.length → lvlQ q s m = lvlQ q t m :=
    fun m hm => lvlQ_append_left q hm
  have hidx : sweepIdxQ q s = sweepIdxQ q t ++ [t.length] := by
    apply List.Perm.eq_of_pairwise (le := fun i k => lvlQ q s (k + 1) < lvlQ q s (i + 1))
    · intro a b _ _ hab hba
      exact (lt_asymm hab hba).elim
    · refine ((sweepIdxQ_pairwise q s).and (sweepIdxQ_nodup q s)).imp_of_mem ?_
      intro a b ha hb h
      have ha' := mem_sweepIdxQ.mp ha
      have hb' := mem_sweepIdxQ.mp hb
      exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
    · rw [List.pairwise_append]
      refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
      · refine ((sweepIdxQ_pairwise q t).and (sweepIdxQ_nodup q t)).imp_of_mem ?_
        intro a b ha hb h
        have ha' := mem_sweepIdxQ.mp ha
        have hb' := mem_sweepIdxQ.mp hb
        rw [hlvl _ (by omega), hlvl _ (by omega)]
        exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
      · intro a ha b hb
        rw [List.mem_singleton] at hb
        rw [hb]
        have ha' := mem_sweepIdxQ.mp ha
        have hgt : 1 < lvlQ q s (a + 1) := hA.prefix_gt (a + 1) (by omega) (by omega)
        have hend : lvlQ q s (t.length + 1) < 1 := by
          rw [← hlen, lvlQ_length]
          exact hA.lt_one
        linarith
    · have h := (sweepIdxQ_perm q t).append_right [t.length]
      have h2 := sweepIdxQ_perm q s
      rw [hlen, List.range_succ] at h2
      exact h2.trans h.symm
  unfold sweepQ
  rw [hidx, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi' : i < t.length := mem_sweepIdxQ.mp hi
    simp [hsdef, List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
  · simp [hsdef]

/-- At a lower record Order a later point of the cut part above an earlier one is above
    it by at least the level of the cut part. -/
theorem lvlQ_mul_le_of_lowerRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : LowerRecordQ q n) {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) {i j : ℕ}
    (hij : i < j) (hj : j < w.length) (hlt : lvlQ q w i < lvlQ q w j) :
    lvlQ q w i * lvlQ q w w.length ≤ lvlQ q w j := by
  have hord := order_cut hq hs
  have hlen := length_cut hq hs
  have hmono := order_take_mono w hij.le
  have hjn : order (w.take j) ≤ n := hord ▸ order_take_le w j
  obtain ⟨a, ha⟩ : ∃ a, order (w.take j) = order (w.take i) + a :=
    ⟨order (w.take j) - order (w.take i), by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  have hlt' := (lvlQ_lt_iff q (by omega) (by omega)).mp hlt
  rw [ha, pow_add, pow_add] at hlt'
  have hqa : 2 ^ d < q ^ a := by
    have hc : 0 < q ^ order (w.take i) * 2 ^ i := by positivity
    by_contra hge
    push Not at hge
    have := Nat.mul_le_mul_left (q ^ order (w.take i) * 2 ^ i) hge
    nlinarith
  have ha1 : 1 ≤ a := by
    by_contra h0
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero] at hqa
    have := Nat.one_le_two_pow (n := d)
    omega
  have hda := (two_pow_lt_q_pow_iff hodd hq ha1).mp hqa
  have hkey : q ^ n * 2 ^ d ≤ q ^ a * 2 ^ w.length := by
    rcases Nat.lt_or_ge a n with han | han
    · have hbf := (lowerRecordQ_iff_blockFactorQ hq n).mp hR a ha1 han
      rw [blockFactorQ_lt_iff, ← hlen, pow_succ] at hbf
      have hpow : 2 ^ (d + 1) ≤ 2 ^ p2Q q a := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1 : q ^ n * 2 ^ (d + 1) ≤ q ^ n * 2 ^ p2Q q a := Nat.mul_le_mul_left _ hpow
      rw [pow_succ] at h1
      nlinarith
    · have han' : a = n := by omega
      rw [han']
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [← not_lt, lvlQ_lt_mul_iff q (by omega) (by omega), ha, hord, not_lt]
  calc q ^ order (w.take i) * q ^ n * 2 ^ (i + d)
      = q ^ order (w.take i) * 2 ^ i * (q ^ n * 2 ^ d) := by
        rw [pow_add]
        ring
    _ ≤ q ^ order (w.take i) * 2 ^ i * (q ^ a * 2 ^ w.length) :=
        Nat.mul_le_mul_left _ hkey
    _ = q ^ (order (w.take i) + a) * 2 ^ i * 2 ^ w.length := by
        rw [pow_add]
        ring

/-- The flip of the cut part of an admissible word around its highest point, with the
    halving, is admissible. -/
theorem peakFlip_append_false_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {w : List Bool}
    (hs : w ++ [false] ∈ admSetQ q n) {k : ℕ} (hk : k ≤ w.length)
    (hmax : ∀ j, j ≤ w.length → lvlQ q w j ≤ lvlQ q w k) :
    peakFlip w k ++ [false] ∈ admSetQ q n := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hq0 : 0 < q := by omega
  have hperm : (peakFlip w k ++ [false]).Perm (w ++ [false]) :=
    (peakFlip_perm w k).append_right [false]
  rw [mem_admSetQ (by omega)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m hm1 hmL
    rw [hperm.length_eq, List.length_append, List.length_singleton] at hmL
    have hmf : m ≤ (peakFlip w k).length := by
      rw [length_peakFlip]
      omega
    rw [List.take_append_of_le_length hmf]
    change 1 < lvlQ q (peakFlip w k) m
    have hE : 1 < lvlQ q w w.length := one_lt_lvlQ_cut hq hs (by omega) le_rfl
    rcases Nat.le_total m k with hmk | hkm
    · have h := lvlQ_peakFlip_le (q := q) hk hmk
      have hlt : lvlQ q w (k - m) < lvlQ q w k :=
        lt_of_le_of_ne (hmax _ (by omega)) (lvlQ_ne_of_ne hodd (by omega) hk (by omega))
      have hp := lvlQ_pos hq0 w (k - m)
      by_contra hle
      push Not at hle
      nlinarith
    · have h := lvlQ_peakFlip_ge (q := q) hk hkm (by omega)
      have hle := hmax (w.length + k - m) (by omega)
      have hp := lvlQ_pos hq0 w (w.length + k - m)
      have hpk := lvlQ_pos hq0 w k
      by_contra hle1
      push Not at hle1
      nlinarith
  · rw [seqProductQ_perm q hperm]
    exact hA.lt_one
  · rw [order_perm hperm, hord]

/-- At a lower record Order the cut sweep of an admissible word is the sweep of the flip
    of its cut part around its highest point, with the halving. -/
theorem cutSweepQ_eq_sweepQ_of_lowerRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : LowerRecordQ q n) {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) {k : ℕ}
    (hk : k ≤ w.length) (hmax : ∀ j, j ≤ w.length → lvlQ q w j ≤ lvlQ q w k) :
    cutSweepQ q (w ++ [false]) = sweepQ q (peakFlip w k ++ [false]) := by
  have hq0 : 0 < q := by omega
  rw [cutSweepQ_append_false,
    sweepQ_append_false hodd hq (peakFlip_append_false_mem_admSetQ hodd hq hs hk hmax)]
  congr 1
  apply startSweepQ_eq_sweepQ_peakFlip hodd hq0 hk
  · intro i j hik hkj hj hlt
    have hE : 1 < lvlQ q w w.length := one_lt_lvlQ_cut hq hs (by omega) le_rfl
    have hp := lvlQ_pos hq0 w i
    nlinarith
  · intro i j hik hkj hj hlt
    by_contra hge
    push Not at hge
    have hne := lvlQ_ne_of_ne hodd (s := w) (i := i) (k := j) (by omega) hj.le (by omega)
    have hlow := lvlQ_mul_le_of_lowerRecordQ hodd hq hR hs (by omega : i < j) hj
      (lt_of_le_of_ne hge hne)
    linarith

/-- At a lower record Order two admissible words whose cut parts are rotations of each
    other are equal. -/
theorem append_comm_of_lowerRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : LowerRecordQ q n) {z u : List Bool} (h1 : z ++ u ++ [false] ∈ admSetQ q n)
    (h2 : u ++ z ++ [false] ∈ admSetQ q n) : z ++ u = u ++ z := by
  rcases List.eq_nil_or_concat' z with hz | hz
  · rw [hz]
    simp
  rcases List.eq_nil_or_concat' u with hu | hu
  · rw [hu]
    simp
  exfalso
  have hq0 : 0 < q := by omega
  have hzl : 1 ≤ z.length := by
    obtain ⟨_, _, rfl⟩ := hz
    simp
  have hul : 1 ≤ u.length := by
    obtain ⟨_, _, rfl⟩ := hu
    simp
  have hlen : (z ++ u).length = z.length + u.length := List.length_append
  have hzgt : 1 < lvlQ q (z ++ u) z.length :=
    one_lt_lvlQ_cut hq h1 hzl (by omega)
  have hz0 : lvlQ q (z ++ u) 0 < lvlQ q (z ++ u) z.length := by
    rw [lvlQ_zero]
    exact hzgt
  have hlow := lvlQ_mul_le_of_lowerRecordQ hodd hq hR h1 (i := 0) (j := z.length)
    (by omega) (by omega) hz0
  rw [lvlQ_zero, one_mul, lvlQ_length, seqProductQ_append] at hlow
  have hzz : lvlQ q (z ++ u) z.length = seqProductQ q z := by
    unfold lvlQ
    rw [List.take_left]
  rw [hzz] at hlow
  have huL : u.length ≤ (u ++ z).length := by
    rw [List.length_append]
    omega
  have hugt : 1 < lvlQ q (u ++ z) u.length := one_lt_lvlQ_cut hq h2 hul huL
  have huu : lvlQ q (u ++ z) u.length = seqProductQ q u := by
    unfold lvlQ
    rw [List.take_left]
  rw [huu] at hugt
  have hzpos := seqProductQ_pos hq0 z
  nlinarith

/-- Under Thomas and Williams, Thm 6.3, the cut sweep permutes the admissible words of a
    lower record Order. -/
theorem cutSweepQ_bijOn (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) {n : ℕ}
    (hR : LowerRecordQ q n) :
    Set.BijOn (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) := by
  have hmaps : Set.MapsTo (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) :=
    fun s hs => cutSweepQ_mem_admSetQ hodd hq hs
  refine ((admSetQ q n).finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).mp ?_
  intro s hs t ht heq
  have hs1 : s ∈ admSetQ q n := hs
  have ht1 : t ∈ admSetQ q n := ht
  obtain ⟨w, rfl⟩ := exists_eq_append_falseQ hq hs1
  obtain ⟨v, rfl⟩ := exists_eq_append_falseQ hq ht1
  obtain ⟨k, hk, hkmax⟩ := exists_peak q w
  obtain ⟨m, hm, hmmax⟩ := exists_peak q v
  rw [cutSweepQ_eq_sweepQ_of_lowerRecordQ hodd hq hR hs1 hk hkmax,
    cutSweepQ_eq_sweepQ_of_lowerRecordQ hodd hq hR ht1 hm hmmax] at heq
  have hfl := (sweepQ_bijOn hodd hq hTW n).injOn
    (peakFlip_append_false_mem_admSetQ hodd hq hs1 hk hkmax)
    (peakFlip_append_false_mem_admSetQ hodd hq ht1 hm hmmax) heq
  obtain ⟨z, u, rfl, rfl⟩ := exists_rotation_of_peakFlip_eq (List.append_cancel_right hfl)
  rw [append_comm_of_lowerRecordQ hodd hq hR hs1 ht1]

/-! ### Orders that are no lower record -/

/-- Two cut parts in a row, with the halving: admissible when
    p2Q(a + b) + 1 = p2Q(a) + p2Q(b). -/
theorem append_cut_mem_admSetQ (hq : 3 ≤ q) {a b : ℕ} {x y : List Bool}
    (hx : x ++ [false] ∈ admSetQ q a) (hy : y ++ [false] ∈ admSetQ q b)
    (hp : p2Q q (a + b) + 1 = p2Q q a + p2Q q b) :
    x ++ y ++ [false] ∈ admSetQ q (a + b) := by
  have hox := order_cut hq hx
  have hoy := order_cut hq hy
  have hlx := length_cut hq hx
  have hly := length_cut hq hy
  have hq0 : 0 < q := by omega
  have hord : order (x ++ y ++ [false]) = a + b := by
    unfold order at hox hoy ⊢
    simp [List.filter_append, hox, hoy]
  have hlen : (x ++ y ++ [false]).length = p2Q q (a + b) := by
    rw [List.length_append, List.length_append, List.length_singleton]
    omega
  rw [mem_admSetQ (by omega)]
  refine ⟨⟨?_, ?_⟩, hord⟩
  · intro m hm1 hmL
    rw [List.length_append, List.length_append, List.length_singleton] at hmL
    change 1 < lvlQ q (x ++ y ++ [false]) m
    rcases Nat.lt_or_ge x.length m with hxm | hmx
    · obtain ⟨e, rfl⟩ : ∃ e, m = x.length + e := ⟨m - x.length, by omega⟩
      have hsplit : lvlQ q (x ++ y ++ [false]) (x.length + e) =
          seqProductQ q x * lvlQ q y e := by
        unfold lvlQ
        rw [List.append_assoc, List.take_length_add_append, seqProductQ_append,
          List.take_append_of_le_length (by omega)]
      rw [hsplit]
      have hxge : 1 ≤ seqProductQ q x := by
        rcases Nat.eq_zero_or_pos x.length with h0 | hpos
        · rw [List.length_eq_zero_iff.mp h0]
          simp [seqProductQ]
        · have h := one_lt_lvlQ_cut hq hx hpos le_rfl
          rw [lvlQ_length] at h
          exact h.le
      have hy1 := one_lt_lvlQ_cut hq hy (j := e) (by omega) (by omega)
      nlinarith
    · rw [List.append_assoc, lvlQ_append_left q hmx]
      exact one_lt_lvlQ_cut hq hx hm1 hmx
  · have h := seqProductQ_mul_pow q (x ++ y ++ [false])
    rw [hord, hlen] at h
    have hspec : (q : ℚ) ^ (a + b) < 2 ^ p2Q q (a + b) := by
      exact_mod_cast p2Q_spec hq (a + b)
    have hpos : (0 : ℚ) < 2 ^ p2Q q (a + b) := by positivity
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_right hge hpos.le
    linarith

theorem p2Q_three_one : p2Q 3 1 = 2 := by
  unfold p2Q
  rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 1) (by norm_num) (by norm_num)]

theorem p2Q_three_two : p2Q 3 2 = 4 := by
  unfold p2Q
  rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 3) (by norm_num) (by norm_num)]

/-- At an Order that is no lower record some admissible word is not a cut sweep. -/
theorem not_surjOn_cutSweepQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hR : ¬LowerRecordQ q n) :
    ¬Set.SurjOn (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) := by
  have hq0 : 0 < q := by omega
  rw [lowerRecordQ_iff_blockFactorQ hq] at hR
  push Not at hR
  obtain ⟨a0, ha01, ha0n, ha0⟩ := hR
  have ha0I : a0 ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨ha01, by omega⟩
  obtain ⟨a, haI, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 (n - 1)) (blockFactorQ q)
    ⟨a0, ha0I⟩
  rw [Finset.mem_Icc] at haI
  have han : blockFactorQ q a ≤ blockFactorQ q n := (hmin a0 ha0I).trans ha0
  obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
  have hb1 : 1 ≤ b := by omega
  have hp : p2Q q (a + b) + 1 = p2Q q a + p2Q q b := by
    have h1 := p2Q_add_le hq a b
    have h2 := p2Q_add_le_succ hq a b
    have h3 := (blockFactorQ_add_lt_iff hq a b).not.mp (not_lt.mpr han)
    omega
  have hlt : blockFactorQ q a < blockFactorQ q (a + b) :=
    (blockFactorQ_lt_add_iff hodd hq a hb1).mpr hp
  rw [blockFactorQ_lt_iff] at hlt
  have hminN : ∀ o, 1 ≤ o → o < a + b → q ^ a * 2 ^ p2Q q o ≤ q ^ o * 2 ^ p2Q q a := by
    intro o ho1 hon
    have h := hmin o (Finset.mem_Icc.mpr ⟨ho1, by omega⟩)
    exact not_lt.mp ((blockFactorQ_lt_iff q o a).not.mp (not_lt.mpr h))
  have hp3 : 3 ≤ p2Q q a := by
    by_contra hsmall
    have hpow : q ^ a < 2 ^ 2 := (q_pow_lt_two_pow_iff hq).mpr (by omega)
    have hqa : q ≤ q ^ a := Nat.le_self_pow (by omega) q
    have hq3 : q = 3 := by omega
    subst hq3
    have ha1 : a = 1 := by
      by_contra hne
      have h9 : 3 ^ 2 ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst ha1
    rcases Nat.lt_or_ge b 2 with hb | hb
    · have hb' : b = 1 := by omega
      subst hb'
      rw [p2Q_three_two, p2Q_three_one] at hp
      omega
    · have h := hminN 2 (by omega) (by omega)
      rw [p2Q_three_two, p2Q_three_one] at h
      omega
  have hxa := upDownQ_mem_admSetQ hodd hq a
  have hyb := upDownQ_mem_admSetQ hodd hq b
  obtain ⟨x, hx⟩ := exists_eq_append_falseQ hq hxa
  obtain ⟨y, hy⟩ := exists_eq_append_falseQ hq hyb
  rw [hx] at hxa
  rw [hy] at hyb
  have ht0 := append_cut_mem_admSetQ hq hxa hyb hp
  intro hsurj
  obtain ⟨s, hs, hst⟩ := hsurj ht0
  have hs1 : s ∈ admSetQ q (a + b) := hs
  obtain ⟨w, rfl⟩ := exists_eq_append_falseQ hq hs1
  rw [cutSweepQ_append_false] at hst
  have hsw : startSweepQ q w = x ++ y := List.append_cancel_right hst
  have hlx := length_cut hq hxa
  have hly := length_cut hq hyb
  have hlw := length_cut hq hs1
  have hbp := lt_p2Q hq b
  obtain ⟨T, k, hcard, h0T, hkT, hk1, hkL, hTk, hbound⟩ :=
    exists_startSweepQ_prefix_bound hodd hq hs1 (m := x.length) (by omega) (by omega)
  rw [hsw, List.take_left] at hbound
  have hmu := seqProductQ_mul_pow q x
  rw [order_cut hq hxa] at hmu
  have hE := lvlQ_mul_pow q (s := w) (j := w.length) le_rfl
  rw [List.take_length, order_cut hq hs1] at hE
  have hltN : q ^ a * 2 ^ w.length < q ^ (a + b) * 2 ^ x.length := by
    rw [← hlw, ← hlx, pow_succ, pow_succ, ← mul_assoc, ← mul_assoc] at hlt
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hltQ : (q : ℚ) ^ a * 2 ^ w.length < (q : ℚ) ^ (a + b) * 2 ^ x.length := by
    exact_mod_cast hltN
  have hmuE : seqProductQ q x < lvlQ q w w.length := by
    have hpos : (0 : ℚ) < 2 ^ x.length * 2 ^ w.length := by positivity
    have h1 : seqProductQ q x * (2 ^ x.length * 2 ^ w.length) =
        (q : ℚ) ^ a * 2 ^ w.length := by
      rw [← hmu]
      ring
    have h2 : lvlQ q w w.length * (2 ^ x.length * 2 ^ w.length) =
        (q : ℚ) ^ (a + b) * 2 ^ x.length := by
      rw [← hE]
      ring
    apply lt_of_mul_lt_mul_right _ hpos.le
    rw [h1, h2]
    exact hltQ
  have hc : lvlQ q w k ≤ seqProductQ q x := by
    rcases min_le_iff.mp hbound with h | h
    · linarith
    · exact h
  have hlow : ∀ j, 1 ≤ j → j < w.length → seqProductQ q x ≤ lvlQ q w j := by
    intro j hj1 hjL
    have hj := lvlQ_mul_pow q (s := w) (j := j) hjL.le
    have hgt := one_lt_lvlQ_cut hq hs1 hj1 hjL.le
    have hon : order (w.take j) ≤ a + b := order_cut hq hs1 ▸ order_take_le w j
    have h2j : 2 ^ j < q ^ order (w.take j) := by
      have h2pos : (0 : ℚ) < 2 ^ j := by positivity
      have hQ : (2 : ℚ) ^ j < (q : ℚ) ^ order (w.take j) := by
        rw [← hj]
        nlinarith
      exact_mod_cast hQ
    have ho1 : 1 ≤ order (w.take j) := by
      by_contra h0
      have ho0 : order (w.take j) = 0 := by omega
      rw [ho0, pow_zero] at h2j
      have := Nat.one_le_two_pow (n := j)
      omega
    have hjo := (two_pow_lt_q_pow_iff hodd hq ho1).mp h2j
    have hkey : q ^ a * 2 ^ j ≤ q ^ order (w.take j) * 2 ^ x.length := by
      rcases Nat.lt_or_ge (order (w.take j)) (a + b) with hlt' | hge'
      · have h1 := hminN _ ho1 hlt'
        rw [← hlx, pow_succ, ← mul_assoc] at h1
        have hpow : 2 ^ (j + 1) ≤ 2 ^ p2Q q (order (w.take j)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : q ^ a * 2 ^ (j + 1) ≤ q ^ a * 2 ^ p2Q q (order (w.take j)) :=
          Nat.mul_le_mul_left _ hpow
        rw [pow_succ, ← mul_assoc] at h2
        exact Nat.le_of_mul_le_mul_right (h2.trans h1) (by norm_num)
      · have heq : order (w.take j) = a + b := by omega
        rw [heq]
        have hpow : 2 ^ j ≤ 2 ^ w.length := Nat.pow_le_pow_right (by norm_num) hjL.le
        exact (Nat.mul_le_mul_left _ hpow).trans hltN.le
    have hkeyQ : (q : ℚ) ^ a * 2 ^ j ≤ (q : ℚ) ^ order (w.take j) * 2 ^ x.length := by
      exact_mod_cast hkey
    have hpos : (0 : ℚ) < 2 ^ x.length * 2 ^ j := by positivity
    have h1 : seqProductQ q x * (2 ^ x.length * 2 ^ j) = (q : ℚ) ^ a * 2 ^ j := by
      rw [← hmu]
      ring
    have h2 : lvlQ q w j * (2 ^ x.length * 2 ^ j) =
        (q : ℚ) ^ order (w.take j) * 2 ^ x.length := by
      rw [← hj]
      ring
    apply le_of_mul_le_mul_right _ hpos
    rw [h1, h2]
    exact hkeyQ
  have hS : (insert k T).card = x.length + 1 := by
    rw [Finset.card_insert_of_notMem hkT, hcard]
  have h2 : 1 < ((insert k T).erase 0).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem h0T), hS]
    omega
  obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp h2
  have hall : ∀ i ∈ (insert k T).erase 0,
      1 ≤ i ∧ i < w.length ∧ lvlQ q w i ≤ seqProductQ q x := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_insert] at hi
    refine ⟨by omega, ?_, ?_⟩
    · rcases hi.2 with rfl | hiT
      · exact hkL
      · exact (hTk i hiT).1
    · rcases hi.2 with rfl | hiT
      · exact hc
      · exact ((hTk i hiT).2.le).trans hc
  obtain ⟨h11, h12, h13⟩ := hall i1 hi1
  obtain ⟨h21, h22, h23⟩ := hall i2 hi2
  have e1 := le_antisymm h13 (hlow i1 h11 h12)
  have e2 := le_antisymm h23 (hlow i2 h21 h22)
  exact lvlQ_ne_of_ne hodd h12.le h22.le hne (e1.trans e2.symm)

/-- At an Order that is no lower record two admissible words have the same cut sweep. -/
theorem not_injOn_cutSweepQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hR : ¬LowerRecordQ q n) :
    ¬Set.InjOn (cutSweepQ q) (admSetQ q n : Set (List Bool)) := by
  have hmaps : Set.MapsTo (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) :=
    fun s hs => cutSweepQ_mem_admSetQ hodd hq hs
  intro hinj
  exact not_surjOn_cutSweepQ hodd hq hR
    (((admSetQ q n).finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).mp hinj).surjOn

/-- Under Thomas and Williams, Thm 6.3, the cut sweep permutes the admissible words of
    Order n exactly at the lower record Orders. -/
theorem cutSweepQ_bijOn_iff (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) (n : ℕ) :
    Set.BijOn (cutSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) ↔
      LowerRecordQ q n := by
  constructor
  · intro h
    by_contra hR
    exact not_surjOn_cutSweepQ hodd hq hR h.surjOn
  · exact cutSweepQ_bijOn hodd hq hTW

/-! ## 10. The start sweep at every Order -/

/-- The flip around the end of a word is the reversed word. -/
theorem peakFlip_length (s : List Bool) : peakFlip s s.length = s.reverse := by
  unfold peakFlip
  rw [List.take_length, List.drop_length, List.reverse_nil, List.append_nil]

/-- The start sweep of a word is the sweep of the reversed word. -/
theorem startSweepQ_eq_sweepQ_reverse (hodd : Odd q) (hq0 : 0 < q) (s : List Bool) :
    startSweepQ q s = sweepQ q s.reverse := by
  rw [← peakFlip_length s]
  apply startSweepQ_eq_sweepQ_peakFlip hodd hq0 le_rfl
  · intro i j _ hkj hj
    exact absurd hj (Nat.not_lt.mpr hkj)
  · intro i j _ hkj hj
    exact absurd hj (Nat.not_lt.mpr hkj)

/-- A word of Order n whose endpoint levels are all below 1 sorts like its integer
    sweep. -/
theorem sweepIdxQ_eq_of_lt_one (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {t : List Bool} (hord : order t = n)
    (hlt : ∀ m, 1 ≤ m → m ≤ t.length → lvlQ q t m < 1) :
    sweepIdxQ q t = sweepIdxZ (c - d) (-d) t := by
  have hmemZ : ∀ {i}, i ∈ sweepIdxZ (c - d) (-d) t → i < t.length := by
    intro i hi
    rw [(sweepIdxZ_perm _ _ t).mem_iff, List.mem_range] at hi
    exact hi
  have hneg : ∀ {m}, 1 ≤ m → m ≤ t.length → lvlZ (c - d) (-d) t m < 0 := by
    intro m hm1 hm
    have hiff := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := t) (i := m) (k := 0) hm
      (Nat.zero_le _)
    rw [lvlQ_zero, lvlZ_zero] at hiff
    exact hiff.mp (hlt m hm1 hm)
  apply List.Perm.eq_of_pairwise (le := fun i k => lvlQ q t (k + 1) < lvlQ q t (i + 1))
  · intro a b _ _ hab hba
    exact (lt_asymm hab hba).elim
  · refine ((sweepIdxQ_pairwise q t).and (sweepIdxQ_nodup q t)).imp_of_mem ?_
    intro a b ha hb h
    have ha' := mem_sweepIdxQ.mp ha
    have hb' := mem_sweepIdxQ.mp hb
    exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
  · refine ((sweepIdxZ_pairwise _ _ t).and (sweepIdxZ_nodup _ _ t)).imp_of_mem ?_
    intro a b ha hb h
    have ha' := hmemZ ha
    have hb' := hmemZ hb
    have hna := hneg (m := a + 1) (by omega) (by omega)
    have hnb := hneg (m := b + 1) (by omega) (by omega)
    have hkey := h.1
    unfold twKey at hkey
    have hfa : decide (lvlZ (c - d) (-d) t (a + 1) < 0) = true := by
      simp only [decide_eq_true_eq]
      exact hna
    have hfb : decide (lvlZ (c - d) (-d) t (b + 1) < 0) = true := by
      simp only [decide_eq_true_eq]
      exact hnb
    rw [hfa, hfb, Prod.Lex.toLex_le_toLex] at hkey
    simp only [lt_self_iff_false, true_and, false_or] at hkey
    rw [Prod.Lex.toLex_le_toLex] at hkey
    have hiff := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := t) (i := b + 1) (k := a + 1)
      (by omega) (by omega)
    rcases hkey with hlt' | ⟨heq, _⟩
    · exact hiff.mpr hlt'
    · exfalso
      have hiff' := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := t) (i := a + 1) (k := b + 1)
        (by omega) (by omega)
      have hne := lvlQ_ne_of_ne hodd (s := t) (i := a + 1) (k := b + 1) (by omega) (by omega)
        (by omega)
      rcases lt_or_gt_of_ne hne with h1 | h1
      · have := hiff'.mp h1
        omega
      · have := hiff.mp h1
        omega
  · exact (sweepIdxQ_perm q t).trans (sweepIdxZ_perm (c - d) (-d) t).symm

/-- The sweep of a word of Order n whose endpoint levels are all below 1 is its integer
    sweep. -/
theorem sweepQ_eq_sweepZ_of_lt_one (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ}
    (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {t : List Bool} (hord : order t = n)
    (hlt : ∀ m, 1 ≤ m → m ≤ t.length → lvlQ q t m < 1) :
    sweepQ q t = sweepZ (c - d) (-d) t := by
  unfold sweepQ sweepZ
  rw [sweepIdxQ_eq_of_lt_one hodd hq hd hcd hord hlt]

/-- Every endpoint level of the reverse of an admissible word is below 1. -/
theorem lvlQ_reverse_lt_one (hq0 : 0 < q) {s : List Bool} (hA : AdmissibleQ q s) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ s.length) : lvlQ q s.reverse m < 1 := by
  have h := lvlQ_peakFlip_le (q := q) (s := s) (k := s.length) (m := m) le_rfl hm
  rw [peakFlip_length, lvlQ_length] at h
  have hpos : 0 < lvlQ q s.reverse m := lvlQ_pos hq0 _ _
  have hge : 1 ≤ lvlQ q s (s.length - m) := by
    rcases Nat.eq_zero_or_pos (s.length - m) with h0 | hpos'
    · rw [h0, lvlQ_zero]
    · exact le_of_lt (hA.prefix_gt (s.length - m) hpos' (by omega))
  have hlt := hA.lt_one
  by_contra hx
  push Not at hx
  have hmul := mul_le_mul hx hge zero_le_one (le_of_lt hpos)
  linarith

/-- Under Thomas and Williams, Thm 6.3, the start sweep is one-to-one on the admissible
    words of every Order. -/
theorem startSweepQ_injOn (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) (n : ℕ) :
    Set.InjOn (startSweepQ q) (admSetQ q n : Set (List Bool)) := by
  obtain ⟨c, d, hd, hcd⟩ := exists_weightsQ hq n
  have hq0 : 0 < q := by omega
  have key : ∀ {s : List Bool}, s ∈ admSetQ q n →
      startSweepQ q s = sweepZ (c - d) (-d) s.reverse ∧
        s.reverse ∈ contentSet n (p2Q q n - n) := by
    intro s hs
    obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
    have hordr : order s.reverse = n := by
      rw [order_perm (List.reverse_perm s), hord]
    have hlt : ∀ m, 1 ≤ m → m ≤ s.reverse.length → lvlQ q s.reverse m < 1 := by
      intro m hm1 hm
      rw [List.length_reverse] at hm
      exact lvlQ_reverse_lt_one hq0 hA hm1 hm
    refine ⟨?_, ?_, ?_⟩
    · rw [startSweepQ_eq_sweepQ_reverse hodd hq0,
        sweepQ_eq_sweepZ_of_lt_one hodd hq hd hcd hordr hlt]
    · rw [← order_eq_count_true, hordr]
    · have hc := count_true_add_count_false s.reverse
      have hl := admissibleQ_length (by omega) hA
      rw [← order_eq_count_true, hordr, List.length_reverse, hl, hord] at hc
      omega
  intro s hs s' hs' heq
  obtain ⟨h1, hm1⟩ := key hs
  obtain ⟨h2, hm2⟩ := key hs'
  rw [h1, h2] at heq
  exact List.reverse_injective ((hTW (c - d) (-d) n (p2Q q n - n)).injOn hm1 hm2 heq)

end SweepQ
