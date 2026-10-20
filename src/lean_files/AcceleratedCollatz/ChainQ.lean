-- SPDX-License-Identifier: MIT
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The chain decomposition of the q-family (odd q ≥ 3), its record Orders and its first words

Self-contained extract of the AcceleratedCollatz Lean 4 project; depends on
Mathlib only.

A word is a `List Bool` (`true` = factor q/2, `false` = factor 1/2); its level
after j steps is the product of the first j factors (`seqProductQ`, exact
rationals). `AdmissibleQ q s`: the level stays > 1 on every proper nonempty prefix
and ends < 1. `order s` = the number of 1s; an admissible word of Order n has
length `p2Q q n = Nat.log 2 (q ^ n) + 1` (`admissibleQ_length`). The block factor
of Order o is q^o / 2^p2Q(o) (`blockFactorQ`). `UpperRecordQ q n`: the block factor
of n is above that of every Order from 1 to n - 1; `LowerRecordQ q n`: below
(`upperRecordQ_iff_blockFactorQ`, `lowerRecordQ_iff_blockFactorQ`; the definitions
compare p2Q(n)/n and (p2Q(n) - 1)/n, in integers). Orders 0 and 1 are records of
both kinds.

Sections:
1. Words and Order.
2. The q-family: levels, `AdmissibleQ`, `p2Q`, `admissibleQ_length`.
3. Record Orders by the block factor (`upperRecordQ_iff_blockFactorQ`,
   `lowerRecordQ_iff_blockFactorQ`).
4. Gaps of the record Orders: the gap between two neighbouring lower record Orders
   is an upper record Order (`upperRecordQ_sub_of_lowerRecordQ`), the gap between
   two neighbouring upper record Orders is a lower record Order
   (`lowerRecordQ_sub_of_upperRecordQ`).
5. The split: an admissible word of Order ≥ 1 is 1 :: (B1 ++ ... ++ Bm) with
   admissible blocks, in one way (`exists_splitQ`, `splitQ_unique`).
6. The chain form depends on the Orders of the blocks only
   (`admissibleQ_iff_chainQ`, `admissibleQ_iff_exists_chainQ`).
7. Record lows: the blocks are cut at the strict record lows of the level
   (`isRecordLowQ_iff_cut`).
8. The first word of each Order (`firstWordQ`): admissible (`firstWordQ_mem`),
   the least admissible word of its Order (`firstWordQ_le`), and lower than at
   every earlier point exactly at the lower record Orders (`firstWordQ_low_iff`,
   `firstWordQ_blocks`).
9. The first word as a chain (`firstWordQ_chain`): every block is the first word
   of its Order, and the Orders read before the blocks are exactly the lower record
   Orders from 1 to n.
10. The Orders of its blocks: every block but the last has an upper record Order
   (`upperRecordQ_order_of_firstWordQ`). The last block is [0] when n is a lower
   record Order; otherwise its Order is n minus the last lower record Order below
   n, which need not be a record Order (q = 3, n = 4: the blocks have Orders 1, 2).
11. The chain as an equivalence: the admissible words of Order n + 1 correspond to
   the block lists `chainBlocksQ q n` (`chainEquivQ`) and to the lists of their
   (d, c) codes, Order and index in the sorted list of that Order (`codeEquivQ`).
12. The count by chains: |admSetQ q (n+1)| is the sum, over the Order lists of the
   chains, of the products of the counts of the Orders (`card_admSetQ_succ`).
13. The deficit budget: with D(o) = 2^p2Q(o) / q^o in (1, 2], the level after a
   leading 1 and blocks of Orders os is above 1 iff 2 ∏ D(o_i) < q
   (`levelUpQ_iff_budgetQ`, `admissibleQ_iff_exists_chain_budgetQ`).
-/

namespace ChainQ

variable {q : ℕ}

/-! ## 1. Words and Order -/

/-- Order: count of tripling (true) entries. -/
def order (s : List Bool) : ℕ := (s.filter id).length

/-- Order is additive under concatenation. -/
theorem order_append (a b : List Bool) : order (a ++ b) = order a + order b := by
  simp [order, List.filter_append]

/-- Order of b :: t. -/
theorem order_cons (b : Bool) (t : List Bool) :
    order (b :: t) = order t + (if b then 1 else 0) := by
  grind [order]

theorem order_replicate_false (r : ℕ) : order (List.replicate r false) = 0 := by
  simp [order]

/-- Order of a concatenation of blocks: the sum of the block Orders. -/
theorem order_flatten (bs : List (List Bool)) : order bs.flatten = (bs.map order).sum := by
  induction bs with
  | nil =>
    simp [order]
  | cons b t ih =>
    rw [List.flatten_cons, order_append, ih, List.map_cons, List.sum_cons]

/-- Order of 1 :: blocks: 1 plus the sum of the block Orders. -/
theorem order_cons_flatten (bs : List (List Bool)) :
    order (true :: bs.flatten) = 1 + (bs.map order).sum := by
  grind [order_cons, order_flatten]

/-- All bit lists of length k. -/
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

/-- q/2 for an odd step, 1/2 for a halving. -/
def factorQ (q : ℕ) (b : Bool) : ℚ := if b then (q : ℚ) / 2 else 1 / 2

/-- Product of the factors of a word. -/
def seqProductQ (q : ℕ) (s : List Bool) : ℚ := (s.map (factorQ q)).prod

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

theorem p2Q_zero (q : ℕ) : p2Q q 0 = 1 := by
  simp [p2Q]

/-! ## 3. Record Orders by the block factor -/

theorem p2Q_mono (hq : 3 ≤ q) {i n : ℕ} (h : i ≤ n) : p2Q q i ≤ p2Q q n := by
  unfold p2Q
  have hp : q ^ i ≤ q ^ n := Nat.pow_le_pow_right (by omega) h
  have hl := Nat.log_mono_right (b := 2) hp
  omega

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

/-! ## 4. Gaps of the record Orders -/

/-- Between a lower record Order a and the next one, no block factor is below that of
    a. -/
theorem not_blockFactorQ_lt_of_lowerRecordQ (hq : 3 ≤ q) {a b : ℕ} (hRa : LowerRecordQ q a)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecordQ q x) {x : ℕ} (hax : a < x) (hxb : x < b) :
    ¬blockFactorQ q x < blockFactorQ q a := by
  intro hlt
  have hex : ∃ y, a < y ∧ blockFactorQ q y < blockFactorQ q a := ⟨x, hax, hlt⟩
  have hy := Nat.find_spec hex
  have hyle : Nat.find hex ≤ x := Nat.find_min' hex ⟨hax, hlt⟩
  have hRy : LowerRecordQ q (Nat.find hex) := by
    rw [lowerRecordQ_iff_blockFactorQ hq]
    intro z hz1 hzy
    rcases Nat.lt_or_ge a z with haz | hza
    · have hmin := Nat.find_min hex hzy
      rw [not_and] at hmin
      exact lt_of_lt_of_le hy.2 (not_lt.mp (hmin haz))
    · rcases Nat.eq_or_lt_of_le hza with heq | hlt'
      · rw [heq]
        exact hy.2
      · exact lt_trans hy.2 ((lowerRecordQ_iff_blockFactorQ hq a).mp hRa z hz1 hlt')
  exact hnone (Nat.find hex) hy.1 (by omega) hRy

/-- Between an upper record Order a and the next one, no block factor is above that of
    a. -/
theorem not_blockFactorQ_lt_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {a b : ℕ}
    (hRa : UpperRecordQ q a) (hnone : ∀ x, a < x → x < b → ¬UpperRecordQ q x) {x : ℕ}
    (hax : a < x) (hxb : x < b) : ¬blockFactorQ q a < blockFactorQ q x := by
  intro hlt
  have hex : ∃ y, a < y ∧ blockFactorQ q a < blockFactorQ q y := ⟨x, hax, hlt⟩
  have hy := Nat.find_spec hex
  have hyle : Nat.find hex ≤ x := Nat.find_min' hex ⟨hax, hlt⟩
  have hRy : UpperRecordQ q (Nat.find hex) := by
    rw [upperRecordQ_iff_blockFactorQ hodd hq]
    intro z hz1 hzy
    rcases Nat.lt_or_ge a z with haz | hza
    · have hmin := Nat.find_min hex hzy
      rw [not_and] at hmin
      exact lt_of_le_of_lt (not_lt.mp (hmin haz)) hy.2
    · rcases Nat.eq_or_lt_of_le hza with heq | hlt'
      · rw [heq]
        exact hy.2
      · exact lt_trans ((upperRecordQ_iff_blockFactorQ hodd hq a).mp hRa z hz1 hlt') hy.2
  exact hnone (Nat.find hex) hy.1 (by omega) hRy

/-- Between a lower record Order a and the next one, p2Q(a + i) + 1 = p2Q(a) + p2Q(i). -/
theorem p2Q_add_of_lowerRecordQ (hq : 3 ≤ q) {a b : ℕ} (hRa : LowerRecordQ q a)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecordQ q x) {i : ℕ} (hi : 1 ≤ i) (hib : a + i < b) :
    p2Q q (a + i) + 1 = p2Q q a + p2Q q i := by
  have hle := p2Q_add_le hq a i
  have hle2 := p2Q_add_le_succ hq a i
  have hnot := not_blockFactorQ_lt_of_lowerRecordQ hq hRa hnone (x := a + i) (by omega) hib
  rw [blockFactorQ_add_lt_iff hq] at hnot
  omega

/-- Between an upper record Order a and the next one, p2Q(a + i) = p2Q(a) + p2Q(i). -/
theorem p2Q_add_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {a b : ℕ} (hRa : UpperRecordQ q a)
    (hnone : ∀ x, a < x → x < b → ¬UpperRecordQ q x) {i : ℕ} (hi : 1 ≤ i) (hib : a + i < b) :
    p2Q q (a + i) = p2Q q a + p2Q q i := by
  have hle := p2Q_add_le hq a i
  have hle2 := p2Q_add_le_succ hq a i
  have hnot := not_blockFactorQ_lt_of_upperRecordQ hodd hq hRa hnone (x := a + i) (by omega) hib
  rw [blockFactorQ_lt_add_iff hodd hq a hi] at hnot
  omega

/-- Between two neighbouring lower record Orders a < b the gap b - a is an upper record
    Order. -/
theorem upperRecordQ_sub_of_lowerRecordQ (hq : 3 ≤ q) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hRa : LowerRecordQ q a) (hRb : LowerRecordQ q b)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecordQ q x) : UpperRecordQ q (b - a) := by
  rw [upperRecordQ_iff_add hq]
  intro c hc1 hcg
  have hadd := (lowerRecordQ_iff_add hq b).mp hRb
  have h1 := hadd a ha hab
  have h2 := hadd (a + c) (by omega) (by omega)
  rw [Nat.sub_add_eq] at h2
  have h3 := p2Q_add_of_lowerRecordQ hq hRa hnone hc1 (by omega)
  omega

/-- Between two neighbouring upper record Orders a < b the gap b - a is a lower record
    Order. -/
theorem lowerRecordQ_sub_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) (hRa : UpperRecordQ q a) (hRb : UpperRecordQ q b)
    (hnone : ∀ x, a < x → x < b → ¬UpperRecordQ q x) : LowerRecordQ q (b - a) := by
  rw [lowerRecordQ_iff_add hq]
  intro c hc1 hcg
  have hadd := (upperRecordQ_iff_add hq b).mp hRb
  have h1 := hadd a ha hab
  have h2 := hadd (a + c) (by omega) (by omega)
  rw [Nat.sub_add_eq] at h2
  have h3 := p2Q_add_of_upperRecordQ hodd hq hRa hnone hc1 (by omega)
  omega

/-! ## 5. The split -/

/-- The empty word is not admissible. -/
theorem not_admissibleQ_nil (q : ℕ) : ¬AdmissibleQ q [] := by
  intro h
  have h1 := h.lt_one
  simp [seqProductQ] at h1

/-- [0] is admissible (Order 0). -/
theorem admissibleQ_singleton_false (q : ℕ) : AdmissibleQ q [false] := by
  refine ⟨?_, ?_⟩
  · intro m hm hml
    rw [List.length_singleton] at hml
    omega
  · norm_num [seqProductQ, factorQ]

/-- An admissible word is nonempty. -/
theorem ne_nil_of_admissibleQ {b : List Bool} (h : AdmissibleQ q b) : b ≠ [] := by
  intro hn
  rw [hn] at h
  exact not_admissibleQ_nil q h

/-- The level of a word is above 1 exactly when 2^length < q^Order. -/
theorem one_lt_seqProductQ_iff (q : ℕ) (s : List Bool) :
    1 < seqProductQ q s ↔ 2 ^ s.length < q ^ order s := by
  have h := seqProductQ_mul_pow q s
  have hpos : (0 : ℚ) < 2 ^ s.length := by positivity
  constructor
  · intro h1
    have h2 := mul_lt_mul_of_pos_right h1 hpos
    rw [one_mul, h] at h2
    exact_mod_cast h2
  · intro h1
    have h2 : (2 : ℚ) ^ s.length < (q : ℚ) ^ order s := by
      exact_mod_cast h1
    by_contra hle
    push Not at hle
    have h3 := mul_le_mul_of_nonneg_right hle hpos.le
    linarith

/-- For odd q ≥ 3 the level of a nonempty word is not 1. -/
theorem seqProductQ_ne_one (hodd : Odd q) (hq : 3 ≤ q) {s : List Bool} (hs : s ≠ []) :
    seqProductQ q s ≠ 1 := by
  intro h
  have hmul := seqProductQ_mul_pow q s
  rw [h, one_mul] at hmul
  have hnat : 2 ^ s.length = q ^ order s := by
    exact_mod_cast hmul
  have hlen : 1 ≤ s.length := List.length_pos_iff.mpr hs
  rcases Nat.eq_zero_or_pos (order s) with h0 | hpos
  · have h2 : 2 ^ 1 ≤ 2 ^ s.length := Nat.pow_le_pow_right (by norm_num) hlen
    rw [h0, pow_zero] at hnat
    rw [pow_one, hnat] at h2
    omega
  · exact two_pow_ne_q_pow hodd hq hpos hnat

/-- An admissible word is not a proper prefix of another one. -/
theorem admissibleQ_not_prefix {a b : List Bool} (ha : AdmissibleQ q a)
    (hb : AdmissibleQ q b) (hne : a ≠ b) : ¬a <+: b := by
  rintro ⟨c, rfl⟩
  have hc : c ≠ [] := by
    intro hc
    apply hne
    rw [hc, List.append_nil]
  have hlen : a.length < (a ++ c).length := by
    have hcl := List.length_pos_iff.mpr hc
    rw [List.length_append]
    omega
  have h1 := hb.prefix_gt a.length (List.length_pos_iff.mpr (ne_nil_of_admissibleQ ha)) hlen
  rw [List.take_left' rfl] at h1
  have h2 := ha.lt_one
  linarith

/-- An admissible word of Order ≥ 1 starts with an odd step. -/
theorem admissibleQ_cons_true {s : List Bool} (hA : AdmissibleQ q s) (hord : 1 ≤ order s) :
    ∃ u, s = true :: u := by
  cases s with
  | nil => exact absurd hA (not_admissibleQ_nil q)
  | cons b u =>
    cases b with
    | true => exact ⟨u, rfl⟩
    | false =>
      exfalso
      cases u with
      | nil => simp [order] at hord
      | cons c v =>
        have h := hA.prefix_gt 1 le_rfl (by simp)
        norm_num [seqProductQ, factorQ] at h

/-- s = 1 :: flatten bs with admissible blocks. -/
structure IsSplitQ (q : ℕ) (s : List Bool) (bs : List (List Bool)) : Prop where
  /-- s is 1 followed by the blocks. -/
  eq : s = true :: bs.flatten
  /-- Every block is admissible. -/
  adm : ∀ b ∈ bs, AdmissibleQ q b

/-- A factorization into admissible blocks is unique. -/
theorem flatten_inj_of_admissibleQ :
    ∀ (bs bs' : List (List Bool)), (∀ b ∈ bs, AdmissibleQ q b) →
      (∀ b ∈ bs', AdmissibleQ q b) → bs.flatten = bs'.flatten → bs = bs' := by
  intro bs
  induction bs with
  | nil =>
    intro bs' _ h' heq
    cases bs' with
    | nil =>
      rfl
    | cons b' t' =>
      have hne := ne_nil_of_admissibleQ (h' b' (by simp))
      simp only [List.flatten_nil, List.flatten_cons] at heq
      exact absurd (List.append_eq_nil_iff.mp heq.symm).1 hne
  | cons b t ih =>
    intro bs' h h' heq
    have hb := h b (by simp)
    have hbne := ne_nil_of_admissibleQ hb
    cases bs' with
    | nil =>
      simp only [List.flatten_nil, List.flatten_cons] at heq
      exact absurd (List.append_eq_nil_iff.mp heq).1 hbne
    | cons b' t' =>
      have hb' := h' b' (by simp)
      simp only [List.flatten_cons] at heq
      have hbb : b = b' := by
        by_contra hne
        rcases List.append_eq_append_iff.mp heq with ⟨a', hb'eq, _⟩ | ⟨c', hbeq, _⟩
        · exact admissibleQ_not_prefix hb hb' hne ⟨a', hb'eq.symm⟩
        · exact admissibleQ_not_prefix hb' hb (Ne.symm hne) ⟨c', hbeq.symm⟩
      subst hbb
      have htt := List.append_cancel_left heq
      rw [ih t' (fun c hc => h c (by simp [hc])) (fun c hc => h' c (by simp [hc])) htt]

/-- Factorization of the remainder r of an admissible P ++ r (P ≠ []). -/
theorem exists_blocksQ (hodd : Odd q) (hq : 3 ≤ q) : ∀ (n : ℕ) (P r : List Bool),
    r.length = n → AdmissibleQ q (P ++ r) → P ≠ [] →
    ∃ bs : List (List Bool), r = bs.flatten ∧ ∀ b ∈ bs, AdmissibleQ q b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P r hn hA hP
    by_cases hr0 : r = []
    · exact ⟨[], by simp [hr0], by simp⟩
    · have hPlen : 1 ≤ P.length := List.length_pos_iff.mpr hP
      have hrlen : 1 ≤ r.length := List.length_pos_iff.mpr hr0
      have hPlt : P.length < (P ++ r).length := by
        rw [List.length_append]
        omega
      have hpre := hA.prefix_gt P.length hPlen hPlt
      rw [List.take_left' rfl] at hpre
      have hfull := hA.lt_one
      rw [seqProductQ_append] at hfull
      have hr1 : seqProductQ q r < 1 := by
        by_contra hge
        push Not at hge
        have := one_lt_mul_of_lt_of_le hpre hge
        linarith
      have hex : ∃ m, 1 ≤ m ∧ m ≤ r.length ∧ seqProductQ q (r.take m) < 1 :=
        ⟨r.length, hrlen, le_rfl, by rwa [List.take_length]⟩
      obtain ⟨hm1, hmle, hmlt⟩ := Nat.find_spec hex
      have hlen : (r.take (Nat.find hex)).length = Nat.find hex := by
        rw [List.length_take]
        exact min_eq_left hmle
      have hbA : AdmissibleQ q (r.take (Nat.find hex)) := by
        refine ⟨?_, hmlt⟩
        intro k hk1 hk
        rw [hlen] at hk
        rw [List.take_take, min_eq_left hk.le]
        have hmin := Nat.find_min hex hk
        push Not at hmin
        have hge := hmin hk1 (by omega)
        have hkl : 0 < (r.take k).length := by
          rw [List.length_take]
          omega
        have hne := seqProductQ_ne_one hodd hq (List.ne_nil_of_length_pos hkl)
        exact lt_of_le_of_ne hge (Ne.symm hne)
      have hsplit : P ++ r = (P ++ r.take (Nat.find hex)) ++ r.drop (Nat.find hex) := by
        rw [List.append_assoc, List.take_append_drop]
      have hA' : AdmissibleQ q ((P ++ r.take (Nat.find hex)) ++ r.drop (Nat.find hex)) := by
        rw [← hsplit]
        exact hA
      have hlt : (r.drop (Nat.find hex)).length < n := by
        rw [List.length_drop]
        omega
      obtain ⟨bs, hbs, hbsA⟩ := ih _ hlt (P ++ r.take (Nat.find hex)) (r.drop (Nat.find hex))
        rfl hA' (by simp [hP])
      refine ⟨r.take (Nat.find hex) :: bs, ?_, ?_⟩
      · rw [List.flatten_cons, ← hbs, List.take_append_drop]
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hbA
        · exact hbsA b hb'

/-- Every admissible s of Order ≥ 1 splits into admissible blocks. -/
theorem exists_splitQ (hodd : Odd q) (hq : 3 ≤ q) {s : List Bool} (hA : AdmissibleQ q s)
    (hord : 1 ≤ order s) : ∃ bs, IsSplitQ q s bs := by
  obtain ⟨u, rfl⟩ := admissibleQ_cons_true hA hord
  obtain ⟨bs, hbs, hbsA⟩ := exists_blocksQ hodd hq u.length [true] u rfl hA (by simp)
  exact ⟨bs, by rw [← hbs], hbsA⟩

/-- The split is unique. -/
theorem splitQ_unique {s : List Bool} {bs bs' : List (List Bool)} (h : IsSplitQ q s bs)
    (h' : IsSplitQ q s bs') : bs = bs' := by
  apply flatten_inj_of_admissibleQ bs bs' h.adm h'.adm
  have heq := h.eq.symm.trans h'.eq
  simpa using heq

theorem order_splitQ {s : List Bool} {bs : List (List Bool)} (h : IsSplitQ q s bs) :
    order s = (bs.map order).sum + 1 := by
  rw [h.eq, order_cons, order_flatten]
  simp

/-! ### The converse -/

/-- Levels > 1 at the start and at inner boundaries give levels > 1 at every
    position inside the blocks. -/
theorem one_lt_seqProductQ_take_flatten :
    ∀ (bs : List (List Bool)) (P : List Bool), (∀ b ∈ bs, AdmissibleQ q b) →
      1 < seqProductQ q P →
      (∀ i, 1 ≤ i → i < bs.length → 1 < seqProductQ q (P ++ (bs.take i).flatten)) →
      ∀ k < bs.flatten.length, 1 < seqProductQ q (P ++ bs.flatten.take k)
  | [], _, _, _, _, k, hk => by
    simp at hk
  | b :: t, P, hbs, hP, hlev, k, hk => by
    have hbA : AdmissibleQ q b := hbs b List.mem_cons_self
    rw [List.flatten_cons, List.take_append]
    by_cases hkb : k < b.length
    · have hdrop : k - b.length = 0 := by omega
      rw [hdrop, List.take_zero, List.append_nil]
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simpa using hP
      · rw [seqProductQ_append]
        have hb := hbA.prefix_gt k hkpos hkb
        exact one_lt_mul_of_lt_of_le hP hb.le
    · have htake : b.take k = b := List.take_of_length_le (by omega)
      rw [htake, ← List.append_assoc]
      rw [List.flatten_cons, List.length_append] at hk
      have htne : t ≠ [] := by
        intro hn
        rw [hn] at hk
        simp at hk
        omega
      have hPb : 1 < seqProductQ q (P ++ b) := by
        have h1 := hlev 1 le_rfl (by simp [List.length_pos_iff.mpr htne])
        simpa using h1
      apply one_lt_seqProductQ_take_flatten t (P ++ b) (fun c hc => hbs c (by simp [hc])) hPb
      · intro i hi hit
        have hlt : i + 1 < (b :: t).length := by
          rw [List.length_cons]
          omega
        have h := hlev (i + 1) (by omega) hlt
        simpa [List.take_succ_cons, List.append_assoc] using h
      · omega

/-- Admissibility of 1 :: (B1 ++ ... ++ Bm) is decided at the block boundaries. -/
theorem admissibleQ_split_iff (hq : 3 ≤ q) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    AdmissibleQ q (true :: bs.flatten) ↔
      (∀ i, 1 ≤ i → i < bs.length → 1 < seqProductQ q (true :: (bs.take i).flatten)) ∧
        seqProductQ q (true :: bs.flatten) < 1 := by
  constructor
  · intro hA
    refine ⟨?_, hA.lt_one⟩
    intro i hi hil
    have hsplit : bs.flatten = (bs.take i).flatten ++ (bs.drop i).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    have hdne : (bs.drop i).flatten ≠ [] := by
      have hne : bs.drop i ≠ [] := by
        rw [ne_eq, List.drop_eq_nil_iff]
        omega
      obtain ⟨c, hc⟩ : ∃ c, c ∈ bs.drop i := ⟨(bs.drop i).head hne, List.head_mem _⟩
      have hcA := hbs c (List.mem_of_mem_drop hc)
      intro hn
      rw [List.flatten_eq_nil_iff] at hn
      exact ne_nil_of_admissibleQ hcA (hn c hc)
    have hm := hA.prefix_gt ((bs.take i).flatten.length + 1) (by omega) (by
      rw [List.length_cons, hsplit, List.length_append]
      have := List.length_pos_iff.mpr hdne
      omega)
    rw [hsplit, List.take_succ_cons, List.take_left] at hm
    exact hm
  · rintro ⟨hlev, hlast⟩
    refine ⟨?_, hlast⟩
    intro m hm1 hml
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm1
    rw [List.take_succ_cons]
    have hk : k < bs.flatten.length := by
      simp only [List.length_cons] at hml
      omega
    have h1 : 1 < seqProductQ q [true] := by
      have hq' : (3 : ℚ) ≤ q := by
        exact_mod_cast hq
      have he : seqProductQ q [true] = (q : ℚ) / 2 := by
        simp [seqProductQ, factorQ]
      rw [he]
      linarith
    have h := one_lt_seqProductQ_take_flatten bs [true] hbs h1 (by simpa using hlev) k hk
    simpa using h

/-! ## 6. The chain form -/

/-- Level after a leading 1 and blocks of Orders os is above 1. -/
def LevelUpQ (q : ℕ) (os : List ℕ) : Prop :=
  2 ^ (1 + (os.map (p2Q q)).sum) < q ^ (1 + os.sum)

/-- `LevelUpQ` is decidable. -/
instance (q : ℕ) (os : List ℕ) : Decidable (LevelUpQ q os) := by
  unfold LevelUpQ
  infer_instance

/-- After the leading 1 alone the level is above 1. -/
theorem levelUpQ_nil (hq : 3 ≤ q) : LevelUpQ q [] := by
  change 2 ^ (1 + 0) < q ^ (1 + 0)
  rw [Nat.add_zero, pow_one, pow_one]
  omega

/-- q^(Σ o) ≤ 2^(Σ p2Q(o)). -/
theorem q_pow_sum_le (hq : 3 ≤ q) (os : List ℕ) : q ^ os.sum ≤ 2 ^ (os.map (p2Q q)).sum := by
  induction os with
  | nil =>
    simp
  | cons o os ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, pow_add, pow_add]
    exact Nat.mul_le_mul (p2Q_spec hq o).le ih

/-- A block lowers the level: `LevelUpQ` of a list gives `LevelUpQ` of a beginning. -/
theorem levelUpQ_of_append (hq : 3 ≤ q) (a b : List ℕ) (h : LevelUpQ q (a ++ b)) :
    LevelUpQ q a := by
  unfold LevelUpQ at h ⊢
  rw [List.map_append, List.sum_append, List.sum_append, ← add_assoc, ← add_assoc,
    pow_add 2 (1 + (a.map (p2Q q)).sum), pow_add q (1 + a.sum)] at h
  have hb := q_pow_sum_le hq b
  by_contra hcon
  have hge : q ^ (1 + a.sum) ≤ 2 ^ (1 + (a.map (p2Q q)).sum) := Nat.le_of_not_lt hcon
  exact absurd h (not_lt.mpr (Nat.mul_le_mul hge hb))

theorem levelUpQ_take (hq : 3 ≤ q) {os : List ℕ} (h : LevelUpQ q os) (i : ℕ) :
    LevelUpQ q (os.take i) := by
  apply levelUpQ_of_append hq (os.take i) (os.drop i)
  rw [List.take_append_drop]
  exact h

/-- Length of a concatenation of admissible blocks, from their Orders. -/
theorem length_flatten_admQ (hq : 3 ≤ q) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    bs.flatten.length = ((bs.map order).map (p2Q q)).sum := by
  induction bs with
  | nil =>
    simp
  | cons b t ih =>
    rw [List.flatten_cons, List.length_append, List.map_cons, List.map_cons, List.sum_cons,
      admissibleQ_length (by omega) (hbs b List.mem_cons_self),
      ih (fun c hc => hbs c (List.mem_cons_of_mem b hc))]

/-- The level after 1 :: blocks is above 1 iff `LevelUpQ` holds for their Orders. -/
theorem one_lt_levelQ_iff (hq : 3 ≤ q) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    1 < seqProductQ q (true :: bs.flatten) ↔ LevelUpQ q (bs.map order) := by
  rw [one_lt_seqProductQ_iff, order_cons_flatten, List.length_cons,
    length_flatten_admQ hq bs hbs, LevelUpQ, Nat.add_comm _ 1]

/-- For odd q the level after 1 :: blocks is below 1 iff `LevelUpQ` fails for their
    Orders. -/
theorem levelQ_lt_one_iff (hodd : Odd q) (hq : 3 ≤ q) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    seqProductQ q (true :: bs.flatten) < 1 ↔ ¬LevelUpQ q (bs.map order) := by
  rw [← one_lt_levelQ_iff hq bs hbs]
  have hne := seqProductQ_ne_one hodd hq (s := true :: bs.flatten) (List.cons_ne_nil _ _)
  constructor
  · intro h hgt
    linarith
  · intro h
    exact lt_of_le_of_ne (not_lt.mp h) hne

/-- Chain form: for admissible blocks, 1 :: (B1 ++ ... ++ Bm) is admissible iff the level
    is above 1 before the last block and below 1 after it; both depend on the Orders of
    the blocks only. -/
theorem admissibleQ_iff_chainQ (hodd : Odd q) (hq : 3 ≤ q) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, AdmissibleQ q b) :
    AdmissibleQ q (true :: bs.flatten) ↔
      LevelUpQ q (bs.map order).dropLast ∧ ¬LevelUpQ q (bs.map order) := by
  rw [admissibleQ_split_iff hq bs hbs, levelQ_lt_one_iff hodd hq bs hbs]
  have htake : ∀ i, ∀ b ∈ bs.take i, AdmissibleQ q b :=
    fun i b hb => hbs b (List.mem_of_mem_take hb)
  constructor
  · rintro ⟨hlev, hend⟩
    refine ⟨?_, hend⟩
    rcases Nat.lt_or_ge bs.length 2 with hlen | hlen
    · have hd : (bs.map order).dropLast = [] := by
        rw [← List.length_eq_zero_iff, List.length_dropLast, List.length_map]
        omega
      rw [hd]
      exact levelUpQ_nil hq
    · have h := hlev (bs.length - 1) (by omega) (by omega)
      rw [one_lt_levelQ_iff hq _ (htake _), List.map_take] at h
      rw [List.dropLast_eq_take, List.length_map]
      exact h
  · rintro ⟨hup, hend⟩
    refine ⟨?_, hend⟩
    intro i hi hil
    rw [one_lt_levelQ_iff hq _ (htake i), List.map_take]
    have h := levelUpQ_take hq hup i
    rw [List.dropLast_eq_take, List.take_take, List.length_map, min_eq_left (by omega)] at h
    exact h

/-- The chain decomposition of the q-family: the admissible words of Order ≥ 1 are
    exactly the words 1 :: (B1 ++ ... ++ Bm) with admissible blocks whose Orders keep the
    level above 1 before the last block and bring it below 1 after it. -/
theorem admissibleQ_iff_exists_chainQ (hodd : Odd q) (hq : 3 ≤ q) (s : List Bool) :
    (AdmissibleQ q s ∧ 1 ≤ order s) ↔
      ∃ bs, IsSplitQ q s bs ∧
        LevelUpQ q (bs.map order).dropLast ∧ ¬LevelUpQ q (bs.map order) := by
  constructor
  · rintro ⟨hA, hord⟩
    obtain ⟨bs, hbs⟩ := exists_splitQ hodd hq hA hord
    rw [hbs.eq] at hA
    exact ⟨bs, hbs, (admissibleQ_iff_chainQ hodd hq bs hbs.adm).mp hA⟩
  · rintro ⟨bs, hbs, hchain⟩
    refine ⟨?_, ?_⟩
    · rw [hbs.eq]
      exact (admissibleQ_iff_chainQ hodd hq bs hbs.adm).mpr hchain
    · rw [order_splitQ hbs]
      omega

/-! ## 7. Record lows -/

/-- m is a strict record-low time of s: the level after m letters is below every
    earlier level. -/
def IsRecordLowQ (q : ℕ) (s : List Bool) (m : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ s.length ∧
    ∀ j, 1 ≤ j → j < m → seqProductQ q (s.take m) < seqProductQ q (s.take j)

/-- The level at the end of w is at most every level along w. -/
def EndIsMinQ (q : ℕ) (w : List Bool) : Prop :=
  ∀ j, 1 ≤ j → j ≤ w.length → seqProductQ q w ≤ seqProductQ q (w.take j)

/-- Inside an appended admissible block the level stays above the block's start. -/
theorem seqProductQ_lt_inside (hq0 : 0 < q) (w b : List Bool) (r : ℕ)
    (hb : AdmissibleQ q b) (hr1 : 1 ≤ r) (hr : r < b.length) :
    seqProductQ q w < seqProductQ q ((w ++ b).take (w.length + r)) := by
  rw [List.take_length_add_append, seqProductQ_append]
  exact lt_mul_of_one_lt_right (seqProductQ_pos hq0 w) (hb.prefix_gt r hr1 hr)

/-- At the end of an appended admissible block the level is below the block's start. -/
theorem seqProductQ_append_lt (hq0 : 0 < q) (w b : List Bool) (hb : AdmissibleQ q b) :
    seqProductQ q (w ++ b) < seqProductQ q w := by
  rw [seqProductQ_append]
  exact mul_lt_of_lt_one_right (seqProductQ_pos hq0 w) hb.lt_one

/-- After an appended admissible block, the level ends at its minimum again. -/
theorem endIsMinQ_append (hq0 : 0 < q) (w b : List Bool) (hQ : EndIsMinQ q w)
    (hb : AdmissibleQ q b) : EndIsMinQ q (w ++ b) := by
  intro j hj1 hj
  rw [List.length_append] at hj
  have hend := seqProductQ_append_lt hq0 w b hb
  rcases Nat.lt_or_ge w.length j with hgt | hle
  · rcases Nat.lt_or_ge j (w.length + b.length) with hlt | hge
    · obtain ⟨r, rfl⟩ : ∃ r, j = w.length + r := ⟨j - w.length, by omega⟩
      have h := seqProductQ_lt_inside hq0 w b r hb (by omega) (by omega)
      linarith
    · have hj' : j = (w ++ b).length := by
        rw [List.length_append]
        omega
      rw [hj', List.take_length]
  · rw [List.take_append_of_le_length hle]
    linarith [hQ j hj1 hle]

/-- Appending an admissible block adds exactly one record low, at its end. -/
theorem isRecordLowQ_append (hq0 : 0 < q) (w b : List Bool) (hw : w ≠ [])
    (hQ : EndIsMinQ q w) (hb : AdmissibleQ q b) (m : ℕ) :
    IsRecordLowQ q (w ++ b) m ↔ IsRecordLowQ q w m ∨ m = w.length + b.length := by
  have hwpos : 1 ≤ w.length := List.length_pos_iff.mpr hw
  have hend := seqProductQ_append_lt hq0 w b hb
  constructor
  · rintro ⟨hm1, hmle, hlow⟩
    rw [List.length_append] at hmle
    rcases Nat.lt_or_ge w.length m with hgt | hle
    · right
      by_contra hne
      obtain ⟨r, rfl⟩ : ∃ r, m = w.length + r := ⟨m - w.length, by omega⟩
      have h1 := hlow w.length hwpos hgt
      rw [List.take_append_of_le_length le_rfl, List.take_length] at h1
      have h2 := seqProductQ_lt_inside hq0 w b r hb (by omega) (by omega)
      linarith
    · left
      refine ⟨hm1, hle, ?_⟩
      intro j hj1 hjm
      have h := hlow j hj1 hjm
      rwa [List.take_append_of_le_length hle, List.take_append_of_le_length (by omega)] at h
  · rintro (⟨hm1, hmle, hlow⟩ | rfl)
    · have hlen : m ≤ (w ++ b).length := by
        rw [List.length_append]
        omega
      refine ⟨hm1, hlen, ?_⟩
      intro j hj1 hjm
      rw [List.take_append_of_le_length hmle, List.take_append_of_le_length (by omega)]
      exact hlow j hj1 hjm
    · have hlen : w.length + b.length = (w ++ b).length := by
        rw [List.length_append]
      refine ⟨by omega, le_of_eq hlen, ?_⟩
      intro j hj1 hj
      rw [hlen, List.take_length]
      rcases Nat.lt_or_ge w.length j with hgt | hle
      · obtain ⟨r, rfl⟩ : ∃ r, j = w.length + r := ⟨j - w.length, by omega⟩
        have h := seqProductQ_lt_inside hq0 w b r hb (by omega) (by omega)
        linarith
      · rw [List.take_append_of_le_length hle]
        linarith [hQ j hj1 hle]

/-- Record lows of w followed by admissible blocks: those of w, and the block ends. -/
theorem isRecordLowQ_append_flatten (hq0 : 0 < q) (cs : List (List Bool))
    (hcs : ∀ c ∈ cs, AdmissibleQ q c) :
    ∀ w : List Bool, w ≠ [] → EndIsMinQ q w → ∀ m,
      (IsRecordLowQ q (w ++ cs.flatten) m ↔
        IsRecordLowQ q w m ∨
          ∃ i, 1 ≤ i ∧ i ≤ cs.length ∧ m = w.length + (cs.take i).flatten.length) := by
  induction cs with
  | nil =>
    intro w _ _ m
    simp
  | cons c cs ih =>
    intro w hw hQ m
    have hc : AdmissibleQ q c := hcs c List.mem_cons_self
    have hcs' : ∀ c' ∈ cs, AdmissibleQ q c' := fun c' h => hcs c' (List.mem_cons_of_mem c h)
    have hwc : w ++ c ≠ [] := by
      simp [hw]
    rw [List.flatten_cons, ← List.append_assoc,
      ih hcs' (w ++ c) hwc (endIsMinQ_append hq0 w c hQ hc) m,
      isRecordLowQ_append hq0 w c hw hQ hc m]
    simp only [List.length_append, List.length_cons]
    constructor
    · rintro ((h | h) | ⟨i, hi1, hi, rfl⟩)
      · exact Or.inl h
      · right
        refine ⟨1, le_rfl, by omega, ?_⟩
        simp [h]
      · right
        refine ⟨i + 1, by omega, by omega, ?_⟩
        simp [List.take_succ_cons, List.flatten_cons, Nat.add_assoc]
    · rintro (h | ⟨i, hi1, hi, rfl⟩)
      · exact Or.inl (Or.inl h)
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rcases Nat.eq_zero_or_pos i' with h0 | hpos
        · left
          right
          simp [h0]
        · right
          refine ⟨i', hpos, by omega, ?_⟩
          simp [List.take_succ_cons, List.flatten_cons, Nat.add_assoc]

/-- The one-letter word [1] has its only record low at 1. -/
theorem isRecordLowQ_single (q m : ℕ) : IsRecordLowQ q [true] m ↔ m = 1 := by
  constructor
  · rintro ⟨hm1, hm, _⟩
    simp at hm
    omega
  · rintro rfl
    refine ⟨le_rfl, by simp, ?_⟩
    intro j hj1 hj
    omega

/-- [1] ends at its minimum level. -/
theorem endIsMinQ_single (q : ℕ) : EndIsMinQ q [true] := by
  intro j hj1 hj
  simp at hj
  have hj' : j = 1 := by
    omega
  rw [hj']
  rfl

/-- The record-low times of 1 :: (B1 ++ ... ++ Bm), with admissible Bi, are the cuts. -/
theorem isRecordLowQ_iff_cut (hq0 : 0 < q) (cs : List (List Bool))
    (hcs : ∀ c ∈ cs, AdmissibleQ q c) (m : ℕ) :
    IsRecordLowQ q (true :: cs.flatten) m ↔
      ∃ i, i ≤ cs.length ∧ m = 1 + (cs.take i).flatten.length := by
  have h := isRecordLowQ_append_flatten hq0 cs hcs [true] (by simp) (endIsMinQ_single q) m
  rw [List.singleton_append] at h
  rw [h, isRecordLowQ_single]
  simp only [List.length_singleton]
  constructor
  · rintro (rfl | ⟨i, _, hi, rfl⟩)
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · left
      simp [h0]
    · right
      exact ⟨i, hpos, hi, rfl⟩

/-- `IsRecordLowQ` is decidable. -/
instance (q : ℕ) (s : List Bool) (m : ℕ) : Decidable (IsRecordLowQ q s m) := by
  unfold IsRecordLowQ
  infer_instance

/-! ## 8. The first word of each Order -/

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

/-! ## 9. The first word as a chain -/

/-- Order 1 is a lower record Order. -/
theorem lowerRecordQ_one (q : ℕ) : LowerRecordQ q 1 := by
  intro a ha1 ha
  omega

/-- The first part of a first word: the first odd step and p2Q(1) - 2 halvings. -/
theorem firstBodyQ_one (q : ℕ) :
    firstBodyQ q 1 = true :: List.replicate (p2Q q 1 - 2) false := by
  have h : firstBodyQ q 1 =
      firstBodyQ q 0 ++ true :: List.replicate (p2Q q 1 - p2Q q 0 - 1) false := rfl
  rw [h, p2Q_zero, Nat.sub_sub]
  rfl

theorem flatten_replicate_false (k : ℕ) :
    (List.replicate k [false]).flatten = List.replicate k false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_succ]
    rfl

/-- Blocks [0] have Orders that sum to 0. -/
theorem sum_map_order_eq_zero {X : List (List Bool)} (h : ∀ b ∈ X, b = [false]) :
    (X.map order).sum = 0 := by
  induction X with
  | nil => rfl
  | cons b X ih =>
    rw [List.map_cons, List.sum_cons, h b List.mem_cons_self,
      ih (fun c hc => h c (List.mem_cons_of_mem b hc))]
    rfl

/-- With blocks [0] in front of the blocks of `FirstBlocksQ`, and at most one behind them,
    present exactly when n is a lower record Order: the Orders read before the blocks are
    the lower record Orders from 1 to n. -/
theorem FirstBlocksQ.cuts_zero {Z cs T : List (List Bool)} {n : ℕ}
    (hcs : FirstBlocksQ q cs n) (hn : 1 ≤ n) (hZ : ∀ b ∈ Z, b = [false])
    (hT : ∀ b ∈ T, b = [false]) (hTlen : T.length ≤ 1) (htail : T ≠ [] ↔ LowerRecordQ q n)
    (a : ℕ) :
    (∃ i, i < (Z ++ (cs ++ T)).length ∧ a = 1 + (((Z ++ (cs ++ T)).take i).map order).sum) ↔
      (1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a) := by
  have hsum := hcs.sum
  constructor
  · rintro ⟨i, hi, ha⟩
    rw [List.length_append, List.length_append] at hi
    rcases Nat.lt_or_ge i Z.length with hiz | hiz
    · rw [List.take_append_of_le_length (le_of_lt hiz),
        sum_map_order_eq_zero (fun b hb => hZ b (List.mem_of_mem_take hb))] at ha
      rw [ha]
      exact ⟨le_rfl, hn, lowerRecordQ_one q⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = Z.length + k := ⟨i - Z.length, by omega⟩
      rw [List.take_length_add_append, List.map_append, List.sum_append,
        sum_map_order_eq_zero hZ] at ha
      rcases Nat.lt_or_ge k cs.length with hk | hk
      · rw [List.take_append_of_le_length (le_of_lt hk)] at ha
        obtain ⟨ha1, han, hR⟩ := (hcs.cuts a).mp ⟨k, hk, by omega⟩
        exact ⟨ha1, by omega, hR⟩
      · obtain ⟨j, rfl⟩ : ∃ j, k = cs.length + j := ⟨k - cs.length, by omega⟩
        rw [List.take_length_add_append, List.map_append, List.sum_append,
          sum_map_order_eq_zero (fun b hb => hT b (List.mem_of_mem_take hb))] at ha
        have hTne : T ≠ [] := by
          intro hnil
          rw [hnil, List.length_nil] at hi
          omega
        have han : a = n := by
          omega
        rw [han]
        exact ⟨hn, le_rfl, htail.mp hTne⟩
  · rintro ⟨ha1, han, hR⟩
    rcases Nat.lt_or_ge a n with hlt | hge
    · obtain ⟨k, hk, hak⟩ := (hcs.cuts a).mpr ⟨ha1, hlt, hR⟩
      refine ⟨Z.length + k, ?_, ?_⟩
      · rw [List.length_append, List.length_append]
        omega
      · rw [List.take_length_add_append, List.take_append_of_le_length (le_of_lt hk),
          List.map_append, List.sum_append, sum_map_order_eq_zero hZ]
        omega
    · have han' : a = n := by
        omega
      rw [han'] at hR
      have hTne := htail.mpr hR
      have hTpos := List.length_pos_iff.mpr hTne
      refine ⟨Z.length + cs.length, ?_, ?_⟩
      · rw [List.length_append, List.length_append]
        omega
      · rw [List.take_length_add_append, List.take_left' rfl, List.map_append,
          List.sum_append, sum_map_order_eq_zero hZ]
        omega

/-- The first word of Order n ≥ 1 as 1 :: (B1 ++ ... ++ Bm): every block is the first word
    of its Order, and the Orders read before the blocks are exactly the lower record
    Orders from 1 to n. -/
theorem firstWordQ_eq_cons_flatten (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ∃ bs : List (List Bool), firstWordQ q n = true :: bs.flatten ∧
      (∀ b ∈ bs, b = firstWordQ q (order b)) ∧ 1 + (bs.map order).sum = n ∧
      ∀ a, (∃ i, i < bs.length ∧ a = 1 + ((bs.take i).map order).sum) ↔
        (1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a) := by
  obtain ⟨cs, t, hs, hcs, htail, ht⟩ := firstWordQ_blocks hq hn
  obtain ⟨Z, hZdef⟩ : ∃ Z : List (List Bool), Z = List.replicate (p2Q q 1 - 2) [false] :=
    ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : List (List Bool), T = t.map (fun _ => [false]) := ⟨_, rfl⟩
  have hZ : ∀ b ∈ Z, b = [false] := by
    intro b hb
    rw [hZdef] at hb
    exact List.eq_of_mem_replicate hb
  have hT : ∀ b ∈ T, b = [false] := by
    intro b hb
    rw [hTdef] at hb
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    rfl
  have hZflat : Z.flatten = List.replicate (p2Q q 1 - 2) false := by
    rw [hZdef, flatten_replicate_false]
  have hTflat : T.flatten = t := by
    rw [hTdef]
    rcases ht with rfl | rfl
    · rfl
    · rfl
  have hTlen : T.length ≤ 1 := by
    rw [hTdef, List.length_map]
    rcases ht with rfl | rfl
    · exact Nat.zero_le 1
    · exact le_rfl
  have hTtail : T ≠ [] ↔ LowerRecordQ q n := by
    rw [← htail, hTdef]
    rcases ht with rfl | rfl
    · simp
    · simp
  refine ⟨Z ++ (cs ++ T), ?_, ?_, ?_, hcs.cuts_zero hn hZ hT hTlen hTtail⟩
  · rw [hs, firstBodyQ_one, List.flatten_append, List.flatten_append, hZflat, hTflat]
    rfl
  · intro b hb
    rcases List.mem_append.mp hb with hb1 | hb2
    · rw [hZ b hb1]
      rfl
    · rcases List.mem_append.mp hb2 with hb3 | hb4
      · exact (hcs.first b hb3).2
      · rw [hT b hb4]
        rfl
  · have hsum := hcs.sum
    rw [List.map_append, List.map_append, List.sum_append, List.sum_append,
      sum_map_order_eq_zero hZ, sum_map_order_eq_zero hT]
    omega

/-- For odd q ≥ 3 the chain of the first word of Order n ≥ 1: every block is the first
    word of its Order, and the Orders read before the blocks are exactly the lower record
    Orders from 1 to n. -/
theorem firstWordQ_chain (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ∃ bs : List (List Bool), IsSplitQ q (firstWordQ q n) bs ∧
      (∀ b ∈ bs, b = firstWordQ q (order b)) ∧
      ∀ a, (∃ i, i < bs.length ∧ a = 1 + ((bs.take i).map order).sum) ↔
        (1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a) := by
  obtain ⟨bs, hs, hfirst, _, hcuts⟩ := firstWordQ_eq_cons_flatten hq hn
  refine ⟨bs, ⟨hs, ?_⟩, hfirst, hcuts⟩
  intro b hb
  rw [hfirst b hb]
  exact firstWordQ_admissibleQ hodd hq (order b)

/-! ## 10. The Orders of the blocks of a first word -/

/-- Order 0 is an upper record Order. -/
theorem upperRecordQ_zero (q : ℕ) : UpperRecordQ q 0 := by
  intro a ha1 ha
  omega

/-- The sum of the first j entries of a list of natural numbers grows with j. -/
theorem sum_take_le_sum_take (l : List ℕ) {j k : ℕ} (h : j ≤ k) :
    (l.take j).sum ≤ (l.take k).sum := by
  induction l generalizing j k with
  | nil =>
    rw [List.take_nil, List.take_nil]
  | cons x l ih =>
    cases j with
    | zero =>
      rw [List.take_zero, List.sum_nil]
      exact Nat.zero_le _
    | succ j =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [List.take_succ_cons, List.take_succ_cons, List.sum_cons, List.sum_cons]
      exact Nat.add_le_add_left (ih (by omega)) x

/-- Blocks for which the Orders read before each block, counted from 1, are exactly the
    lower record Orders from 1 to n: every block but the last has an upper record
    Order. -/
theorem upperRecordQ_order_of_cuts (hq : 3 ≤ q) {bs : List (List Bool)} {n : ℕ}
    (hcuts : ∀ a, (∃ i, i < bs.length ∧ a = 1 + ((bs.take i).map order).sum) ↔
      (1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a))
    {b : List Bool} (hb : b ∈ bs.dropLast) : UpperRecordQ q (order b) := by
  obtain ⟨i, hi, hbi⟩ := List.mem_iff_getElem.mp hb
  rw [List.getElem_dropLast] at hbi
  rw [List.length_dropLast] at hi
  have hi0 : i < bs.length := by
    omega
  have hi1 : i + 1 < bs.length := by
    omega
  have hstep : ((bs.take (i + 1)).map order).sum =
      ((bs.take i).map order).sum + order b := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi0, hbi, List.map_append,
      List.sum_append]
    simp
  obtain ⟨ha1, _, hRa⟩ := (hcuts _).mp ⟨i, hi0, rfl⟩
  obtain ⟨_, hbn, hRb⟩ := (hcuts _).mp ⟨i + 1, hi1, rfl⟩
  rcases Nat.eq_zero_or_pos (order b) with h0 | hpos
  · rw [h0]
    exact upperRecordQ_zero q
  · have hnone : ∀ x, 1 + ((bs.take i).map order).sum < x →
        x < 1 + ((bs.take (i + 1)).map order).sum → ¬LowerRecordQ q x := by
      intro x hax hxb hRx
      obtain ⟨j, _, hxj⟩ := (hcuts x).mpr ⟨by omega, by omega, hRx⟩
      rcases Nat.lt_or_ge i j with hij | hji
      · have hmono := sum_take_le_sum_take (bs.map order) (show i + 1 ≤ j by omega)
        rw [← List.map_take, ← List.map_take] at hmono
        omega
      · have hmono := sum_take_le_sum_take (bs.map order) hji
        rw [← List.map_take, ← List.map_take] at hmono
        omega
    have h := upperRecordQ_sub_of_lowerRecordQ hq ha1 (by omega) hRa hRb hnone
    have heq : 1 + ((bs.take (i + 1)).map order).sum - (1 + ((bs.take i).map order).sum) =
        order b := by
      omega
    rw [heq] at h
    exact h

/-- For odd q ≥ 3, in the chain of the first word of Order n ≥ 1 every block but the last
    has an upper record Order. -/
theorem upperRecordQ_order_of_firstWordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n)
    {bs : List (List Bool)} (hs : IsSplitQ q (firstWordQ q n) bs) {b : List Bool}
    (hb : b ∈ bs.dropLast) : UpperRecordQ q (order b) := by
  obtain ⟨bs', hs', _, hcuts⟩ := firstWordQ_chain hodd hq hn
  rw [splitQ_unique hs hs'] at hb
  exact upperRecordQ_order_of_cuts hq hcuts hb

/-! ## 11. The chain as an equivalence -/

/-- Lists of admissible blocks with Order sum n whose Orders keep the level above 1
    before the last block and bring it below 1 after it. -/
def chainBlocksQ (q n : ℕ) : Set (List (List Bool)) :=
  {bs | (∀ b ∈ bs, AdmissibleQ q b) ∧ LevelUpQ q (bs.map order).dropLast ∧
    ¬LevelUpQ q (bs.map order) ∧ (bs.map order).sum = n}

/-- 1 :: blocks. -/
def chainWordQ (bs : List (List Bool)) : List Bool :=
  true :: bs.flatten

theorem order_chainWordQ (bs : List (List Bool)) :
    order (chainWordQ bs) = 1 + (bs.map order).sum :=
  order_cons_flatten bs

theorem chainWordQ_mem (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {bs : List (List Bool)}
    (h : bs ∈ chainBlocksQ q n) : chainWordQ bs ∈ admSetQ q (n + 1) := by
  obtain ⟨hadm, hup, hend, hsum⟩ := h
  rw [mem_admSetQ (by omega)]
  refine ⟨(admissibleQ_iff_chainQ hodd hq bs hadm).mpr ⟨hup, hend⟩, ?_⟩
  rw [order_chainWordQ, hsum]
  omega

theorem chainWordQ_injOn (q n : ℕ) : Set.InjOn chainWordQ (chainBlocksQ q n) := by
  intro bs hbs bs' hbs' h
  unfold chainWordQ at h
  rw [List.cons.injEq] at h
  exact flatten_inj_of_admissibleQ bs bs' hbs.1 hbs'.1 h.2

theorem chainWordQ_surjOn (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    Set.SurjOn chainWordQ (chainBlocksQ q n) (admSetQ q (n + 1) : Set (List Bool)) := by
  intro s hs
  rw [Finset.mem_coe, mem_admSetQ (by omega)] at hs
  obtain ⟨bs, hsplit, hup, hend⟩ :=
    (admissibleQ_iff_exists_chainQ hodd hq s).mp ⟨hs.1, by omega⟩
  have hord := order_splitQ hsplit
  exact ⟨bs, ⟨hsplit.adm, hup, hend, by omega⟩, hsplit.eq.symm⟩

/-- `chainWordQ` maps `chainBlocksQ q n` one to one onto the admissible words of
    Order n + 1. -/
theorem chainWordQ_bijOn (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    Set.BijOn chainWordQ (chainBlocksQ q n) (admSetQ q (n + 1) : Set (List Bool)) :=
  ⟨fun _ h => chainWordQ_mem hodd hq h, chainWordQ_injOn q n, chainWordQ_surjOn hodd hq n⟩

/-- Chain decomposition: admissible words of Order n + 1 ≃ `chainBlocksQ q n`. -/
noncomputable def chainEquivQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (admSetQ q (n + 1) : Set (List Bool)) ≃ chainBlocksQ q n :=
  (Set.BijOn.equiv chainWordQ (chainWordQ_bijOn hodd hq n)).symm

theorem chainWordQ_chainEquivQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ)
    (s : (admSetQ q (n + 1) : Set (List Bool))) :
    chainWordQ (chainEquivQ hodd hq n s) = s := by
  unfold chainEquivQ
  exact congrArg Subtype.val ((Set.BijOn.equiv chainWordQ _).apply_symm_apply s)

/-- Admissible words of Order d in lexicographic order, indexed from 0. -/
noncomputable def admIndexQ (q d : ℕ) : Fin (admSetQ q d).card ≃o admSetQ q d :=
  (admSetQ q d).orderIsoOfFin rfl

/-- (d, c) code of a block: its Order and its index in that Order's sorted list. -/
noncomputable def blockCodeQ (q : ℕ) (b : List Bool) (hb : b ∈ admSetQ q (order b)) :
    Σ d, Fin (admSetQ q d).card :=
  ⟨order b, (admIndexQ q (order b)).symm ⟨b, hb⟩⟩

/-- Block of a (d, c) code. -/
noncomputable def codeBlockQ (x : Σ d, Fin (admSetQ q d).card) : List Bool :=
  (admIndexQ q x.1 x.2).1

theorem codeBlockQ_mem (x : Σ d, Fin (admSetQ q d).card) : codeBlockQ x ∈ admSetQ q x.1 :=
  (admIndexQ q x.1 x.2).2

theorem order_codeBlockQ (hq : 3 ≤ q) (x : Σ d, Fin (admSetQ q d).card) :
    order (codeBlockQ x) = x.1 :=
  ((mem_admSetQ (by omega) _ _).mp (codeBlockQ_mem x)).2

theorem codeBlockQ_blockCodeQ (b : List Bool) (hb : b ∈ admSetQ q (order b)) :
    codeBlockQ (blockCodeQ q b hb) = b := by
  unfold codeBlockQ blockCodeQ
  rw [OrderIso.apply_symm_apply]

theorem blockCodeQ_codeBlockQ (hq : 3 ≤ q) (x : Σ d, Fin (admSetQ q d).card)
    (hb : codeBlockQ x ∈ admSetQ q (order (codeBlockQ x))) :
    blockCodeQ q (codeBlockQ x) hb = x := by
  obtain ⟨d, i⟩ := x
  have key : ∀ e (h : e = d) (hm : (admIndexQ q d i).1 ∈ admSetQ q e),
      (⟨e, (admIndexQ q e).symm ⟨(admIndexQ q d i).1, hm⟩⟩ : Σ d, Fin (admSetQ q d).card) =
        ⟨d, i⟩ := by
    intro e h hm
    subst h
    simp
  exact key _ (order_codeBlockQ hq ⟨d, i⟩) hb

/-- (d, c) codes of Order n + 1: lists of codes with Order sum n whose Orders keep the
    level above 1 before the last one and bring it below 1 after it. -/
def chainCodesQ (q n : ℕ) : Set (List (Σ d, Fin (admSetQ q d).card)) :=
  {l | LevelUpQ q (l.map Sigma.fst).dropLast ∧ ¬LevelUpQ q (l.map Sigma.fst) ∧
    (l.map Sigma.fst).sum = n}

theorem mem_admSetQ_order (hq : 3 ≤ q) {b : List Bool} (h : AdmissibleQ q b) :
    b ∈ admSetQ q (order b) :=
  (mem_admSetQ (by omega) _ b).mpr ⟨h, rfl⟩

theorem map_fst_pmap_blockCodeQ (bs : List (List Bool))
    (h : ∀ b ∈ bs, b ∈ admSetQ q (order b)) :
    (bs.pmap (blockCodeQ q) h).map Sigma.fst = bs.map order := by
  rw [List.map_pmap]
  exact List.pmap_eq_map _

theorem map_order_map_codeBlockQ (hq : 3 ≤ q) (l : List (Σ d, Fin (admSetQ q d).card)) :
    (l.map codeBlockQ).map order = l.map Sigma.fst := by
  rw [List.map_map]
  exact List.map_congr_left (fun x _ => order_codeBlockQ hq x)

/-- Blocks ≃ their (d, c) codes. -/
noncomputable def chainCodeEquivQ (hq : 3 ≤ q) (n : ℕ) : chainBlocksQ q n ≃ chainCodesQ q n where
  toFun bs := ⟨bs.1.pmap (blockCodeQ q) (fun b hb => mem_admSetQ_order hq (bs.2.1 b hb)), by
    obtain ⟨_, hup, hend, hsum⟩ := bs.2
    refine ⟨?_, ?_, ?_⟩
    · rw [map_fst_pmap_blockCodeQ]
      exact hup
    · rw [map_fst_pmap_blockCodeQ]
      exact hend
    · rw [map_fst_pmap_blockCodeQ]
      exact hsum⟩
  invFun l := ⟨l.1.map codeBlockQ, by
    obtain ⟨hup, hend, hsum⟩ := l.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
      exact ((mem_admSetQ (by omega) _ _).mp (codeBlockQ_mem x)).1
    · rw [map_order_map_codeBlockQ hq]
      exact hup
    · rw [map_order_map_codeBlockQ hq]
      exact hend
    · rw [map_order_map_codeBlockQ hq]
      exact hsum⟩
  left_inv bs := by
    apply Subtype.ext
    simp only [List.map_pmap, codeBlockQ_blockCodeQ]
    exact List.pmap_eq_self.mpr fun _ _ => rfl
  right_inv l := by
    apply Subtype.ext
    simp only [List.pmap_map, blockCodeQ_codeBlockQ hq]
    exact List.pmap_eq_self.mpr fun _ _ => rfl

/-- (d, c) encoding: admissible words of Order n + 1 ≃ `chainCodesQ q n`. -/
noncomputable def codeEquivQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (admSetQ q (n + 1) : Set (List Bool)) ≃ chainCodesQ q n :=
  (chainEquivQ hodd hq n).trans (chainCodeEquivQ hq n)

/-! ## 12. The count by chains -/

/-- Lists of k natural numbers, 0 allowed, with sum n. -/
def weakComps : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | k + 1, n => (List.range (n + 1)).flatMap (fun j => (weakComps k (n - j)).map (List.cons j))

/-- Membership in `weakComps k n`. -/
theorem mem_weakComps : ∀ (k n : ℕ) (os : List ℕ),
    os ∈ weakComps k n ↔ os.length = k ∧ os.sum = n
  | 0, 0, os => by
    simp only [weakComps, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h, _⟩
      exact List.length_eq_zero_iff.mp h
  | 0, n + 1, os => by
    simp only [weakComps, List.not_mem_nil, false_iff]
    rintro ⟨h, hs⟩
    rw [List.length_eq_zero_iff.mp h] at hs
    simp at hs
  | k + 1, n, os => by
    simp only [weakComps, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨j, hj, t, ht, rfl⟩
      rw [mem_weakComps k (n - j) t] at ht
      refine ⟨by rw [List.length_cons, ht.1], ?_⟩
      rw [List.sum_cons, ht.2]
      omega
    · rintro ⟨hlen, hsum⟩
      cases os with
      | nil =>
        simp at hlen
      | cons o t =>
        rw [List.sum_cons] at hsum
        rw [List.length_cons] at hlen
        refine ⟨o, by omega, t, ?_, rfl⟩
        rw [mem_weakComps k (n - o) t]
        exact ⟨by omega, by omega⟩

/-- A list has at most as many entries as the sum of p2Q of its entries. -/
theorem length_le_sum_p2Q (q : ℕ) (os : List ℕ) : os.length ≤ (os.map (p2Q q)).sum := by
  induction os with
  | nil =>
    simp
  | cons o t ih =>
    have h := one_le_p2Q q o
    rw [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- The sum of a list without its last entry is at most the sum of the list. -/
theorem sum_dropLast_le (os : List ℕ) : os.dropLast.sum ≤ os.sum := by
  have h : os.sum = os.dropLast.sum + (os.drop (os.length - 1)).sum := by
    rw [← List.sum_append, List.dropLast_eq_take, List.take_append_drop]
  omega

/-- Orders that keep the level above 1 before the last one: fewer than p2Q(sum + 1)
    of them. -/
theorem length_lt_of_levelUpQ_dropLast (hq : 3 ≤ q) {os : List ℕ}
    (h : LevelUpQ q os.dropLast) : os.length < p2Q q (os.sum + 1) := by
  unfold LevelUpQ at h
  have hsum := sum_dropLast_le os
  have hpow : q ^ (1 + os.dropLast.sum) ≤ q ^ (os.sum + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hspec := p2Q_spec hq (os.sum + 1)
  have hlt : 2 ^ (1 + (os.dropLast.map (p2Q q)).sum) < 2 ^ p2Q q (os.sum + 1) :=
    lt_of_lt_of_le h (le_trans hpow hspec.le)
  have hexp := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have hlen := length_le_sum_p2Q q os.dropLast
  rw [List.length_dropLast] at hlen
  omega

/-- Order lists of the chains of Order n + 1: sum n, the level above 1 before the last
    entry and below 1 after it. -/
def validCompsQ (q n : ℕ) : Finset (List ℕ) :=
  ((List.range (p2Q q (n + 1))).flatMap (fun k => weakComps k n)).toFinset.filter
    (fun os => LevelUpQ q os.dropLast ∧ ¬LevelUpQ q os)

/-- Membership in `validCompsQ q n`. -/
theorem mem_validCompsQ (hq : 3 ≤ q) (n : ℕ) (os : List ℕ) :
    os ∈ validCompsQ q n ↔ os.sum = n ∧ LevelUpQ q os.dropLast ∧ ¬LevelUpQ q os := by
  simp only [validCompsQ, Finset.mem_filter, List.mem_toFinset, List.mem_flatMap,
    List.mem_range, mem_weakComps]
  constructor
  · rintro ⟨⟨k, _, _, hsum⟩, h⟩
    exact ⟨hsum, h⟩
  · rintro ⟨hsum, hup, hend⟩
    refine ⟨⟨os.length, ?_, rfl, hsum⟩, hup, hend⟩
    rw [← hsum]
    exact length_lt_of_levelUpQ_dropLast hq hup

/-- Block lists with Orders os, every block admissible. -/
def blockSetQ (q : ℕ) : List ℕ → Finset (List (List Bool))
  | [] => {[]}
  | o :: os => (admSetQ q o ×ˢ blockSetQ q os).image (fun p => p.1 :: p.2)

/-- Membership in `blockSetQ q os`. -/
theorem mem_blockSetQ (hq : 3 ≤ q) : ∀ (os : List ℕ) (bs : List (List Bool)),
    bs ∈ blockSetQ q os ↔ bs.map order = os ∧ ∀ b ∈ bs, AdmissibleQ q b
  | [], bs => by
    cases bs with
    | nil =>
      simp [blockSetQ]
    | cons b t =>
      simp [blockSetQ]
  | o :: os, bs => by
    simp only [blockSetQ, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨b, t, ⟨hb, ht⟩, rfl⟩
      rw [mem_admSetQ (by omega)] at hb
      rw [mem_blockSetQ hq os t] at ht
      refine ⟨by rw [List.map_cons, hb.2, ht.1], ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hb.1
      · exact ht.2 c hc'
    · rintro ⟨hmap, hadm⟩
      cases bs with
      | nil =>
        simp at hmap
      | cons b t =>
        rw [List.map_cons, List.cons.injEq] at hmap
        refine ⟨b, t, ⟨?_, ?_⟩, rfl⟩
        · rw [mem_admSetQ (by omega)]
          exact ⟨hadm b List.mem_cons_self, hmap.1⟩
        · rw [mem_blockSetQ hq os t]
          exact ⟨hmap.2, fun c hc => hadm c (List.mem_cons_of_mem b hc)⟩

/-- Number of block lists with Orders os: the product of the counts of the Orders. -/
theorem card_blockSetQ (q : ℕ) : ∀ os : List ℕ,
    (blockSetQ q os).card = (os.map (fun o => (admSetQ q o).card)).prod
  | [] => by
    simp [blockSetQ]
  | o :: os => by
    rw [blockSetQ, Finset.card_image_of_injective, Finset.card_product, card_blockSetQ q os,
      List.map_cons, List.prod_cons]
    intro p r h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2

/-- The block lists over `validCompsQ q n` are `chainBlocksQ q n`. -/
theorem mem_sigma_blockSetQ (hq : 3 ≤ q) (n : ℕ) (os : List ℕ) (bs : List (List Bool)) :
    (⟨os, bs⟩ : Σ _ : List ℕ, List (List Bool)) ∈ (validCompsQ q n).sigma (blockSetQ q) ↔
      bs ∈ chainBlocksQ q n ∧ bs.map order = os := by
  simp only [Finset.mem_sigma, mem_validCompsQ hq, mem_blockSetQ hq]
  constructor
  · rintro ⟨⟨hsum, hup, hend⟩, rfl, hadm⟩
    exact ⟨⟨hadm, hup, hend, hsum⟩, rfl⟩
  · rintro ⟨⟨hadm, hup, hend, hsum⟩, rfl⟩
    exact ⟨⟨hsum, hup, hend⟩, rfl, hadm⟩

/-- The count by chains: |admSetQ q (n+1)| = Σ over the Order lists os in
    `validCompsQ q n` of ∏ |admSetQ q o_i|. -/
theorem card_admSetQ_succ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (admSetQ q (n + 1)).card =
      ∑ os ∈ validCompsQ q n, (os.map (fun o => (admSetQ q o).card)).prod := by
  have himg : ((validCompsQ q n).sigma (blockSetQ q)).image (fun p => chainWordQ p.2) =
      admSetQ q (n + 1) := by
    ext s
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨os, bs⟩, hp, rfl⟩
      exact chainWordQ_mem hodd hq ((mem_sigma_blockSetQ hq n os bs).mp hp).1
    · intro hs
      obtain ⟨bs, hbs, rfl⟩ := chainWordQ_surjOn hodd hq n (Finset.mem_coe.mpr hs)
      exact ⟨⟨bs.map order, bs⟩, (mem_sigma_blockSetQ hq n _ bs).mpr ⟨hbs, rfl⟩, rfl⟩
  have hinj : Set.InjOn (fun p : Σ _ : List ℕ, List (List Bool) => chainWordQ p.2)
      ((validCompsQ q n).sigma (blockSetQ q)) := by
    rintro ⟨os, bs⟩ hp ⟨os', bs'⟩ hr h
    rw [Finset.mem_coe, mem_sigma_blockSetQ hq] at hp hr
    have hbb : bs = bs' := chainWordQ_injOn q n hp.1 hr.1 h
    subst hbb
    rw [← hp.2, ← hr.2]
  rw [← himg, Finset.card_image_of_injOn hinj, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro os _
  exact card_blockSetQ q os

-- q = 5: the counts of Orders 1 to 4, directly and by chains.
set_option linter.hashCommand false in
#guard (List.range 4).map (fun n => (admSetQ 5 (n + 1)).card) = [1, 2, 5, 14]

set_option linter.hashCommand false in
#guard (List.range 4).map
    (fun n => ∑ os ∈ validCompsQ 5 n, (os.map (fun o => (admSetQ 5 o).card)).prod) =
  [1, 2, 5, 14]

/-! ## 13. The deficit budget -/

/-- Deficit ratio D(o) = 2^p2Q(o) / q^o, the reciprocal of the block factor. -/
def deficitRatioQ (q o : ℕ) : ℚ := 2 ^ p2Q q o / (q : ℚ) ^ o

/-- 1 < D(o): every block lowers the level. -/
theorem one_lt_deficitRatioQ (hq : 3 ≤ q) (o : ℕ) : 1 < deficitRatioQ q o := by
  unfold deficitRatioQ
  have hq0 : (0 : ℚ) < q := by
    exact_mod_cast (by omega : 0 < q)
  have hpos : (0 : ℚ) < (q : ℚ) ^ o := pow_pos hq0 o
  have hlt : (q : ℚ) ^ o < 2 ^ p2Q q o := by
    exact_mod_cast p2Q_spec hq o
  rw [lt_div_iff₀ hpos, one_mul]
  exact hlt

/-- D(o) ≤ 2: a block at most halves the level. -/
theorem deficitRatioQ_le_two (hq : 3 ≤ q) (o : ℕ) : deficitRatioQ q o ≤ 2 := by
  unfold deficitRatioQ
  have hq0 : (0 : ℚ) < q := by
    exact_mod_cast (by omega : 0 < q)
  have hpos : (0 : ℚ) < (q : ℚ) ^ o := pow_pos hq0 o
  have hn : (2 : ℚ) ^ (p2Q q o - 1) ≤ (q : ℚ) ^ o := by
    exact_mod_cast p2Q_spec_lower hq o
  have hone := one_le_p2Q q o
  have hp : p2Q q o = (p2Q q o - 1) + 1 := by
    omega
  rw [div_le_iff₀ hpos, hp, pow_succ]
  linarith

/-- D(0) = 2: the block [0] halves the level. -/
theorem deficitRatioQ_zero (q : ℕ) : deficitRatioQ q 0 = 2 := by
  simp [deficitRatioQ, p2Q]

/-- For odd q, D(o) < 2 for a block of Order ≥ 1. -/
theorem deficitRatioQ_lt_two (hodd : Odd q) (hq : 3 ≤ q) {o : ℕ} (ho : 1 ≤ o) :
    deficitRatioQ q o < 2 := by
  apply lt_of_le_of_ne (deficitRatioQ_le_two hq o)
  intro h
  unfold deficitRatioQ at h
  have hq0 : (0 : ℚ) < q := by
    exact_mod_cast (by omega : 0 < q)
  have hpos : (0 : ℚ) < (q : ℚ) ^ o := pow_pos hq0 o
  rw [div_eq_iff hpos.ne'] at h
  have hone := one_le_p2Q q o
  have hp : p2Q q o = (p2Q q o - 1) + 1 := by
    omega
  rw [hp, pow_succ] at h
  have h2 : (2 : ℚ) ^ (p2Q q o - 1) = (q : ℚ) ^ o := by
    linarith
  have hnat : 2 ^ (p2Q q o - 1) = q ^ o := by
    exact_mod_cast h2
  exact two_pow_ne_q_pow hodd hq ho hnat

/-- ∏ D(o_i) = 2^(Σ p2Q(o_i)) / q^(Σ o_i). -/
theorem prod_deficitRatioQ (q : ℕ) (os : List ℕ) :
    (os.map (deficitRatioQ q)).prod = 2 ^ (os.map (p2Q q)).sum / (q : ℚ) ^ os.sum := by
  induction os with
  | nil =>
    simp
  | cons o t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, List.sum_cons,
      pow_add, pow_add, deficitRatioQ, div_mul_div_comm]

/-- Budget form of `LevelUpQ`: 2 ∏ D(o_i) < q. -/
theorem levelUpQ_iff_budgetQ (hq : 3 ≤ q) (os : List ℕ) :
    LevelUpQ q os ↔ 2 * (os.map (deficitRatioQ q)).prod < q := by
  rw [prod_deficitRatioQ]
  have hq0 : (0 : ℚ) < q := by
    exact_mod_cast (by omega : 0 < q)
  have hpos : (0 : ℚ) < (q : ℚ) ^ os.sum := pow_pos hq0 _
  rw [← mul_div_assoc, div_lt_iff₀ hpos]
  unfold LevelUpQ
  rw [pow_add, pow_add, pow_one, pow_one]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- The admissible words of Order ≥ 1 in budget form: 1 :: (B1 ++ ... ++ Bm) with
    admissible blocks, 2 ∏ D(o_i) < q over all blocks but the last, and not over all. -/
theorem admissibleQ_iff_exists_chain_budgetQ (hodd : Odd q) (hq : 3 ≤ q) (s : List Bool) :
    (AdmissibleQ q s ∧ 1 ≤ order s) ↔
      ∃ bs, IsSplitQ q s bs ∧
        2 * ((bs.map order).dropLast.map (deficitRatioQ q)).prod < q ∧
          ¬2 * ((bs.map order).map (deficitRatioQ q)).prod < q := by
  simp only [← levelUpQ_iff_budgetQ hq]
  exact admissibleQ_iff_exists_chainQ hodd hq s

end ChainQ
