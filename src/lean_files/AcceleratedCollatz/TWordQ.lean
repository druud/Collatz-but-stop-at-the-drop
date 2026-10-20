-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSieve

/-!
  The q-family (Winkler 2026, Def. 1): words in the factors q/2 (odd step, `true`)
  and 1/2 (halving, `false`) whose proper nonempty prefixes have level > 1 and
  whose whole product is < 1. An admissible word of Order n has length
  p2Q q n = log2(q^n) + 1 (`admissibleQ_length`); `admSetQ q n` collects them, cut out
  of the bit lists of that length (`allBits`). Powers of 2 against powers of q
  (`q_pow_lt_two_pow_iff`, `p2Q_spec`, `two_pow_ne_q_pow`); levels are positive
  (`seqProductQ_pos`). For q = 3 this is the layer of AdmissibleLength
  (`admissibleQ_three`, `seqProductQ_three`, `p2Q_three`).
-/

namespace AcceleratedCollatz

/-! ### Words: enumeration and Order -/

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

theorem p2Q_zero (q : ℕ) : p2Q q 0 = 1 := by
  simp [p2Q]

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

variable {q : ℕ}

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

/-! ### Levels are positive -/

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

/-! ### q = 3 -/

theorem factorQ_three : factorQ 3 = factor := by
  funext b
  cases b
  · simp [factorQ, factor]
  · simp [factorQ, factor]

theorem seqProductQ_three : seqProductQ 3 = seqProduct := by
  funext s
  simp [seqProductQ, seqProduct, factorQ_three]

theorem admissibleQ_three (s : List Bool) : AdmissibleQ 3 s ↔ Admissible s := by
  constructor
  · intro h
    exact ⟨by simpa [seqProductQ_three] using h.prefix_gt,
      by simpa [seqProductQ_three] using h.lt_one⟩
  · intro h
    exact ⟨by simpa [seqProductQ_three] using h.prefix_gt,
      by simpa [seqProductQ_three] using h.lt_one⟩

theorem p2Q_three : p2Q 3 = p2_of := rfl

end AcceleratedCollatz
