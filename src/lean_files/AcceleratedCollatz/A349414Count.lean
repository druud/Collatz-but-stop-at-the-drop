-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.ChainDecomposition
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Set.Card

/-!
# The stop words of the A349414 run: 2 A100982(a) of them

Self-contained extract of the AcceleratedCollatz Lean 4 project; depends on Mathlib and
the extract `ChainDecomposition` only.

The run of `A349414Run` reads a word in three letters, U (factor 3/2), D (3/4) and S (1/4).
A stop word (`Stop`) has product at least 1 on every proper prefix and below 1 in all;
`ud w` counts its U and D. With U -> 1, D -> 10, S -> 00 (`enc`, injective: `enc_inj`) the
product is the level of the bits (`prod_eq`). A stop word goes to an admissible PV v of
Order `ud w` (`ChainDecomposition.Admissible`), or to v followed by a 0 (`enc_of_stop`);
conversely v and v0 both come from a stop word (`stop_of_adm`, `stop_of_adm_zero`; every
bit list v or 0v decodes, `dec_or`). So the stop words with a >= 1 letters U or D number
2 A100982(a) (`stop_count`), and the only one with none is S (`stop_count_zero`): the
count of `OEIS/a349414_variant_01.py`.
-/

namespace A349414Count

open ChainDecomposition

/-- The three letters of the run. -/
inductive L | U | D | S
  deriving DecidableEq

/-- The factor of a letter. -/
def lf : L → ℚ
  | .U => 3 / 2
  | .D => 3 / 4
  | .S => 1 / 4

/-- The bits of a letter: U -> 1, D -> 10, S -> 00. -/
def bits : L → List Bool
  | .U => [true]
  | .D => [true, false]
  | .S => [false, false]

/-- The product of a word. -/
def prod (w : List L) : ℚ := (w.map lf).prod

/-- The bits of a word. -/
def enc (w : List L) : List Bool := w.flatMap bits

/-- The number of letters U and D. -/
def ud (w : List L) : ℕ := w.countP (fun c => c != .S)

/-- A stop word: product at least 1 on every proper prefix, below 1 in all. -/
def Stop (w : List L) : Prop := (∀ i < w.length, 1 ≤ prod (w.take i)) ∧ prod w < 1

theorem enc_cons (c : L) (w : List L) : enc (c :: w) = bits c ++ enc w := by
  simp [enc]

theorem enc_append (a b : List L) : enc (a ++ b) = enc a ++ enc b := by
  simp [enc]

theorem prod_append (a b : List L) : prod (a ++ b) = prod a * prod b := by
  simp [prod]

theorem bits_prod (c : L) : seqProduct (bits c) = lf c := by
  cases c <;> norm_num [bits, lf, seqProduct, factor]

/-- The product of a word is the level of its bits. -/
theorem prod_eq (w : List L) : prod w = seqProduct (enc w) := by
  induction w with
  | nil => simp [prod, enc, seqProduct]
  | cons c w ih =>
    rw [enc_cons, seqProduct_append, bits_prod, ← ih]
    simp [prod]

theorem ud_eq (w : List L) : ud w = order (enc w) := by
  induction w with
  | nil => simp [ud, enc, order]
  | cons c w ih =>
    rw [enc_cons]
    have ho : order (bits c ++ enc w) = order (bits c) + order (enc w) := by
      simp [order, List.filter_append]
    rw [ho, ← ih]
    cases c <;> simp [ud, bits, order] <;> omega

theorem bits_ne_nil (c : L) : bits c ≠ [] := by cases c <;> simp [bits]

theorem enc_length_pos {w : List L} (h : w ≠ []) : 0 < (enc w).length := by
  obtain ⟨c, w, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [enc_cons, List.length_append]
  have := List.length_pos_of_ne_nil (bits_ne_nil c)
  omega

/-! ### Unique decoding -/

/-- No word's bits are a 0 followed by another word's bits. -/
theorem enc_ne_false_cons : ∀ n (x y : List L), (enc x).length + (enc y).length ≤ n →
    enc x ≠ false :: enc y := by
  intro n
  induction n with
  | zero =>
    intro x y _ h
    have := congrArg List.length h
    simp at this
    omega
  | succ n ih =>
    intro x y hn h
    cases x with
    | nil => simp [enc] at h
    | cons c x =>
      cases c with
      | U => simp [enc_cons, bits] at h
      | D => simp [enc_cons, bits] at h
      | S =>
        rw [enc_cons] at h
        simp only [bits, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
        have hl : (enc x).length + 2 = (enc (L.S :: x)).length := by
          rw [enc_cons]; simp [bits]
        have hy := congrArg List.length h
        simp only [List.length_cons] at hy
        exact ih y x (by omega) h.symm

theorem enc_inj : Function.Injective enc := by
  intro x
  induction x with
  | nil =>
    intro y h
    cases y with
    | nil => rfl
    | cons c y =>
      have := enc_length_pos (List.cons_ne_nil c y)
      rw [← h] at this
      simp [enc] at this
  | cons c x ih =>
    intro y h
    cases y with
    | nil =>
      have := enc_length_pos (List.cons_ne_nil c x)
      rw [h] at this
      simp [enc] at this
    | cons d y =>
      rw [enc_cons, enc_cons] at h
      cases c <;> cases d <;>
        simp only [bits, List.cons_append, List.nil_append, List.cons.injEq, true_and,
          Bool.true_eq_false, Bool.false_eq_true, false_and] at h
      all_goals first
        | rw [ih h]
        | exact absurd h (enc_ne_false_cons _ _ _ le_rfl)
        | exact absurd h.symm (enc_ne_false_cons _ _ _ le_rfl)

/-- Every bit list v or 0v is the bits of a word. -/
theorem dec_or : ∀ v : List Bool, (∃ w, enc w = v) ∨ (∃ w, enc w = false :: v) := by
  intro v
  induction v with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons b v ih =>
    cases b with
    | true =>
      left
      rcases ih with ⟨w, hw⟩ | ⟨w, hw⟩
      · exact ⟨L.U :: w, by rw [enc_cons, hw]; rfl⟩
      · cases w with
        | nil => simp [enc] at hw
        | cons c w =>
          rw [enc_cons] at hw
          cases c with
          | U => simp [bits] at hw
          | D => simp [bits] at hw
          | S =>
            simp only [bits, List.cons_append, List.nil_append, List.cons.injEq,
              true_and] at hw
            exact ⟨L.D :: w, by rw [enc_cons, ← hw]; rfl⟩
    | false =>
      rcases ih with ⟨w, hw⟩ | ⟨w, hw⟩
      · right
        exact ⟨L.S :: w, by rw [enc_cons, hw]; rfl⟩
      · exact Or.inl ⟨w, hw⟩

/-! ### Levels -/

theorem seqProduct_pos (l : List Bool) : 0 < seqProduct l := by
  rw [seqProduct_eq]
  positivity

/-- A nonempty bit list has level other than 1. -/
theorem seqProduct_ne_one {l : List Bool} (h : l ≠ []) : seqProduct l ≠ 1 := by
  intro h1
  rw [seqProduct_eq] at h1
  have hle := order_le_length l
  have hlen := List.length_pos_of_ne_nil h
  have e : (2 : ℚ) ^ l.length = 2 ^ order l * 2 ^ (l.length - order l) := by
    rw [← pow_add]; congr 1; omega
  have a1 : (3 / 2 : ℚ) ^ order l * 2 ^ order l = 3 ^ order l := by
    rw [← mul_pow]; norm_num
  have a2 : (1 / 2 : ℚ) ^ (l.length - order l) * 2 ^ (l.length - order l) = 1 := by
    rw [← mul_pow]; norm_num
  have h2 : (3 : ℚ) ^ order l = 2 ^ l.length := by
    linear_combination (-1 : ℚ) * a1 - (3 / 2 : ℚ) ^ order l * 2 ^ order l * a2
      + 2 ^ order l * 2 ^ (l.length - order l) * h1 - e
  have h3 : (3 ^ order l : ℕ) = 2 ^ l.length := by exact_mod_cast h2
  have h4 : 2 ∣ 3 ^ order l := by rw [h3]; exact dvd_pow_self 2 (by omega)
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h4
  omega

theorem one_lt_of_le {l : List Bool} (h : 1 ≤ seqProduct l) (hne : l ≠ []) :
    1 < seqProduct l := lt_of_le_of_ne h (seqProduct_ne_one hne).symm

theorem take_enc_append (p : List L) (c : L) (j : ℕ) :
    (enc (p ++ [c])).take j = (enc p).take j ++ (bits c).take (j - (enc p).length) := by
  rw [enc_append, List.take_append]
  simp [enc]

/-- Product at least 1 on the letter prefixes of p gives level above 1 at every nonempty
    bit prefix of its bits. -/
theorem prefix_bits : ∀ p : List L, (∀ i ≤ p.length, 1 ≤ prod (p.take i)) →
    ∀ j, 1 ≤ j → j ≤ (enc p).length → 1 < seqProduct ((enc p).take j) := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro _ j h1 h2; simp [enc] at h2; omega
  | append_singleton p c ih =>
    intro hP j h1 h2
    have hP' : ∀ i ≤ p.length, 1 ≤ prod (p.take i) := by
      intro i hi
      have := hP i (by simp; omega)
      rwa [List.take_append_of_le_length hi] at this
    have hp : 1 ≤ seqProduct (enc p) := by
      have := hP' p.length le_rfl
      rwa [List.take_length, prod_eq] at this
    have hpc : 1 ≤ seqProduct (enc p) * lf c := by
      have := hP (p.length + 1) (by simp)
      have hb : enc [c] = bits c := by simp [enc]
      rw [List.take_of_length_le (by simp), prod_eq, enc_append, seqProduct_append, hb,
        bits_prod] at this
      exact this
    have hlen : (enc (p ++ [c])).length = (enc p).length + (bits c).length := by
      rw [enc_append, List.length_append]
      simp [enc]
    rw [take_enc_append]
    by_cases hj : j ≤ (enc p).length
    · rw [show j - (enc p).length = 0 by omega, List.take_zero, List.append_nil]
      exact ih hP' j h1 hj
    · rw [seqProduct_append]
      have hjc : j - (enc p).length ≤ (bits c).length := by omega
      rw [List.take_of_length_le (show (enc p).length ≤ j by omega)]
      have hfull : 1 < seqProduct (enc p) * seqProduct (bits c) := by
        rw [← seqProduct_append]
        refine one_lt_of_le ?_ (by simp [bits_ne_nil])
        rw [seqProduct_append, bits_prod]
        exact hpc
      cases c with
      | U =>
        simp only [bits, List.length_singleton] at hjc
        rw [show j - (enc p).length = 1 by omega]
        exact hfull
      | D =>
        simp only [bits, List.length_cons, List.length_nil] at hjc
        rcases (show j - (enc p).length = 1 ∨ j - (enc p).length = 2 by omega) with e | e
        · rw [e]
          have : seqProduct ((bits L.D).take 1) = 3 / 2 := by
            norm_num [bits, seqProduct, factor]
          rw [this]
          linarith
        · rw [e]
          exact hfull
      | S =>
        simp only [bits, List.length_cons, List.length_nil] at hjc
        rcases (show j - (enc p).length = 1 ∨ j - (enc p).length = 2 by omega) with e | e
        · rw [e]
          have : seqProduct ((bits L.S).take 1) = 1 / 2 := by
            norm_num [bits, seqProduct, factor]
          rw [this]
          norm_num [lf] at hpc
          linarith
        · rw [e]
          exact hfull

/-! ### Stop words and admissible PVs -/

theorem sp_snoc (l : List Bool) (b : Bool) : seqProduct (l ++ [b]) = seqProduct l * factor b := by
  simp [seqProduct]

theorem sp_snoc2 (l : List Bool) (a b : Bool) :
    seqProduct (l ++ [a, b]) = seqProduct l * factor a * factor b := by
  simp [seqProduct, mul_assoc]

theorem take_succ_len (l : List Bool) (a b : Bool) :
    (l ++ [a, b]).take (l.length + 1) = l ++ [a] := by
  simp [List.take_append]

/-- A stop word gives an admissible PV, or one followed by a 0. -/
theorem enc_of_stop {w : List L} (h : Stop w) :
    Admissible (enc w) ∨ ∃ v, Admissible v ∧ enc w = v ++ [false] := by
  obtain ⟨hP, hlt⟩ := h
  have hne : w ≠ [] := by rintro rfl; simp [prod] at hlt
  obtain ⟨p, c, rfl⟩ : ∃ p c, w = p ++ [c] :=
    ⟨w.dropLast, w.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  have hP' : ∀ i ≤ p.length, 1 ≤ prod (p.take i) := by
    intro i hi
    have := hP i (by simp; omega)
    rwa [List.take_append_of_le_length hi] at this
  have hx : 1 ≤ seqProduct (enc p) := by
    have := hP' p.length le_rfl
    rwa [List.take_length, prod_eq] at this
  have hb : enc [c] = bits c := by simp [enc]
  have hl : seqProduct (enc p) * lf c < 1 := by
    rwa [prod_eq, enc_append, seqProduct_append, hb, bits_prod] at hlt
  have K := prefix_bits p hP'
  have hK : ∀ t : List Bool, ∀ m, 1 ≤ m → m ≤ (enc p).length →
      1 < seqProduct ((enc p ++ t).take m) := by
    intro t m h1 h2
    rw [List.take_append_of_le_length h2]
    exact K m h1 h2
  rw [enc_append, hb]
  cases c with
  | U => norm_num [lf] at hl; linarith
  | D =>
    left
    refine ⟨fun m h1 h2 => ?_, ?_⟩
    · simp only [bits, List.length_append, List.length_cons, List.length_nil] at h2
      by_cases hm : m ≤ (enc p).length
      · exact hK _ m h1 hm
      · rw [show m = (enc p).length + 1 by omega]
        change 1 < seqProduct ((enc p ++ [true, false]).take _)
        rw [take_succ_len, sp_snoc]
        norm_num [factor]
        linarith
    · change seqProduct (enc p ++ [true, false]) < 1
      rw [sp_snoc2]
      norm_num [lf] at hl
      norm_num [factor]
      linarith
  | S =>
    by_cases hx2 : seqProduct (enc p) * (1 / 2) < 1
    · right
      refine ⟨enc p ++ [false], ⟨fun m h1 h2 => ?_, ?_⟩, by simp [bits]⟩
      · simp only [List.length_append, List.length_cons, List.length_nil] at h2
        exact hK _ m h1 (by omega)
      · rw [sp_snoc]
        norm_num [factor]
        linarith
    · left
      refine ⟨fun m h1 h2 => ?_, ?_⟩
      · simp only [bits, List.length_append, List.length_cons, List.length_nil] at h2
        by_cases hm : m ≤ (enc p).length
        · exact hK _ m h1 hm
        · rw [show m = (enc p).length + 1 by omega]
          change 1 < seqProduct ((enc p ++ [false, false]).take _)
          rw [take_succ_len]
          refine one_lt_of_le ?_ (by simp)
          rw [sp_snoc]
          norm_num [factor]
          linarith
      · change seqProduct (enc p ++ [false, false]) < 1
        rw [sp_snoc2]
        norm_num [lf] at hl
        norm_num [factor]
        linarith

/-- The bits of a prefix of a word, and of the rest. -/
theorem enc_take_drop (w : List L) (i : ℕ) : enc w = enc (w.take i) ++ enc (w.drop i) := by
  rw [← enc_append, List.take_append_drop]

theorem drop_ne_nil {w : List L} {i : ℕ} (hi : i < w.length) : 0 < (enc (w.drop i)).length :=
  enc_length_pos (by intro h; have := congrArg List.length h; simp at this; omega)

/-- A word whose bits are an admissible PV is a stop word. -/
theorem stop_of_adm {w : List L} (hA : Admissible (enc w)) : Stop w := by
  refine ⟨fun i hi => ?_, by rw [prod_eq]; exact hA.lt_one⟩
  have he := enc_take_drop w i
  have hr := drop_ne_nil hi
  rw [prod_eq]
  have hj : (enc (w.take i)).length < (enc w).length := by
    rw [he, List.length_append]; omega
  have ht : (enc w).take (enc (w.take i)).length = enc (w.take i) := by
    rw [he]; simp
  rcases Nat.eq_zero_or_pos (enc (w.take i)).length with h0 | h0
  · rw [List.length_eq_zero_iff.mp h0]; simp [seqProduct]
  · rw [← ht]
    exact (hA.prefix_gt _ h0 hj).le

/-- A word whose bits are an admissible PV followed by a 0 is a stop word. -/
theorem stop_of_adm_zero {w : List L} {v : List Bool} (hA : Admissible v)
    (hw : enc w = v ++ [false]) : Stop w := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have he := enc_take_drop w i
    have hr := drop_ne_nil hi
    rw [prod_eq]
    have hlen : (enc (w.take i)).length + (enc (w.drop i)).length = v.length + 1 := by
      have := congrArg List.length he
      rw [hw] at this
      simp at this
      omega
    have hj : (enc (w.take i)).length < v.length := by
      rcases Nat.lt_or_ge (enc (w.take i)).length v.length with h | h
      · exact h
      · exfalso
        have h1 : (enc (w.drop i)).length = 1 := by omega
        have hd : enc (w.drop i) = [false] := by
          have := congrArg (List.drop (enc (w.take i)).length) he
          rw [hw, List.drop_left] at this
          rw [← this, List.drop_append_of_le_length (by omega)]
          rw [show (enc (w.take i)).length = v.length by omega]
          simp
        exact enc_ne_false_cons _ (w.drop i) [] le_rfl (by simpa [enc] using hd)
    have ht : v.take (enc (w.take i)).length = enc (w.take i) := by
      have := congrArg (List.take (enc (w.take i)).length) he
      rw [hw, List.take_append_of_le_length hj.le] at this
      rw [this]; simp
    rcases Nat.eq_zero_or_pos (enc (w.take i)).length with h0 | h0
    · rw [List.length_eq_zero_iff.mp h0]; simp [seqProduct]
    · rw [← ht]
      exact (hA.prefix_gt _ h0 hj).le
  · rw [prod_eq, hw, sp_snoc]
    have := hA.lt_one
    have := seqProduct_pos v
    norm_num [factor]
    linarith

/-- A bit list starting with 1 is the bits of a word. -/
theorem dec_true (r : List Bool) : ∃ w, enc w = true :: r := by
  rcases dec_or (true :: r) with h | ⟨w, hw⟩
  · exact h
  · cases w with
    | nil => simp [enc] at hw
    | cons c w => cases c <;> simp [enc_cons, bits] at hw

/-- An admissible PV of Order at least 1 starts with 1. -/
theorem adm_head {v : List Bool} (hA : Admissible v) (ho : 1 ≤ order v) : ∃ r, v = true :: r := by
  cases v with
  | nil => simp [order] at ho
  | cons b r =>
    cases b with
    | true => exact ⟨r, rfl⟩
    | false =>
      exfalso
      cases r with
      | nil => simp [order] at ho
      | cons b' r' =>
        have := hA.prefix_gt 1 le_rfl (by simp)
        norm_num [seqProduct, factor] at this

theorem order_snoc_false (v : List Bool) : order (v ++ [false]) = order v := by
  simp [order, List.filter_append]

/-- The stop words with a ≥ 1 letters U or D: 2 A100982(a) of them. -/
theorem stop_count (a : ℕ) (ha : 1 ≤ a) :
    {w : List L | Stop w ∧ ud w = a}.ncard = 2 * A100982 a := by
  have himg : enc '' {w : List L | Stop w ∧ ud w = a} =
      ↑(admSet a ∪ (admSet a).image (· ++ [false])) := by
    ext v
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_union, Finset.coe_image,
      Set.mem_union, Finset.mem_coe, mem_admSet]
    constructor
    · rintro ⟨w, ⟨hs, hu⟩, rfl⟩
      rw [ud_eq] at hu
      rcases enc_of_stop hs with h | ⟨u, hu', he⟩
      · exact Or.inl ⟨h, hu⟩
      · right
        refine ⟨u, ⟨hu', ?_⟩, he.symm⟩
        rw [← order_snoc_false, ← he, hu]
    · rintro (⟨hA, ho⟩ | ⟨u, hu, rfl⟩)
      · obtain ⟨r, rfl⟩ := adm_head hA (by omega)
        obtain ⟨w, hw⟩ := dec_true r
        exact ⟨w, ⟨stop_of_adm (hw ▸ hA), by rw [ud_eq, hw, ho]⟩, hw⟩
      · obtain ⟨hA, ho⟩ := hu
        obtain ⟨r, rfl⟩ := adm_head hA (by omega)
        obtain ⟨w, hw⟩ := dec_true (r ++ [false])
        refine ⟨w, ⟨stop_of_adm_zero hA (by rw [hw]; rfl), ?_⟩, by rw [hw]; rfl⟩
        rw [ud_eq, hw, show true :: (r ++ [false]) = (true :: r) ++ [false] from rfl,
          order_snoc_false, ho]
  have hdis : Disjoint (admSet a) ((admSet a).image (· ++ [false])) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv'
    have h1 := (mem_admSet a _).mp hv
    have h2 := (mem_admSet a _).mp hu
    have l1 := admissible_length _ h1.1
    have l2 := admissible_length _ h2.1
    rw [h1.2] at l1
    rw [h2.2] at l2
    simp at l1
    omega
  rw [← Set.ncard_image_of_injective _ enc_inj, himg, Set.ncard_coe_finset,
    Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (List.append_left_injective [false])]
  rw [A100982]
  omega

/-- The only stop word without U or D is S. -/
theorem stop_count_zero : {w : List L | Stop w ∧ ud w = 0}.ncard = 1 := by
  have : {w : List L | Stop w ∧ ud w = 0} = {[L.S]} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hP, hlt⟩, hu⟩
      have hS : ∀ c ∈ w, c = L.S := by
        intro c hc
        have := List.countP_eq_zero.mp hu c hc
        simpa using this
      cases w with
      | nil => simp [prod] at hlt
      | cons c w =>
        rw [hS c (by simp)]
        cases w with
        | nil => rfl
        | cons d w =>
          have := hP 1 (by simp)
          rw [hS c (by simp)] at this
          norm_num [prod, lf] at this
    · rintro rfl
      refine ⟨⟨fun i hi => ?_, by norm_num [prod, lf]⟩, rfl⟩
      obtain rfl : i = 0 := by simpa using hi
      simp [prod]
  rw [this, Set.ncard_singleton]

end A349414Count
