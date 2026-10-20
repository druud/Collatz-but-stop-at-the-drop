-- SPDX-License-Identifier: MIT
import Mathlib.Data.List.Lex
import Mathlib.Data.Nat.Find
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Chain decomposition of admissible parity words (A100982)

Self-contained extract of the AcceleratedCollatz Lean 4 project; depends on
Mathlib only.

A word is a `List Bool` (`true` = factor 3/2, `false` = factor 1/2); its
level is the running product. `Admissible s`: the level stays > 1 on every
proper nonempty prefix and ends < 1 (first-passage words). `order s` = the
number of 1s; an admissible word of Order n has length p2(n) =
`Nat.log 2 (3 ^ n) + 1` (`admissible_length`). `admSet n` = the admissible
words of Order n; `A100982 n` = its size.

Sections:
1. Words, products and Order.
2. Admissible words.
3. Splitting into admissible blocks.
4. Chain decomposition: `exists_chain`, `chain_unique`.
5. Validity depends on the Orders only: `admissible_iff_chain`,
   `tail_eq_zero_iff`.
6. Counting: composition recursion (`card_admSet_succ`).
7. First-passage binomial identity (`choose_eq_sum_admSet`).
8. Range form, M. Winkler (`choose_eq_sum_admSet_of_le`).
9. Deficit budget: `validOrders_iff_dropLast`, `validOrders_iff_budget`.
10. Cuts are record lows: `isRecordLow_iff_cut`, `exists_chain_recordLow`.
11. Main results in OEIS notation, with m(j) = p2(j) - 1:
   * `A100982_succ`: a(n + 1) = Σ over valid compositions (o₁, …, oₖ) of n
     of Π a(oᵢ).
   * `A100982_binomial`: C(m(n), n - 1) = Σ_{i=1..n} a(i) C(m(n) - m(i), n - i).
   * `A100982_range`: for every M ≥ m(n - 1),
     C(M, n - 1) = a(n) + Σ_{i=1..n-1} a(i) C(M - m(i), n - i).
   * `A100982_rec`: the case M = m(n - 1), a recurrence for a(n).
   * `#guard` check of a(1..7) = 1, 1, 2, 3, 7, 12, 30.
-/

namespace ChainDecomposition

/-!
## Words, products and Order

A word is a `List Bool`: `true` stands for the factor 3/2, `false` for 1/2.
The running product of a prefix is its level; `order` counts the 1s.
-/

/-- Length of an admissible word of Order p3: the least p2 with 3^p3 < 2^p2. -/
def p2_of (p3 : ℕ) : ℕ := Nat.log 2 (3 ^ p3) + 1

/-- true = tripling factor 3/2, false = halving factor 1/2. -/
def factor (b : Bool) : ℚ := if b then 3 / 2 else 1 / 2

/-- Running product of a word: the product of its factors. -/
def seqProduct (s : List Bool) : ℚ := (s.map factor).prod

/-- Order: count of tripling (true) entries. -/
def order (s : List Bool) : ℕ := (s.filter id).length

/-!
## Admissible words

Admissible (first-passage) words: the level stays > 1 on every proper
nonempty prefix and ends < 1. Such a word of Order n has length p2(n).
-/

/-- An admissible (first-passage) word. -/
structure Admissible (s : List Bool) : Prop where
  /-- Every proper nonempty prefix has level > 1. -/
  prefix_gt : ∀ m, 1 ≤ m → m < s.length → 1 < seqProduct (s.take m)
  /-- The whole word has level < 1. -/
  lt_one : seqProduct s < 1

/-- `Admissible` is decidable. -/
instance (s : List Bool) : Decidable (Admissible s) :=
  decidable_of_iff
    ((∀ m, 1 ≤ m → m < s.length → 1 < seqProduct (s.take m)) ∧ seqProduct s < 1)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

/-- An admissible word ends with 0. -/
theorem admissible_last_false (s : List Bool) (hA : Admissible s) (hne : s ≠ []) :
    s.getLast hne = false := by
  by_contra hlast
  simp only [Bool.not_eq_false] at hlast
  have hlen : s.length ≥ 1 := List.length_pos_of_ne_nil hne
  have hsplit : s = s.dropLast ++ [s.getLast hne] :=
    (List.dropLast_append_getLast hne).symm
  have hfull : seqProduct s = seqProduct s.dropLast * (3 / 2) := by
    rw [hsplit]
    unfold seqProduct
    simp [factor, hlast]
  have hdlen : s.dropLast.length = s.length - 1 := by simp
  rcases Nat.lt_or_ge s.length 2 with hlt2 | hge2
  · have hz : s.dropLast.length = 0 := by omega
    have hdl : s.dropLast = [] := List.length_eq_zero_iff.mp hz
    rw [hdl] at hfull
    have heval : seqProduct s = 3 / 2 := by
      rw [hfull]
      simp [seqProduct]
    linarith [hA.lt_one, heval]
  · have hdlpos : 1 ≤ s.dropLast.length := by omega
    have hdllt : s.dropLast.length < s.length := by omega
    have hdltake : s.dropLast = s.take s.dropLast.length := by
      simp [List.dropLast_eq_take]
    have hprefix : 1 < seqProduct s.dropLast := by
      rw [hdltake]
      exact hA.prefix_gt s.dropLast.length hdlpos hdllt
    linarith [hA.lt_one, hfull, hprefix]

/-- The Order of a word is at most its length. -/
theorem order_le_length (l : List Bool) : order l ≤ l.length := by
  unfold order
  exact List.length_filter_le _ _

/-- Product of a word: (3/2)^(ones) (1/2)^(zeros). -/
theorem seqProduct_eq (l : List Bool) :
    seqProduct l = (3 / 2 : ℚ) ^ (order l) * (1 / 2 : ℚ) ^ (l.length - order l) := by
  induction l with
  | nil => simp [seqProduct, order]
  | cons b t ih =>
    have hle := order_le_length t
    cases b with
    | true =>
      have hord : order (true :: t) = order t + 1 := by
        unfold order
        simp
      have hlen : (true :: t).length = t.length + 1 := by simp
      have hprod : seqProduct (true :: t) = (3 / 2) * seqProduct t := by
        unfold seqProduct
        simp [factor]
      rw [hprod, ih, hord, hlen]
      have hsub : t.length + 1 - (order t + 1) = t.length - order t := by omega
      rw [hsub]
      ring
    | false =>
      have hord : order (false :: t) = order t := by
        unfold order
        simp
      have hlen : (false :: t).length = t.length + 1 := by simp
      have hprod : seqProduct (false :: t) = (1 / 2) * seqProduct t := by
        unfold seqProduct
        simp [factor]
      rw [hprod, ih, hord, hlen]
      have hsub : t.length + 1 - order t = (t.length - order t) + 1 := by omega
      rw [hsub, pow_succ]
      ring

/-- (3/2)^a (1/2)^(b-a) 2^b = 3^a for a ≤ b. -/
theorem seqProduct_combine_mul (a b : ℕ) (hab : a ≤ b) :
    (3 / 2 : ℚ) ^ a * (1 / 2 : ℚ) ^ (b - a) * (2 : ℚ) ^ b = (3 : ℚ) ^ a := by
  have hexp : (2:ℚ) ^ b = (2:ℚ) ^ a * (2:ℚ) ^ (b - a) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : (2:ℚ) ^ a ≠ 0 := by positivity
  have h2 : (2:ℚ) ^ (b - a) ≠ 0 := by positivity
  rw [hexp, div_pow, div_pow, one_pow]
  rw [show (3:ℚ) ^ a / (2:ℚ) ^ a * (1 / (2:ℚ) ^ (b - a)) * ((2:ℚ) ^ a * (2:ℚ) ^ (b - a))
      = (3:ℚ) ^ a * ((2:ℚ) ^ a / (2:ℚ) ^ a) *
        ((2:ℚ) ^ (b - a) / (2:ℚ) ^ (b - a)) from by ring]
  rw [div_self h1, div_self h2]
  ring

/-- An admissible word of Order n has length p2(n). -/
theorem admissible_length (s : List Bool) (hA : Admissible s) :
    s.length = p2_of (order s) := by
  have hne : s ≠ [] := by
    intro hcontra
    rw [hcontra] at hA
    have h := hA.lt_one
    simp [seqProduct] at h
  have hlast := admissible_last_false s hA hne
  have hsplit : s = s.dropLast ++ [false] := by
    rw [← hlast]
    exact (List.dropLast_append_getLast hne).symm
  have hdlen : s.dropLast.length = s.length - 1 := by simp
  have hdord : order s.dropLast = order s := by
    conv_rhs => rw [hsplit]
    unfold order
    simp
  have hple : order s ≤ s.length := order_le_length s
  have hple1 : order s ≤ s.length - 1 := by
    have := order_le_length s.dropLast
    rw [hdord, hdlen] at this
    exact this
  have hnpos : s.length ≥ 1 := List.length_pos_of_ne_nil hne
  have hub_nat : (3 : ℕ) ^ (order s) < 2 ^ s.length := by
    have hcombine := seqProduct_combine_mul (order s) s.length hple
    have heq : seqProduct s * (2:ℚ) ^ s.length = (3:ℚ) ^ (order s) := by
      rw [seqProduct_eq s]
      exact hcombine
    have h2pos : (0:ℚ) < (2:ℚ) ^ s.length := by positivity
    have hstep := mul_lt_mul_of_pos_right hA.lt_one h2pos
    rw [heq, one_mul] at hstep
    exact_mod_cast hstep
  have hdllt : s.dropLast.length < s.length := by omega
  rcases Nat.lt_or_ge s.length 2 with hlt2 | hge2
  · have hl1 : s.length = 1 := by omega
    have hz : s.dropLast.length = 0 := by omega
    have hdl : s.dropLast = [] := List.length_eq_zero_iff.mp hz
    have hord0 : order s = 0 := by
      rw [← hdord, hdl]
      unfold order
      simp
    rw [hl1, hord0]
    unfold p2_of
    simp
  · have hdlpos : 1 ≤ s.dropLast.length := by omega
    have hdltake : s.dropLast = s.take s.dropLast.length := by
      simp [List.dropLast_eq_take]
    have hlb_raw : 1 < seqProduct s.dropLast := by
      rw [hdltake]
      exact hA.prefix_gt s.dropLast.length hdlpos hdllt
    have hlb_nat : 2 ^ (s.length - 1) ≤ 3 ^ (order s) := by
      have hcombine := seqProduct_combine_mul (order s) (s.length - 1) hple1
      have heq : seqProduct s.dropLast * (2:ℚ) ^ (s.length - 1) = (3:ℚ) ^ (order s) := by
        rw [seqProduct_eq s.dropLast, hdord, hdlen]
        exact hcombine
      have h2pos : (0:ℚ) < (2:ℚ) ^ (s.length - 1) := by positivity
      have hstep := mul_lt_mul_of_pos_right hlb_raw h2pos
      rw [heq, one_mul] at hstep
      exact_mod_cast hstep.le
    have hub_nat' : 3 ^ order s < 2 ^ (s.length - 1 + 1) := by
      rw [Nat.sub_add_cancel hnpos]
      exact hub_nat
    have hlog : Nat.log 2 (3 ^ order s) = s.length - 1 :=
      Nat.log_eq_of_pow_le_of_lt_pow hlb_nat hub_nat'
    unfold p2_of
    omega

/-- Prefix property (paper sec:words): no admissible sequence is a proper
    prefix of another. Distinct-order classes have distinct lengths
    (admissible_length + p2_of's strict monotonicity), so if one were a
    prefix of the other it would have to be the strictly shorter one --
    but a proper-prefix product must be > 1 (Admissible's own first
    clause), contradicting that the shorter sequence, being itself fully
    admissible, has full product < 1. -/
theorem admissible_not_prefix (s s' : List Bool)
    (hA : Admissible s) (hA' : Admissible s') (hne : s ≠ s') :
    ¬ s <+: s' := by
  intro hpre
  obtain ⟨t, ht⟩ := hpre
  have hspos : s ≠ [] := by
    intro h
    rw [h] at hA
    have h1 := hA.lt_one
    simp [seqProduct] at h1
  have hlen : s.length < s'.length := by
    rcases Nat.lt_or_ge s.length s'.length with h | h
    · exact h
    · exfalso
      have hsum : s.length + t.length = s'.length := by
        rw [← ht]
        simp
      have htlen : t.length = 0 := by omega
      have ht0 : t = [] := List.length_eq_zero_iff.mp htlen
      rw [ht0, List.append_nil] at ht
      exact hne ht
  have hstake : s'.take s.length = s := by
    rw [← ht]
    simp
  have hspos_len : 1 ≤ s.length := by
    rcases Nat.eq_zero_or_pos s.length with h0 | h0
    · exact absurd (List.length_eq_zero_iff.mp h0) hspos
    · exact h0
  have hbound := hA'.prefix_gt s.length hspos_len hlen
  rw [hstake] at hbound
  linarith [hA.lt_one, hbound]

/-- Order of b :: t. -/
theorem order_cons (b : Bool) (t : List Bool) :
    order (b :: t) = order t + (if b then 1 else 0) := by
  grind [order]

/-- Product times 2^length is 3^Order. -/
theorem seqProduct_mul_pow (l : List Bool) :
    seqProduct l * (2 : ℚ) ^ l.length = (3 : ℚ) ^ order l := by
  rw [seqProduct_eq]
  exact seqProduct_combine_mul _ _ (order_le_length l)

/-- Product > 1 iff 2^length < 3^Order. -/
theorem one_lt_seqProduct_iff (l : List Bool) :
    1 < seqProduct l ↔ 2 ^ l.length < 3 ^ order l := by
  have h := seqProduct_mul_pow l
  have hpos : (0 : ℚ) < (2 : ℚ) ^ l.length := by positivity
  constructor
  · intro h1
    have h2 := mul_lt_mul_of_pos_right h1 hpos
    rw [one_mul, h] at h2
    exact_mod_cast h2
  · intro h2
    have h2q : (2 : ℚ) ^ l.length < (3 : ℚ) ^ order l := by exact_mod_cast h2
    rw [← h] at h2q
    apply lt_of_mul_lt_mul_right _ hpos.le
    rwa [one_mul]

/-- Product < 1 iff 3^Order < 2^length. -/
theorem seqProduct_lt_one_iff (l : List Bool) :
    seqProduct l < 1 ↔ 3 ^ order l < 2 ^ l.length := by
  have h := seqProduct_mul_pow l
  have hpos : (0 : ℚ) < (2 : ℚ) ^ l.length := by positivity
  constructor
  · intro h1
    have h2 := mul_lt_mul_of_pos_right h1 hpos
    rw [one_mul, h] at h2
    exact_mod_cast h2
  · intro h2
    have h2q : (3 : ℚ) ^ order l < (2 : ℚ) ^ l.length := by exact_mod_cast h2
    rw [← h] at h2q
    apply lt_of_mul_lt_mul_right _ hpos.le
    rwa [one_mul]

/-- Order is additive under concatenation. -/
theorem order_append (a b : List Bool) : order (a ++ b) = order a + order b := by
  simp [order, List.filter_append]

/-- Admissible, with natural-number powers instead of rational products. -/
theorem admissible_iff_pow (s : List Bool) :
    Admissible s ↔
      (∀ m < s.length, 1 ≤ m → 2 ^ m < 3 ^ order (s.take m)) ∧
        3 ^ order s < 2 ^ s.length := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (seqProduct_lt_one_iff s).mp h2⟩
    intro m hm h1m
    have h := (one_lt_seqProduct_iff _).mp (h1 m h1m hm)
    rwa [List.length_take, min_eq_left hm.le] at h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (seqProduct_lt_one_iff s).mpr h2⟩
    intro m h1m hm
    apply (one_lt_seqProduct_iff _).mpr
    rw [List.length_take, min_eq_left hm.le]
    exact h1 m hm h1m

/-- 2^m ≠ 3^a for m ≥ 1. -/
theorem two_pow_ne_three_pow (m a : ℕ) (hm : 1 ≤ m) : 2 ^ m ≠ 3 ^ a := by
  intro h
  have hodd : (3 ^ a) % 2 = 1 := Nat.odd_iff.mp ((by decide : Odd 3).pow)
  have heven : (2 ^ m) % 2 = 0 := by
    obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ]
    simp
  omega

/-- The empty word is not admissible. -/
theorem not_admissible_nil : ¬ Admissible [] := by
  intro h
  have h2 := h.2
  simp [seqProduct] at h2

/-- The only admissible word of Order 0 is [0]. -/
theorem admissible_order_zero (s : List Bool) (hA : Admissible s) (h0 : order s = 0) :
    s = [false] := by
  have hlen := admissible_length s hA
  rw [h0] at hlen
  have hp2 : p2_of 0 = 1 := by
    simp [p2_of]
  rw [hp2] at hlen
  match s, hlen with
  | [b], _ =>
    cases b with
    | true =>
      simp [order] at h0
    | false =>
      rfl

/-- An admissible word of Order ≥ 1 starts with 1. -/
theorem admissible_cons_true (s : List Bool) (hA : Admissible s) (hord : 1 ≤ order s) :
    ∃ u, s = true :: u := by
  have h32 : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have hle := order_le_length s
  have hlen : 2 ≤ s.length := by
    by_contra hlt
    have ho : order s = 1 := by omega
    have hl : s.length = 1 := by omega
    rw [ho, hl] at h32
    norm_num at h32
  have hp := hA.prefix_gt 1 le_rfl (by omega)
  rw [one_lt_seqProduct_iff] at hp
  match s, hp with
  | b :: u, hp =>
    cases b with
    | true =>
      exact ⟨u, rfl⟩
    | false =>
      simp [order] at hp

/-!
## Splitting into admissible blocks

After its leading 1, every admissible word of Order ≥ 1 is a concatenation
of admissible blocks, cut wherever the level reaches a new low.
-/

/-- s = 1 :: flatten bs with admissible blocks. -/
structure IsSplit (s : List Bool) (bs : List (List Bool)) : Prop where
  /-- s is 1 followed by the blocks. -/
  eq : s = true :: bs.flatten
  /-- Every block is admissible. -/
  adm : ∀ b ∈ bs, Admissible b

/-- Order of a concatenation of blocks: the sum of the block Orders. -/
theorem order_flatten (bs : List (List Bool)) : order bs.flatten = (bs.map order).sum := by
  induction bs with
  | nil =>
    simp [order]
  | cons b t ih =>
    rw [List.flatten_cons, order_append, ih, List.map_cons, List.sum_cons]

/-- Admissible blocks: 3^(order) ≤ 2^(length) for their concatenation. -/
theorem pow_le_of_admissible_blocks (bs : List (List Bool)) (h : ∀ b ∈ bs, Admissible b) :
    3 ^ order bs.flatten ≤ 2 ^ bs.flatten.length := by
  induction bs with
  | nil =>
    simp [order]
  | cons b t ih =>
    have hb : 3 ^ order b < 2 ^ b.length := (seqProduct_lt_one_iff b).mp (h b (by simp)).2
    have ht := ih (fun c hc => h c (by simp [hc]))
    rw [List.flatten_cons, order_append, List.length_append, pow_add, pow_add]
    exact Nat.mul_le_mul hb.le ht

/-- A factorization into admissible blocks is unique. -/
theorem flatten_inj_of_admissible :
    ∀ (bs bs' : List (List Bool)), (∀ b ∈ bs, Admissible b) →
      (∀ b ∈ bs', Admissible b) →
      bs.flatten = bs'.flatten → bs = bs' := by
  intro bs
  induction bs with
  | nil =>
    intro bs' _ h' heq
    cases bs' with
    | nil =>
      rfl
    | cons b' t' =>
      have hb' := h' b' (by simp)
      have hne : b' ≠ [] := by
        intro hn
        rw [hn] at hb'
        exact not_admissible_nil hb'
      simp only [List.flatten_nil, List.flatten_cons] at heq
      exact absurd (List.append_eq_nil_iff.mp heq.symm).1 hne
  | cons b t ih =>
    intro bs' h h' heq
    have hb := h b (by simp)
    have hbne : b ≠ [] := by
      intro hn
      rw [hn] at hb
      exact not_admissible_nil hb
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
        · exact admissible_not_prefix b b' hb hb' hne ⟨a', hb'eq.symm⟩
        · exact admissible_not_prefix b' b hb' hb (Ne.symm hne) ⟨c', hbeq.symm⟩
      subst hbb
      have htt := List.append_cancel_left heq
      rw [ih t' (fun c hc => h c (by simp [hc])) (fun c hc => h' c (by simp [hc])) htt]

/-- Factorization of the remainder r of an admissible P ++ r (P ≠ []). -/
theorem exists_blocks : ∀ (n : ℕ) (P r : List Bool), r.length = n → Admissible (P ++ r) →
    P ≠ [] → ∃ bs : List (List Bool), r = bs.flatten ∧ ∀ b ∈ bs, Admissible b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P r hn hA hP
    by_cases hr0 : r = []
    · exact ⟨[], by simp [hr0], by simp⟩
    · have hr : r ≠ [] := hr0
      have hPlen : 1 ≤ P.length := List.length_pos_iff.mpr hP
      have hrlen : 1 ≤ r.length := List.length_pos_iff.mpr hr
      have hApow := (admissible_iff_pow _).mp hA
      have hfull := hApow.2
      have hPlt : P.length < (P ++ r).length := by
        rw [List.length_append]
        omega
      have hpre := hApow.1 P.length hPlt hPlen
      rw [List.take_append_of_le_length le_rfl, List.take_length] at hpre
      rw [order_append, List.length_append, pow_add, pow_add] at hfull
      have hrpow : 3 ^ order r < 2 ^ r.length := by
        by_contra hge
        push Not at hge
        exact Nat.lt_irrefl _ (lt_of_lt_of_le hfull (Nat.mul_le_mul hpre.le hge))
      have hex : ∃ m, 1 ≤ m ∧ m ≤ r.length ∧ 3 ^ order (r.take m) < 2 ^ m :=
        ⟨r.length, hrlen, le_rfl, by rwa [List.take_length]⟩
      obtain ⟨hm1, hmle, hmpow⟩ := Nat.find_spec hex
      have hbA : Admissible (r.take (Nat.find hex)) := by
        rw [admissible_iff_pow]
        have hlen : (r.take (Nat.find hex)).length = Nat.find hex := by
          rw [List.length_take]
          exact min_eq_left hmle
        rw [hlen]
        refine ⟨?_, hmpow⟩
        intro k hk hk1
        rw [List.take_take, min_eq_left hk.le]
        have hmin := Nat.find_min hex hk
        push Not at hmin
        have hle := hmin hk1 (by omega)
        have hne := two_pow_ne_three_pow k (order (r.take k)) hk1
        omega
      have hsplit : P ++ r = (P ++ r.take (Nat.find hex)) ++ r.drop (Nat.find hex) := by
        rw [List.append_assoc, List.take_append_drop]
      have hA' : Admissible ((P ++ r.take (Nat.find hex)) ++ r.drop (Nat.find hex)) := by
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
theorem exists_split (s : List Bool) (hA : Admissible s) (hord : 1 ≤ order s) :
    ∃ bs, IsSplit s bs := by
  obtain ⟨u, rfl⟩ := admissible_cons_true s hA hord
  obtain ⟨bs, hbs, hbsA⟩ := exists_blocks u.length [true] u rfl hA (by simp)
  exact ⟨bs, by rw [← hbs], hbsA⟩

/-- A block followed by another block has Order ≥ 1. -/
theorem zero_block_last (s : List Bool) (hA : Admissible s) (pre post : List (List Bool))
    (b : List Bool) (h : IsSplit s (pre ++ b :: post)) (hpost : post ≠ []) : 1 ≤ order b := by
  by_contra h0
  have hbA : Admissible b := h.adm b (by simp)
  have hb : b = [false] := admissible_order_zero b hbA (by omega)
  have hpreA : ∀ c ∈ pre, Admissible c := fun c hc => h.adm c (by simp [hc])
  have hbound := pow_le_of_admissible_blocks pre hpreA
  obtain ⟨c, ct, rfl⟩ : ∃ c ct, post = c :: ct := by
    cases post with
    | nil =>
      exact absurd rfl hpost
    | cons c ct =>
      exact ⟨c, ct, rfl⟩
  have hcA : Admissible c := h.adm c (by simp)
  have hcne : c ≠ [] := by
    intro hn
    rw [hn] at hcA
    exact not_admissible_nil hcA
  have hs : s = (true :: (pre.flatten ++ [false])) ++ (c ++ ct.flatten) := by
    rw [h.eq, hb]
    simp
  have hApow := (admissible_iff_pow s).mp hA
  have hQlen : (true :: (pre.flatten ++ [false])).length = pre.flatten.length + 2 := by
    simp
  have hslen : pre.flatten.length + 2 < s.length := by
    rw [hs, List.length_append, hQlen]
    have : 0 < (c ++ ct.flatten).length := by
      simp only [List.length_append, List.length_flatten, add_pos_iff]
      exact Or.inl (List.length_pos_iff.mpr hcne)
    omega
  have hp := hApow.1 (pre.flatten.length + 2) hslen (by omega)
  rw [hs, List.take_append_of_le_length (by rw [hQlen]), ← hQlen, List.take_length] at hp
  rw [hQlen, order_cons, order_append] at hp
  have ho : order [false] = 0 := by
    simp [order]
  simp only [ho, ↓reduceIte, add_zero] at hp
  have h4 : 2 ^ (pre.flatten.length + 2) = 2 ^ pre.flatten.length * 4 := by
    rw [pow_add]
    norm_num
  have h3 : 3 ^ (order pre.flatten + 1) = 3 ^ order pre.flatten * 3 := pow_succ _ _
  rw [h4, h3] at hp
  omega

/-- The product is multiplicative under concatenation. -/
theorem seqProduct_append (a b : List Bool) :
    seqProduct (a ++ b) = seqProduct a * seqProduct b := by
  simp [seqProduct, List.map_append, List.prod_append]

/-- An admissible word is nonempty. -/
theorem ne_nil_of_admissible (b : List Bool) (h : Admissible b) : b ≠ [] := by
  intro hn
  rw [hn] at h
  exact not_admissible_nil h

/-- Levels > 1 at the start and at inner boundaries give levels > 1 at every
    position inside the blocks. -/
theorem one_lt_seqProduct_take_flatten :
    ∀ (bs : List (List Bool)) (P : List Bool), (∀ b ∈ bs, Admissible b) →
      1 < seqProduct P →
      (∀ i, 1 ≤ i → i < bs.length → 1 < seqProduct (P ++ (bs.take i).flatten)) →
      ∀ k < bs.flatten.length, 1 < seqProduct (P ++ bs.flatten.take k)
  | [], _, _, _, _, k, hk => by
    simp at hk
  | b :: t, P, hbs, hP, hlev, k, hk => by
    have hbA : Admissible b := hbs b List.mem_cons_self
    rw [List.flatten_cons, List.take_append]
    by_cases hkb : k < b.length
    · have hdrop : k - b.length = 0 := by omega
      rw [hdrop, List.take_zero, List.append_nil]
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simpa using hP
      · rw [seqProduct_append]
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
      have hPb : 1 < seqProduct (P ++ b) := by
        have h1 := hlev 1 le_rfl (by simp [List.length_pos_iff.mpr htne])
        simpa using h1
      apply one_lt_seqProduct_take_flatten t (P ++ b) (fun c hc => hbs c (by simp [hc])) hPb
      · intro i hi hit
        have hlt : i + 1 < (b :: t).length := by
          rw [List.length_cons]
          omega
        have h := hlev (i + 1) (by omega) hlt
        simpa [List.take_succ_cons, List.append_assoc] using h
      · omega

/-- Grammar converse: admissibility of 1 :: A1 ++ ... ++ Ak is decided at the block
    boundaries. -/
theorem admissible_split_iff (bs : List (List Bool)) (hbs : ∀ b ∈ bs, Admissible b) :
    Admissible (true :: bs.flatten) ↔
      (∀ i, 1 ≤ i → i < bs.length → 1 < seqProduct (true :: (bs.take i).flatten)) ∧
        seqProduct (true :: bs.flatten) < 1 := by
  constructor
  · intro hA
    refine ⟨?_, hA.2⟩
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
      exact ne_nil_of_admissible c hcA (hn c hc)
    have hm := hA.1 ((bs.take i).flatten.length + 1) (by omega) (by
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
    have h1 : 1 < seqProduct [true] := by
      norm_num [seqProduct, factor]
    have h := one_lt_seqProduct_take_flatten bs [true] hbs h1 (by simpa using hlev) k hk
    simpa using h

/-!
## Chain decomposition

Chain blocks are admissible words of Order ≥ 1. An admissible word of
Order ≥ 1 is 1 :: (b₁ ++ … ++ bₖ ++ t) with chain blocks bᵢ and t = [] or [0].
The cuts are the strict record lows of the level (section "Cuts are record lows"),
the classical factorization of a path at its descending ladder epochs.
-/

/-- Chain condition: admissible PVs of Order ≥ 1. -/
structure IsChainBlock (b : List Bool) : Prop where
  /-- The block is admissible. -/
  adm : Admissible b
  /-- The block has Order ≥ 1. -/
  order_pos : 1 ≤ order b

/-- Products are positive. -/
theorem seqProduct_pos (s : List Bool) : 0 < seqProduct s := by
  induction s with
  | nil =>
    simp [seqProduct]
  | cons b t ih =>
    have h := seqProduct_append [b] t
    simp only [List.singleton_append] at h
    rw [h]
    apply mul_pos _ ih
    cases b
    · norm_num [seqProduct, factor]
    · norm_num [seqProduct, factor]

/-- Product of [0] is 1/2. -/
theorem seqProduct_singleton_false : seqProduct [false] = 1 / 2 := by
  norm_num [seqProduct, factor]

/-- [0] is admissible (Order 0). -/
theorem admissible_singleton_false : Admissible [false] := by
  refine ⟨?_, ?_⟩
  · intro m hm hml
    simp at hml
    omega
  · rw [seqProduct_singleton_false]
    norm_num

/-- Chain blocks concatenated have product ≤ 1. -/
theorem seqProduct_flatten_le_one (bs : List (List Bool)) (h : ∀ b ∈ bs, IsChainBlock b) :
    seqProduct bs.flatten ≤ 1 := by
  induction bs with
  | nil =>
    simp [seqProduct]
  | cons b t ih =>
    rw [List.flatten_cons, seqProduct_append]
    have hb := (h b List.mem_cons_self).adm.lt_one
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem b hc))
    have hbpos := seqProduct_pos b
    have htpos := seqProduct_pos t.flatten
    nlinarith

/-- Chain blocks concatenated, at least one, have product < 1. -/
theorem seqProduct_flatten_lt_one (bs : List (List Bool)) (h : ∀ b ∈ bs, IsChainBlock b)
    (hne : bs ≠ []) : seqProduct bs.flatten < 1 := by
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.flatten_cons, seqProduct_append]
  have hb := (h b List.mem_cons_self).adm.lt_one
  have ht := seqProduct_flatten_le_one t (fun c hc => h c (List.mem_cons_of_mem b hc))
  have hbpos := seqProduct_pos b
  have htpos := seqProduct_pos t.flatten
  nlinarith

/-- The level after 1 :: chain blocks: 3/2 times the product of the blocks. -/
theorem seqProduct_true_cons_flatten (bs : List (List Bool)) :
    seqProduct (true :: bs.flatten) = 3 / 2 * seqProduct bs.flatten := by
  have h1 := seqProduct_append [true] bs.flatten
  simp only [List.singleton_append] at h1
  rw [h1]
  norm_num [seqProduct, factor]

/-- The level after 1 :: chain blocks is at most 3/2 (equality for the empty chain). -/
theorem seqProduct_chain_le (bs : List (List Bool)) (h : ∀ b ∈ bs, IsChainBlock b) :
    seqProduct (true :: bs.flatten) ≤ 3 / 2 := by
  rw [seqProduct_true_cons_flatten]
  have hle := seqProduct_flatten_le_one bs h
  linarith

/-- The level after 1 :: chain blocks is < 3/2 when there is at least one block. -/
theorem seqProduct_chain_lt (bs : List (List Bool)) (h : ∀ b ∈ bs, IsChainBlock b)
    (hne : bs ≠ []) : seqProduct (true :: bs.flatten) < 3 / 2 := by
  rw [seqProduct_true_cons_flatten]
  have hlt := seqProduct_flatten_lt_one bs h hne
  linarith

/-- A nonempty PV-factor is never 1. -/
theorem seqProduct_ne_one (s : List Bool) (hne : s ≠ []) : seqProduct s ≠ 1 := by
  intro h1
  have hm := seqProduct_mul_pow s
  rw [h1, one_mul] at hm
  have hnat : 2 ^ s.length = 3 ^ order s := by
    exact_mod_cast hm
  have hlen : 0 < s.length := List.length_pos_iff.mpr hne
  have h2 : 2 ∣ 3 ^ order s := by
    rw [← hnat]
    exact dvd_pow_self 2 (by omega)
  have h3 : ¬ 2 ∣ 3 ^ order s := by
    rw [Nat.two_dvd_ne_zero, Nat.pow_mod]
    norm_num
  exact h3 h2

/-- Assembly: a chain whose level stays > 1 at inner boundaries is completed by no
    tail if its final level is < 1, and by a single 0 otherwise. -/
theorem admissible_chain (bs : List (List Bool)) (hbs : ∀ b ∈ bs, IsChainBlock b)
    (hlev : ∀ i, 1 ≤ i → i < bs.length → 1 < seqProduct (true :: (bs.take i).flatten)) :
    (seqProduct (true :: bs.flatten) < 1 → Admissible (true :: bs.flatten)) ∧
      (1 < seqProduct (true :: bs.flatten) → Admissible (true :: (bs.flatten ++ [false]))) := by
  have hbsA : ∀ b ∈ bs, Admissible b := fun b hb => (hbs b hb).adm
  constructor
  · intro hlt
    exact (admissible_split_iff bs hbsA).mpr ⟨hlev, hlt⟩
  · intro hgt
    have hA' : ∀ b ∈ bs ++ [[false]], Admissible b := by
      intro b hb
      rcases List.mem_append.mp hb with hb' | hb'
      · exact hbsA b hb'
      · rw [List.mem_singleton] at hb'
        rw [hb']
        exact admissible_singleton_false
    have hflat : (bs ++ [[false]]).flatten = bs.flatten ++ [false] := by
      simp
    rw [← hflat]
    apply (admissible_split_iff (bs ++ [[false]]) hA').mpr
    constructor
    · intro i hi hil
      rw [List.length_append, List.length_singleton] at hil
      rw [List.take_append_of_le_length (by omega)]
      rcases Nat.lt_or_ge i bs.length with hlt | hge
      · exact hlev i hi hlt
      · have hi' : i = bs.length := by omega
        rw [hi', List.take_length]
        exact hgt
    · rw [hflat]
      have h2 : seqProduct (true :: bs.flatten) < 2 := by
        have h32 := seqProduct_chain_le bs hbs
        linarith
      have happ : true :: (bs.flatten ++ [false]) = (true :: bs.flatten) ++ [false] := by
        simp
      rw [happ, seqProduct_append, seqProduct_singleton_false]
      linarith

/-- Parse: an admissible PV of Order ≥ 1 is a leading 1, a chain, and a tail t ∈ {[], [0]};
    t = [0] iff the level after the chain is > 1. -/
theorem exists_chain (s : List Bool) (hA : Admissible s) (hord : 1 ≤ order s) :
    ∃ (bs : List (List Bool)) (t : List Bool),
      s = true :: (bs.flatten ++ t) ∧ (∀ b ∈ bs, IsChainBlock b) ∧
      (t = [] ∨ t = [false]) ∧ (t = [false] ↔ 1 < seqProduct (true :: bs.flatten)) := by
  obtain ⟨bs0, hsplit⟩ := exists_split s hA hord
  rcases List.eq_nil_or_concat bs0 with h0 | ⟨pre, b, rfl⟩
  · have hs : s = [true] := by
      rw [hsplit.eq, h0]
      rfl
    have hP := hA.lt_one
    rw [hs] at hP
    norm_num [seqProduct, factor] at hP
  · rw [List.concat_eq_append] at hsplit
    have hpre : ∀ c ∈ pre, IsChainBlock c := by
      intro c hc
      refine ⟨hsplit.adm c (by simp [hc]), ?_⟩
      obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hc
      apply zero_block_last s hA l1 (l2 ++ [b]) c
      · have h := hsplit
        simp only [List.append_assoc, List.cons_append] at h
        exact h
      · simp
    have hbA : Admissible b := hsplit.adm b (by simp)
    have hs : s = true :: (pre.flatten ++ b) := by
      rw [hsplit.eq]
      simp
    rcases Nat.eq_zero_or_pos (order b) with hb0 | hbpos
    · have hbf : b = [false] := admissible_order_zero b hbA hb0
      refine ⟨pre, [false], by rw [hs, hbf], hpre, Or.inr rfl, ?_⟩
      simp only [true_iff]
      have hlen : (true :: pre.flatten).length < s.length := by
        rw [hs, hbf]
        simp
      have h := hA.prefix_gt (true :: pre.flatten).length (by simp) hlen
      rw [hs, hbf, ← List.cons_append, List.take_left] at h
      exact h
    · have hs' : s = true :: ((pre ++ [b]).flatten ++ []) := by
        rw [hs]
        simp
      refine ⟨pre ++ [b], [], hs', ?_, Or.inl rfl, ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with hc' | hc'
        · exact hpre c hc'
        · rw [List.mem_singleton] at hc'
          rw [hc']
          exact ⟨hbA, hbpos⟩
      · have hP := hA.lt_one
        have hflat : true :: (pre ++ [b]).flatten = s := by
          rw [hs]
          simp
        rw [hflat]
        constructor
        · intro h
          simp at h
        · intro h
          linarith

/-- Length of concatenated chain blocks: the sum of p2 of their Orders. -/
theorem length_flatten_chain (bs : List (List Bool)) (hbs : ∀ b ∈ bs, IsChainBlock b) :
    bs.flatten.length = (bs.map (fun b => p2_of (order b))).sum := by
  induction bs with
  | nil =>
    simp
  | cons b t ih =>
    rw [List.flatten_cons, List.length_append, List.map_cons, List.sum_cons,
      admissible_length b (hbs b List.mem_cons_self).adm,
      ih (fun c hc => hbs c (List.mem_cons_of_mem b hc))]

/-- p2 form of the tail: t = [0] iff p2(1 + Σ o_i) = 2 + Σ p2(o_i), o_i the chain Orders. -/
theorem tail_eq_zero_iff (bs : List (List Bool)) (t : List Bool)
    (hbs : ∀ b ∈ bs, IsChainBlock b) (ht : t = [] ∨ t = [false])
    (hA : Admissible (true :: (bs.flatten ++ t))) :
    t = [false] ↔
      p2_of (1 + (bs.map order).sum) = 2 + (bs.map (fun b => p2_of (order b))).sum := by
  have hlen := admissible_length _ hA
  have hord : order (true :: (bs.flatten ++ t)) = 1 + (bs.map order).sum := by
    rcases ht with rfl | rfl
    · rw [order_cons, List.append_nil, order_flatten]
      simp only [↓reduceIte]
      omega
    · rw [order_cons, order_append, order_flatten]
      simp [order]
      omega
  rw [hord, List.length_cons, List.length_append, length_flatten_chain bs hbs] at hlen
  rw [← hlen]
  rcases ht with rfl | rfl
  · simp only [List.length_nil, reduceCtorEq, false_iff]
    omega
  · simp only [List.length_singleton, true_iff]
    omega

/-!
## Validity depends on the Orders only

Whether chain blocks assembleChain into an admissible word depends only on their
Orders o₁, …, oₖ: `ValidOrders` checks 2^(1 + Σ p2(oᵢ)) < 3^(1 + Σ oᵢ) at
every inner boundary. Uniqueness and the converse complete the decomposition.
-/

/-- Level after a leading 1 and blocks of Orders os is > 1. -/
def LevelUp (os : List ℕ) : Prop :=
  2 ^ (1 + (os.map p2_of).sum) < 3 ^ (1 + os.sum)

/-- LevelUp at every inner boundary 1 ≤ i < |os|. -/
def ValidOrders (os : List ℕ) : Prop :=
  ∀ i, 1 ≤ i → i < os.length → LevelUp (os.take i)

/-- Order of 1 :: blocks: 1 plus the sum of the block Orders. -/
theorem order_cons_flatten (bs : List (List Bool)) :
    order (true :: bs.flatten) = 1 + (bs.map order).sum := by
  grind [order_cons, order_flatten]

/-- The level after 1 :: blocks is > 1 iff `LevelUp` holds for their Orders. -/
theorem one_lt_level_iff (bs : List (List Bool)) (hbs : ∀ b ∈ bs, IsChainBlock b) :
    1 < seqProduct (true :: bs.flatten) ↔ LevelUp (bs.map order) := by
  rw [one_lt_seqProduct_iff, order_cons_flatten, List.length_cons,
    length_flatten_chain bs hbs, LevelUp, List.map_map]
  rw [Nat.add_comm _ 1]
  rfl

/-- The levels at all inner block boundaries are > 1 iff the Orders are valid. -/
theorem inner_levels_iff (bs : List (List Bool)) (hbs : ∀ b ∈ bs, IsChainBlock b) :
    (∀ i, 1 ≤ i → i < bs.length → 1 < seqProduct (true :: (bs.take i).flatten)) ↔
      ValidOrders (bs.map order) := by
  have htake : ∀ i, ∀ b ∈ bs.take i, IsChainBlock b :=
    fun i b hb => hbs b (List.mem_of_mem_take hb)
  constructor
  · intro h i hi hil
    rw [List.length_map] at hil
    rw [← List.map_take, ← one_lt_level_iff _ (htake i)]
    exact h i hi hil
  · intro h i hi hil
    rw [one_lt_level_iff _ (htake i), List.map_take]
    have hil' : i < (bs.map order).length := by
      rw [List.length_map]
      exact hil
    exact h i hi hil'

/-- Chains of blocks with tails in {[], [0]} that flatten to the same word are equal. -/
theorem chain_unique (bs bs' : List (List Bool)) (t t' : List Bool)
    (hbs : ∀ b ∈ bs, IsChainBlock b) (hbs' : ∀ b ∈ bs', IsChainBlock b)
    (ht : t = [] ∨ t = [false]) (ht' : t' = [] ∨ t' = [false])
    (h : bs.flatten ++ t = bs'.flatten ++ t') : bs = bs' ∧ t = t' := by
  have hfl : ∀ (cs : List (List Bool)) (u : List Bool), (u = [] ∨ u = [false]) →
      cs.flatten ++ u = (cs ++ (if u = [] then [] else [[false]])).flatten := by
    intro cs u hu
    rcases hu with rfl | rfl
    · simp
    · simp
  have hadm : ∀ (cs : List (List Bool)) (u : List Bool), (∀ c ∈ cs, IsChainBlock c) →
      ∀ c ∈ cs ++ (if u = [] then [] else [[false]]), Admissible c := by
    intro cs u hcs c hc
    rcases List.mem_append.mp hc with hc' | hc'
    · exact (hcs c hc').1
    · split_ifs at hc' with hu
      · simp at hc'
      · rw [List.mem_singleton] at hc'
        rw [hc']
        exact admissible_singleton_false
  have heq := flatten_inj_of_admissible _ _ (hadm bs t hbs) (hadm bs' t' hbs')
    (by rw [← hfl bs t ht, ← hfl bs' t' ht', h])
  have hnot : ∀ (cs : List (List Bool)), (∀ c ∈ cs, IsChainBlock c) → [false] ∉ cs := by
    intro cs hcs hmem
    have h1 := (hcs [false] hmem).order_pos
    simp [order] at h1
  rcases ht with rfl | rfl
  · rcases ht' with rfl | rfl
    · simpa using heq
    · simp only [↓reduceIte, List.append_nil, reduceCtorEq] at heq
      exact absurd (heq ▸ List.mem_append_right bs' (List.mem_singleton_self _)) (hnot bs hbs)
  · rcases ht' with rfl | rfl
    · simp only [↓reduceIte, List.append_nil, reduceCtorEq] at heq
      exact absurd (heq ▸ List.mem_append_right bs (List.mem_singleton_self _)) (hnot bs' hbs')
    · simp only [reduceCtorEq, ↓reduceIte, List.append_cancel_right_eq] at heq
      exact ⟨heq, rfl⟩

/-- Chain characterization: admissible PVs of Order ≥ 1 are exactly 1 :: (chain ++ tail)
    with valid Orders, tail determined by `LevelUp` of all Orders. -/
theorem admissible_iff_chain (s : List Bool) :
    (Admissible s ∧ 1 ≤ order s) ↔
      ∃ (bs : List (List Bool)) (t : List Bool),
        s = true :: (bs.flatten ++ t) ∧ (∀ b ∈ bs, IsChainBlock b) ∧
        ValidOrders (bs.map order) ∧
        ((LevelUp (bs.map order) ∧ t = [false]) ∨ (¬ LevelUp (bs.map order) ∧ t = [])) := by
  constructor
  · rintro ⟨hA, hord⟩
    obtain ⟨bs, t, hs, hbs, ht, htiff⟩ := exists_chain s hA hord
    refine ⟨bs, t, hs, hbs, ?_, ?_⟩
    · rw [← inner_levels_iff bs hbs]
      intro i hi hil
      rcases ht with rfl | rfl
      · rw [List.append_nil] at hs
        rw [hs] at hA
        exact ((admissible_split_iff bs (fun b hb => (hbs b hb).adm)).mp hA).1 i hi hil
      · have hA' : Admissible (true :: (bs ++ [[false]]).flatten) := by
          rw [hs] at hA
          simpa using hA
        have hsA : ∀ b ∈ bs ++ [[false]], Admissible b := by
          intro b hb
          rcases List.mem_append.mp hb with hb' | hb'
          · exact (hbs b hb').adm
          · rw [List.mem_singleton] at hb'
            rw [hb']
            exact admissible_singleton_false
        have hil' : i < (bs ++ [[false]]).length := by
          rw [List.length_append]
          omega
        have h := ((admissible_split_iff _ hsA).mp hA').1 i hi hil'
        rw [List.take_append_of_le_length hil.le] at h
        exact h
    · rw [← one_lt_level_iff bs hbs, ← htiff]
      rcases ht with rfl | rfl
      · right
        exact ⟨by simp, rfl⟩
      · left
        exact ⟨rfl, rfl⟩
  · rintro ⟨bs, t, rfl, hbs, hvalid, htail⟩
    have hinner := (inner_levels_iff bs hbs).mpr hvalid
    have hparts := admissible_chain bs hbs hinner
    refine ⟨?_, ?_⟩
    · rcases htail with ⟨hup, rfl⟩ | ⟨hup, rfl⟩
      · exact hparts.2 ((one_lt_level_iff bs hbs).mpr hup)
      · rw [List.append_nil]
        apply hparts.1
        have hne := seqProduct_ne_one (true :: bs.flatten) (List.cons_ne_nil _ _)
        have hng : ¬ 1 < seqProduct (true :: bs.flatten) := by
          rw [one_lt_level_iff bs hbs]
          exact hup
        rcases lt_trichotomy (seqProduct (true :: bs.flatten)) 1 with hl | he | hg
        · exact hl
        · exact absurd he hne
        · exact absurd hg hng
    · rw [order_cons]
      simp

/-- `LevelUp` is decidable. -/
instance (os : List ℕ) : Decidable (LevelUp os) := by
  unfold LevelUp
  infer_instance

/-- `ValidOrders` is decidable. -/
instance (os : List ℕ) : Decidable (ValidOrders os) := by
  unfold ValidOrders
  infer_instance

/-!
## Counting: composition recursion for A100982

`admSet n` is the finite set of admissible words of Order n, so
`(admSet n).card` = A100982(n). Assembling blocks over all valid
compositions gives a(n + 1) = Σ Π a(oᵢ).
-/

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

/-- Admissible PVs of Order n. -/
def admSet (n : ℕ) : Finset (List Bool) :=
  (allBits (p2_of n)).toFinset.filter (fun s => Admissible s ∧ order s = n)

/-- Membership in `admSet n`. -/
theorem mem_admSet (n : ℕ) (s : List Bool) : s ∈ admSet n ↔ Admissible s ∧ order s = n := by
  simp only [admSet, Finset.mem_filter, List.mem_toFinset, mem_allBits]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    rw [admissible_length s h.1, h.2]

/-- Compositions of n with positive parts (fuel f ≥ n). -/
def compsAux : ℕ → ℕ → List (List ℕ)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | f + 1, n + 1 =>
    (List.range (n + 1)).flatMap (fun j => (compsAux f (n - j)).map (List.cons (j + 1)))

/-- Compositions of n with positive parts. -/
def comps (n : ℕ) : List (List ℕ) := compsAux n n

/-- Membership in `compsAux f n` for n ≤ f. -/
theorem mem_compsAux : ∀ (f n : ℕ), n ≤ f → ∀ os : List ℕ,
    os ∈ compsAux f n ↔ (∀ o ∈ os, 1 ≤ o) ∧ os.sum = n
  | f, 0, _, os => by
    cases f with
    | zero =>
      cases os with
      | nil =>
        simp [compsAux]
      | cons o t =>
        constructor
        · intro h
          simp [compsAux] at h
        · rintro ⟨h1, h2⟩
          have := h1 o List.mem_cons_self
          rw [List.sum_cons] at h2
          omega
    | succ f =>
      cases os with
      | nil =>
        simp [compsAux]
      | cons o t =>
        constructor
        · intro h
          simp [compsAux] at h
        · rintro ⟨h1, h2⟩
          have := h1 o List.mem_cons_self
          rw [List.sum_cons] at h2
          omega
  | 0, n + 1, h, _ => by
    omega
  | f + 1, n + 1, h, os => by
    simp only [compsAux, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨j, hj, t, ht, rfl⟩
      rw [mem_compsAux f (n - j) (by omega) t] at ht
      refine ⟨?_, ?_⟩
      · intro o ho
        rcases List.mem_cons.mp ho with rfl | ho'
        · omega
        · exact ht.1 o ho'
      · rw [List.sum_cons, ht.2]
        omega
    · rintro ⟨hpos, hsum⟩
      cases os with
      | nil =>
        simp at hsum
      | cons o t =>
        have ho := hpos o List.mem_cons_self
        rw [List.sum_cons] at hsum
        refine ⟨o - 1, by omega, t, ?_, by rw [Nat.sub_add_cancel ho]⟩
        rw [mem_compsAux f (n - (o - 1)) (by omega) t]
        refine ⟨fun x hx => hpos x (List.mem_cons_of_mem o hx), ?_⟩
        omega

/-- Membership in `comps n`. -/
theorem mem_comps (n : ℕ) (os : List ℕ) :
    os ∈ comps n ↔ (∀ o ∈ os, 1 ≤ o) ∧ os.sum = n :=
  mem_compsAux n n le_rfl os

/-- Block lists with Orders os, every block admissible. -/
def blockSet : List ℕ → Finset (List (List Bool))
  | [] => {[]}
  | o :: os => (admSet o ×ˢ blockSet os).image (fun p => p.1 :: p.2)

/-- Membership in `blockSet os`. -/
theorem mem_blockSet : ∀ (os : List ℕ) (bs : List (List Bool)),
    bs ∈ blockSet os ↔ bs.map order = os ∧ ∀ b ∈ bs, Admissible b
  | [], bs => by
    cases bs with
    | nil =>
      simp [blockSet]
    | cons b t =>
      simp [blockSet]
  | o :: os, bs => by
    simp only [blockSet, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨b, t, ⟨hb, ht⟩, rfl⟩
      rw [mem_admSet] at hb
      rw [mem_blockSet os t] at ht
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
        · rw [mem_admSet]
          exact ⟨hadm b List.mem_cons_self, hmap.1⟩
        · rw [mem_blockSet os t]
          exact ⟨hmap.2, fun c hc => hadm c (List.mem_cons_of_mem b hc)⟩

/-- Number of block lists with Orders os: the product of a(o). -/
theorem card_blockSet : ∀ os : List ℕ,
    (blockSet os).card = (os.map (fun o => (admSet o).card)).prod
  | [] => by
    simp [blockSet]
  | o :: os => by
    rw [blockSet, Finset.card_image_of_injective, Finset.card_product, card_blockSet os,
      List.map_cons, List.prod_cons]
    intro p q h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2

/-- Valid compositions of n. -/
def validComps (n : ℕ) : Finset (List ℕ) :=
  (comps n).toFinset.filter ValidOrders

/-- Chain assembly map: Orders os and blocks bs to 1 :: (bs ++ tail). -/
def assembleChain (p : Σ _ : List ℕ, List (List Bool)) : List Bool :=
  true :: (p.2.flatten ++ (if LevelUp p.1 then [false] else []))

/-- Blocks with Orders ≥ 1 are chain blocks. -/
theorem chainBlocks_of_mem (os : List ℕ) (bs : List (List Bool)) (hos : ∀ o ∈ os, 1 ≤ o)
    (hbs : bs ∈ blockSet os) : ∀ b ∈ bs, IsChainBlock b := by
  rw [mem_blockSet] at hbs
  intro b hb
  refine ⟨hbs.2 b hb, ?_⟩
  apply hos
  rw [← hbs.1]
  exact List.mem_map_of_mem hb

/-- A100982 recursion: |admSet (n+1)| = Σ over valid compositions os of n of ∏ |admSet o_i|. -/
theorem card_admSet_succ (n : ℕ) :
    (admSet (n + 1)).card =
      ∑ os ∈ validComps n, (os.map (fun o => (admSet o).card)).prod := by
  have himg : ((validComps n).sigma blockSet).image assembleChain = admSet (n + 1) := by
    ext s
    simp only [Finset.mem_image, Finset.mem_sigma, validComps, Finset.mem_filter,
      List.mem_toFinset, mem_comps, mem_admSet, Sigma.exists]
    constructor
    · rintro ⟨os, bs, ⟨⟨⟨hpos, hsum⟩, hvalid⟩, hbs⟩, rfl⟩
      have hcb := chainBlocks_of_mem os bs hpos hbs
      have hmap := ((mem_blockSet os bs).mp hbs).1
      have hvalid' : ValidOrders (bs.map order) := by
        rw [hmap]
        exact hvalid
      have htail : (LevelUp (bs.map order) ∧ (if LevelUp os then [false] else []) = [false]) ∨
          (¬ LevelUp (bs.map order) ∧ (if LevelUp os then [false] else []) = []) := by
        rw [hmap]
        by_cases hl : LevelUp os
        · left
          exact ⟨hl, by simp [hl]⟩
        · right
          exact ⟨hl, by simp [hl]⟩
      have hA := (admissible_iff_chain (assembleChain ⟨os, bs⟩)).mpr
        ⟨bs, if LevelUp os then [false] else [], rfl, hcb, hvalid', htail⟩
      refine ⟨hA.1, ?_⟩
      have htl : order (if LevelUp os then [false] else []) = 0 := by
        split_ifs
        · simp [order]
        · simp [order]
      have hord : order (assembleChain ⟨os, bs⟩) = 1 + (bs.map order).sum := by
        unfold assembleChain
        rw [order_cons, order_append, order_flatten, htl]
        simp only [↓reduceIte]
        omega
      rw [hord, hmap, hsum]
      omega
    · rintro ⟨hA, hord⟩
      obtain ⟨bs, t, hs, hcb, hvalid, htail⟩ :=
        (admissible_iff_chain s).mp ⟨hA, by omega⟩
      have htl : order t = 0 := by
        rcases htail with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · simp [order]
        · simp [order]
      have hord' : order s = 1 + (bs.map order).sum := by
        rw [hs, order_cons, order_append, order_flatten, htl]
        simp only [↓reduceIte]
        omega
      refine ⟨bs.map order, bs, ⟨⟨⟨?_, ?_⟩, hvalid⟩, ?_⟩, ?_⟩
      · intro o ho
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ho
        exact (hcb b hb).2
      · omega
      · rw [mem_blockSet]
        exact ⟨rfl, fun b hb => (hcb b hb).1⟩
      · unfold assembleChain
        rw [hs]
        rcases htail with ⟨hl, rfl⟩ | ⟨hl, rfl⟩
        · simp [hl]
        · simp [hl]
  have hinj : Set.InjOn assembleChain ((validComps n).sigma blockSet) := by
    rintro ⟨os, bs⟩ hp ⟨os', bs'⟩ hq h
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, validComps,
      Finset.mem_filter, List.mem_toFinset, mem_comps] at hp hq
    obtain ⟨⟨⟨hpos, _⟩, _⟩, hbs⟩ := hp
    obtain ⟨⟨⟨hpos', _⟩, _⟩, hbs'⟩ := hq
    have hcb := chainBlocks_of_mem os bs hpos hbs
    have hcb' := chainBlocks_of_mem os' bs' hpos' hbs'
    have hmap := ((mem_blockSet os bs).mp hbs).1
    have hmap' := ((mem_blockSet os' bs').mp hbs').1
    unfold assembleChain at h
    rw [List.cons.injEq] at h
    have ht : ∀ o : List ℕ, (if LevelUp o then [false] else []) = [] ∨
        (if LevelUp o then [false] else []) = [false] := by
      intro o
      by_cases hl : LevelUp o
      · right
        simp [hl]
      · left
        simp [hl]
    obtain ⟨hbb, _⟩ := chain_unique bs bs' _ _ hcb hcb' (ht os) (ht os') h.2
    subst hbb
    have hos : os = os' := by
      rw [← hmap, ← hmap']
    subst hos
    rfl
  rw [← himg, Finset.card_image_of_injOn hinj, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro os _
  exact card_blockSet os

/-!
## First-passage binomial identity

The C(p2(n) - 1, n - 1) words of length p2(n) and Order n that start with 1
split uniquely at their first passage below 1: an admissible prefix of some
Order i ≤ n, then an arbitrary rest.
-/

/-- 3^k < 2^p2(k). -/
theorem three_pow_lt_two_pow_p2 (k : ℕ) : 3 ^ k < 2 ^ p2_of k :=
  Nat.lt_pow_succ_log_self (by norm_num) _

/-- p2 is monotone in one step. -/
theorem p2_of_le_succ (k : ℕ) : p2_of k ≤ p2_of (k + 1) := by
  have h : Nat.log 2 (3 ^ k) ≤ Nat.log 2 (3 ^ (k + 1)) :=
    Nat.log_mono_right (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [p2_of]
  omega

/-- Bit strings of length L and Order w. -/
def wordSet (L w : ℕ) : Finset (List Bool) :=
  (allBits L).toFinset.filter (fun s => order s = w)

/-- Membership in `wordSet L w`. -/
theorem mem_wordSet (L w : ℕ) (s : List Bool) :
    s ∈ wordSet L w ↔ s.length = L ∧ order s = w := by
  simp [wordSet, mem_allBits]

/-- Words of `wordSet (L+1) (w+1)` starting with 1: 1 :: `wordSet L w`. -/
theorem wordSet_head_true (L w : ℕ) :
    (wordSet (L + 1) (w + 1)).filter (fun s => s.head? = some true) =
      (wordSet L w).image (List.cons true) := by
  ext s
  cases s with
  | nil =>
    simp
  | cons b t =>
    cases b
    · simp
    · simp [mem_wordSet, order_cons]

/-- No word of Order 0 starts with 1. -/
theorem wordSet_head_true_zero (L : ℕ) :
    (wordSet (L + 1) 0).filter (fun s => s.head? = some true) = ∅ := by
  ext s
  cases s with
  | nil =>
    simp
  | cons b t =>
    cases b
    · simp
    · simp [mem_wordSet, order_cons]

/-- Words of `wordSet (L+1) w` starting with 0: 0 :: `wordSet L w`. -/
theorem wordSet_head_false (L w : ℕ) :
    (wordSet (L + 1) w).filter (fun s => ¬ s.head? = some true) =
      (wordSet L w).image (List.cons false) := by
  ext s
  cases s with
  | nil =>
    simp [mem_wordSet]
  | cons b t =>
    cases b
    · simp [mem_wordSet, order_cons]
    · simp

/-- |`wordSet L w`| = C(L, w). -/
theorem card_wordSet : ∀ L w : ℕ, (wordSet L w).card = L.choose w
  | 0, w => by
    cases w with
    | zero =>
      rfl
    | succ w =>
      rfl
  | L + 1, w => by
    rw [← Finset.card_filter_add_card_filter_not (fun s => s.head? = some true),
      wordSet_head_false, Finset.card_image_of_injective _ (List.cons_injective), card_wordSet L w]
    cases w with
    | zero =>
      rw [wordSet_head_true_zero]
      simp
    | succ w =>
      rw [wordSet_head_true, Finset.card_image_of_injective _ (List.cons_injective),
        card_wordSet L w, Nat.choose_succ_succ']

/-- p2 is monotone. -/
theorem p2_of_mono {i n : ℕ} (h : i ≤ n) : p2_of i ≤ p2_of n :=
  monotone_nat_of_le_succ p2_of_le_succ h

/-- Strings of length p2(n) and Order n starting with 1. -/
def startWords (n : ℕ) : Finset (List Bool) :=
  (wordSet (p2_of n - 1) (n - 1)).image (List.cons true)

/-- Membership in `startWords n`. -/
theorem mem_startWords (n : ℕ) (hn : 1 ≤ n) (s : List Bool) :
    s ∈ startWords n ↔ (∃ u, s = true :: u) ∧ s.length = p2_of n ∧ order s = n := by
  have hp : 1 ≤ p2_of n := by
    simp [p2_of]
  simp only [startWords, Finset.mem_image, mem_wordSet]
  constructor
  · rintro ⟨u, ⟨hl, ho⟩, rfl⟩
    refine ⟨⟨u, rfl⟩, ?_, ?_⟩
    · rw [List.length_cons]
      omega
    · rw [order_cons]
      simp only [↓reduceIte]
      omega
  · rintro ⟨⟨u, rfl⟩, hl, ho⟩
    rw [List.length_cons] at hl
    rw [order_cons] at ho
    simp only [↓reduceIte] at ho
    exact ⟨u, ⟨by omega, by omega⟩, rfl⟩

/-- First-drop decomposition domain: Order i, admissible prefix, arbitrary rest. -/
def firstPassageSplits (n : ℕ) : Finset (Σ _ : ℕ, List Bool × List Bool) :=
  (Finset.Icc 1 n).sigma (fun i => admSet i ×ˢ wordSet (p2_of n - p2_of i) (n - i))

/-- Size of the first-passage domain. -/
theorem card_firstPassageSplits (n : ℕ) :
    (firstPassageSplits n).card =
      ∑ i ∈ Finset.Icc 1 n, (admSet i).card * (p2_of n - p2_of i).choose (n - i) := by
  rw [firstPassageSplits, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_product, card_wordSet]

/-- First drop of a string starting with 1, of length p2(n) and Order n. -/
theorem exists_first_drop (n : ℕ) (hn : 1 ≤ n) (s : List Bool) (hs : s ∈ startWords n) :
    ∃ m, 1 ≤ m ∧ m ≤ s.length ∧ Admissible (s.take m) := by
  rw [mem_startWords n hn] at hs
  obtain ⟨⟨u, rfl⟩, hl, ho⟩ := hs
  have hex : ∃ m, seqProduct ((true :: u).take m) < 1 := by
    refine ⟨(true :: u).length, ?_⟩
    rw [List.take_length, seqProduct_lt_one_iff, hl, ho]
    exact three_pow_lt_two_pow_p2 n
  classical
  set m := Nat.find hex with hm_def
  have hspec : seqProduct ((true :: u).take m) < 1 := Nat.find_spec hex
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0, List.take_zero] at hspec
    simp [seqProduct] at hspec
  have hmle : m ≤ (true :: u).length := Nat.find_min' hex (by
    rw [List.take_length, seqProduct_lt_one_iff, hl, ho]
    exact three_pow_lt_two_pow_p2 n)
  refine ⟨m, hm1, hmle, ?_, hspec⟩
  intro k hk1 hkl
  rw [List.length_take, min_eq_left hmle] at hkl
  have hnot : ¬ seqProduct ((true :: u).take k) < 1 := Nat.find_min hex hkl
  rw [List.take_take, min_eq_left hkl.le]
  have hne : (true :: u).take k ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with h | h
    · omega
    · simp at h
  have hne1 := seqProduct_ne_one _ hne
  rcases lt_trichotomy (seqProduct ((true :: u).take k)) 1 with h | h | h
  · exact absurd h hnot
  · exact absurd h hne1
  · exact h

/-- A100982 binomial identity: C(p2(n) - 1, n - 1) = Σ_{i=1..n} a(i) C(p2(n) - p2(i), n - i). -/
theorem choose_eq_sum_admSet (n : ℕ) (hn : 1 ≤ n) :
    (p2_of n - 1).choose (n - 1) =
      ∑ i ∈ Finset.Icc 1 n, (admSet i).card * (p2_of n - p2_of i).choose (n - i) := by
  have hstart : (startWords n).card = (p2_of n - 1).choose (n - 1) := by
    rw [startWords, Finset.card_image_of_injective _ (List.cons_injective), card_wordSet]
  have himg : (firstPassageSplits n).image (fun p => p.2.1 ++ p.2.2) = startWords n := by
    ext s
    simp only [Finset.mem_image, firstPassageSplits, Finset.mem_sigma, Finset.mem_Icc,
      Finset.mem_product,
      mem_admSet, mem_wordSet, Sigma.exists, Prod.exists]
    constructor
    · rintro ⟨i, a, r, ⟨⟨hi1, hin⟩, ⟨hA, hoa⟩, hlr, hor⟩, rfl⟩
      rw [mem_startWords n hn]
      obtain ⟨u, rfl⟩ := admissible_cons_true a hA (by omega)
      refine ⟨⟨u ++ r, rfl⟩, ?_, ?_⟩
      · have hla := admissible_length _ hA
        rw [hoa] at hla
        have hmono := p2_of_mono hin
        rw [List.length_append, hla, hlr]
        omega
      · rw [order_append, hoa, hor]
        omega
    · intro hs
      obtain ⟨m, hm1, hml, hA⟩ := exists_first_drop n hn s hs
      rw [mem_startWords n hn] at hs
      obtain ⟨⟨u, rfl⟩, hl, ho⟩ := hs
      set a := (true :: u).take m with ha_def
      set r := (true :: u).drop m with hr_def
      have hsplit : a ++ r = true :: u := List.take_append_drop m _
      have hord := order_append a r
      rw [hsplit] at hord
      have hla := admissible_length a hA
      have hlen : a.length + r.length = (true :: u).length := by
        rw [← List.length_append, hsplit]
      have hoa1 : 1 ≤ order a := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hm1
        rw [ha_def, hk, List.take_succ_cons, order_cons]
        simp
      refine ⟨order a, a, r, ⟨⟨hoa1, by omega⟩, ⟨hA, rfl⟩, ?_, by omega⟩, hsplit⟩
      rw [hla] at hlen
      omega
  have hinj : Set.InjOn (fun p : (Σ _ : ℕ, List Bool × List Bool) => p.2.1 ++ p.2.2)
      (firstPassageSplits n) := by
    rintro ⟨i, a, r⟩ hp ⟨i', a', r'⟩ hq h
    simp only [firstPassageSplits, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe,
      Finset.mem_Icc,
      Finset.mem_product, mem_admSet, mem_wordSet] at hp hq h
    obtain ⟨_, ⟨ha, hoa⟩, _⟩ := hp
    obtain ⟨_, ⟨ha', hoa'⟩, _⟩ := hq
    have hpre : a <+: a ++ r := List.prefix_append a r
    have hpre' : a' <+: a ++ r := by
      rw [h]
      exact List.prefix_append a' r'
    have haa : a = a' := by
      by_contra hne
      rcases le_total a.length a'.length with hle | hle
      · exact admissible_not_prefix a a' ha ha' hne
          (List.prefix_of_prefix_length_le hpre hpre' hle)
      · exact admissible_not_prefix a' a ha' ha (Ne.symm hne)
          (List.prefix_of_prefix_length_le hpre' hpre hle)
    subst haa
    have hrr : r = r' := List.append_cancel_left h
    subst hrr
    have hii : i = i' := by
      rw [← hoa, ← hoa']
    subst hii
    rfl
  rw [← hstart, ← himg, Finset.card_image_of_injOn hinj, card_firstPassageSplits]

/-!
## Range form (M. Winkler)

With m(i) = p2(i) - 1: for every M ≥ m(n - 1),
C(M, n - 1) = a(n) + Σ_{i<n} a(i) C(M - m(i), n - i). Induction on n via
Pascal's rule in M, anchored at the identity of the previous section (M = m(n)).
-/

/-- Right-hand side of the range identity. -/
def rangeSum (n M : ℕ) : ℕ :=
  (admSet n).card +
    ∑ i ∈ Finset.Ico 1 n, (admSet i).card * (M - (p2_of i - 1)).choose (n - i)

/-- p2(k) ≥ 1. -/
theorem one_le_p2_of (k : ℕ) : 1 ≤ p2_of k := by
  simp [p2_of]

/-- The anchor M = m(n): `choose_eq_sum_admSet` in range form. -/
theorem rangeSum_anchor (n : ℕ) (hn : 1 ≤ n) :
    (p2_of n - 1).choose (n - 1) = rangeSum n (p2_of n - 1) := by
  rw [choose_eq_sum_admSet n hn, rangeSum]
  have hIcc : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by
    rw [← Finset.Ico_insert_right hn]
  rw [hIcc, Finset.sum_insert Finset.right_notMem_Ico]
  simp only [Nat.sub_self, Nat.choose_zero_right, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 := one_le_p2_of i
  have hi2 := one_le_p2_of n
  congr 2
  omega

/-- Pascal step in M: rangeSum (n + 1) (M + 1) = rangeSum (n + 1) M + rangeSum n M. -/
theorem rangeSum_succ (n M : ℕ) (hn : 1 ≤ n) (hM : p2_of n - 1 ≤ M) :
    rangeSum (n + 1) (M + 1) = rangeSum (n + 1) M + rangeSum n M := by
  have hstep : ∀ i ∈ Finset.Ico 1 (n + 1),
      (admSet i).card * (M + 1 - (p2_of i - 1)).choose (n + 1 - i) =
        (admSet i).card * (M - (p2_of i - 1)).choose (n + 1 - i) +
          (admSet i).card * (M - (p2_of i - 1)).choose (n - i) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hmono := p2_of_mono (Nat.lt_succ_iff.mp hi.2)
    have hsub : M + 1 - (p2_of i - 1) = (M - (p2_of i - 1)) + 1 := by
      omega
    have hk : n + 1 - i = (n - i) + 1 := by
      omega
    rw [hsub, hk, Nat.choose_succ_succ', mul_add, add_comm]
  have hsplit :
      ∑ i ∈ Finset.Ico 1 (n + 1), (admSet i).card * (M - (p2_of i - 1)).choose (n - i) =
      ∑ i ∈ Finset.Ico 1 n, (admSet i).card * (M - (p2_of i - 1)).choose (n - i) +
        (admSet n).card := by
    rw [Finset.sum_Ico_succ_top hn]
    simp
  unfold rangeSum
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hsplit]
  ring

/-- Range identity (M. Winkler): C(M, n - 1) = a(n) + Σ_{i<n} a(i) C(M - m(i), n - i). -/
theorem choose_eq_sum_admSet_of_le (n : ℕ) (hn : 1 ≤ n) :
    ∀ M, p2_of (n - 1) - 1 ≤ M → M.choose (n - 1) = rangeSum n M := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro M _
    have h1 := rangeSum_anchor 1 le_rfl
    have hc : (admSet 1).card = 1 := by
      rw [rangeSum] at h1
      simpa using h1.symm
    simp [rangeSum, hc]
  | succ n hn ih =>
    have hsucc : n + 1 - 1 = n := by
      omega
    rw [hsucc]
    have hmono : p2_of n ≤ p2_of (n + 1) := p2_of_mono (Nat.le_add_right n 1)
    have hshift : ∀ k, (p2_of n - 1 + k + 1).choose n = rangeSum (n + 1) (p2_of n - 1 + k + 1) ↔
        (p2_of n - 1 + k).choose n = rangeSum (n + 1) (p2_of n - 1 + k) := by
      intro k
      have hle : p2_of (n - 1) - 1 ≤ p2_of n - 1 + k := by
        have := p2_of_mono (Nat.sub_le n 1)
        omega
      have hih := ih (p2_of n - 1 + k) hle
      have hn1 : n = (n - 1) + 1 := by
        omega
      rw [rangeSum_succ n _ hn (Nat.le_add_right _ _)]
      conv_lhs => rw [hn1, Nat.choose_succ_succ', ← hn1, hih]
      omega
    have hall : ∀ k, (p2_of n - 1 + k).choose n = rangeSum (n + 1) (p2_of n - 1 + k) ↔
        (p2_of n - 1).choose n = rangeSum (n + 1) (p2_of n - 1) := by
      intro k
      induction k with
      | zero =>
        rfl
      | succ k hk =>
        rw [← add_assoc, hshift k, hk]
    have hanchor := rangeSum_anchor (n + 1) (by omega)
    rw [hsucc] at hanchor
    have hbase : (p2_of n - 1).choose n = rangeSum (n + 1) (p2_of n - 1) := by
      have h := (hall (p2_of (n + 1) - 1 - (p2_of n - 1))).mp
      have heq : p2_of n - 1 + (p2_of (n + 1) - 1 - (p2_of n - 1)) = p2_of (n + 1) - 1 := by
        omega
      rw [heq] at h
      exact h hanchor
    intro M hM
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
    exact (hall k).mpr hbase

/-!
## Deficit budget

Every block lowers the level (3^o < 2^p2(o)), so the levels at the cuts decrease,
and validity needs checking only at the last inner cut:
`ValidOrders os ↔ LevelUp os.dropLast`. Equivalently, with d(o) = 1 - {o log₂ 3},
the deficits d(o_1) + ... + d(o_(k-1)) stay below the budget log₂ 3 - 1
(M. Winkler). In rational form, with the deficit ratio D(o) = 2^p2(o) / 3^o in
(1, 2]: validity iff 2 ∏_{i<k} D(o_i) < 3 (`validOrders_iff_budget`).
-/

/-- 3^(Σo) ≤ 2^(Σp2(o)): blocks never raise the level. -/
theorem three_pow_sum_le (os : List ℕ) : 3 ^ os.sum ≤ 2 ^ (os.map p2_of).sum := by
  induction os with
  | nil =>
    simp
  | cons o os ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, pow_add, pow_add]
    exact Nat.mul_le_mul (three_pow_lt_two_pow_p2 o).le ih

/-- `LevelUp` of a longer list implies it for a prefix. -/
theorem levelUp_of_append (a b : List ℕ) (h : LevelUp (a ++ b)) : LevelUp a := by
  unfold LevelUp at h ⊢
  rw [List.map_append, List.sum_append, List.sum_append, ← add_assoc, ← add_assoc,
    pow_add 2 (1 + (a.map p2_of).sum), pow_add 3 (1 + a.sum)] at h
  have hb := three_pow_sum_le b
  by_contra hcon
  have hge : 3 ^ (1 + a.sum) ≤ 2 ^ (1 + (a.map p2_of).sum) := Nat.le_of_not_lt hcon
  have hmul := Nat.mul_le_mul hge hb
  omega

/-- `LevelUp []`: the level 3/2 after the leading 1. -/
theorem levelUp_nil : LevelUp [] := by
  unfold LevelUp
  norm_num

/-- Deficit budget: the Orders are valid iff the level at the last inner cut is > 1. -/
theorem validOrders_iff_dropLast (os : List ℕ) : ValidOrders os ↔ LevelUp os.dropLast := by
  constructor
  · intro h
    rcases Nat.lt_or_ge os.length 2 with hlen | hlen
    · have hd : os.dropLast = [] := by
        rw [← List.length_eq_zero_iff, List.length_dropLast]
        omega
      rw [hd]
      exact levelUp_nil
    · have hi := h (os.length - 1) (by omega) (by omega)
      rwa [← List.dropLast_eq_take] at hi
  · intro h i hi1 hi
    have ht : os.dropLast.take i = os.take i := by
      rw [List.dropLast_eq_take, List.take_take, min_eq_left (by omega)]
    have hsplit : os.dropLast = os.take i ++ os.dropLast.drop i := by
      rw [← ht, List.take_append_drop]
    rw [hsplit] at h
    exact levelUp_of_append _ _ h

/-- `LevelUp` of all Orders (tail [0]) implies validity. -/
theorem validOrders_of_levelUp (os : List ℕ) (h : LevelUp os) : ValidOrders os := by
  rw [validOrders_iff_dropLast]
  apply levelUp_of_append os.dropLast (os.drop (os.length - 1))
  rwa [List.dropLast_eq_take, List.take_append_drop]

/-- Deficit ratio D(o) = 2^p2(o) / 3^o, the reciprocal of the block factor. -/
def deficitRatio (o : ℕ) : ℚ := 2 ^ p2_of o / 3 ^ o

/-- 1 < D(o): every block lowers the level. -/
theorem one_lt_deficitRatio (o : ℕ) : 1 < deficitRatio o := by
  unfold deficitRatio
  have h3 : (0 : ℚ) < 3 ^ o := by
    positivity
  have hlt : (3 : ℚ) ^ o < 2 ^ p2_of o := by
    exact_mod_cast three_pow_lt_two_pow_p2 o
  rw [lt_div_iff₀ h3, one_mul]
  exact hlt

/-- D(o) ≤ 2: a block at most halves the level. -/
theorem deficitRatio_le_two (o : ℕ) : deficitRatio o ≤ 2 := by
  unfold deficitRatio
  have h3 : (0 : ℚ) < 3 ^ o := by
    positivity
  have hn : (2 : ℚ) ^ Nat.log 2 (3 ^ o) ≤ 3 ^ o := by
    exact_mod_cast Nat.pow_log_le_self 2 (by positivity)
  rw [div_le_iff₀ h3, p2_of, pow_succ]
  linarith

/-- ∏ D(o_i) = 2^(Σ p2(o_i)) / 3^(Σ o_i). -/
theorem prod_deficitRatio (os : List ℕ) :
    (os.map deficitRatio).prod = 2 ^ (os.map p2_of).sum / 3 ^ os.sum := by
  induction os with
  | nil =>
    simp
  | cons o t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, List.sum_cons,
      pow_add, pow_add, deficitRatio, div_mul_div_comm]

/-- Budget form of `LevelUp`: 2 ∏ D(o_i) < 3. -/
theorem levelUp_iff_budget (os : List ℕ) :
    LevelUp os ↔ 2 * (os.map deficitRatio).prod < 3 := by
  rw [prod_deficitRatio]
  have h3 : (0 : ℚ) < 3 ^ os.sum := by
    positivity
  rw [← mul_div_assoc, div_lt_iff₀ h3]
  unfold LevelUp
  rw [pow_add, pow_add, pow_one, pow_one]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- Budget form of validity: 2 ∏_{i<k} D(o_i) < 3. -/
theorem validOrders_iff_budget (os : List ℕ) :
    ValidOrders os ↔ 2 * (os.dropLast.map deficitRatio).prod < 3 := by
  rw [validOrders_iff_dropLast, levelUp_iff_budget]

/-- Admissible words of Order ≥ 1 in budget form: chain blocks with
    2 ∏_{i<k} D(o_i) < 3, and tail [0] iff moreover 2 ∏_{i≤k} D(o_i) < 3. -/
theorem admissible_iff_chain_budget (s : List Bool) :
    (Admissible s ∧ 1 ≤ order s) ↔
      ∃ (bs : List (List Bool)) (t : List Bool),
        s = true :: (bs.flatten ++ t) ∧ (∀ b ∈ bs, IsChainBlock b) ∧
        2 * ((bs.map order).dropLast.map deficitRatio).prod < 3 ∧
        ((2 * ((bs.map order).map deficitRatio).prod < 3 ∧ t = [false]) ∨
          (¬ 2 * ((bs.map order).map deficitRatio).prod < 3 ∧ t = [])) := by
  simp only [← levelUp_iff_budget, ← validOrders_iff_dropLast]
  exact admissible_iff_chain s

/-!
## Cuts are record lows

A strict record-low time m of a word: the level after its first m letters is below
every earlier level. Appending an admissible block to a word whose level ends at
its minimum adds exactly one record low, at the block's end. So the cuts of the
chain decomposition are exactly the record-low times of the word, the tail [0]
counting as a last block (`exists_chain_recordLow`).
-/

/-- m is a strict record-low time of s: the level after m letters is below every
    earlier level. -/
def IsRecordLow (s : List Bool) (m : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ s.length ∧ ∀ j, 1 ≤ j → j < m → seqProduct (s.take m) < seqProduct (s.take j)

/-- The level at the end of w is at most every level along w. -/
def EndIsMin (w : List Bool) : Prop :=
  ∀ j, 1 ≤ j → j ≤ w.length → seqProduct w ≤ seqProduct (w.take j)

/-- Inside an appended admissible block the level stays above the block's start. -/
theorem seqProduct_lt_inside (w b : List Bool) (r : ℕ) (hb : Admissible b) (hr1 : 1 ≤ r)
    (hr : r < b.length) : seqProduct w < seqProduct ((w ++ b).take (w.length + r)) := by
  rw [List.take_length_add_append, seqProduct_append]
  exact lt_mul_of_one_lt_right (seqProduct_pos w) (hb.prefix_gt r hr1 hr)

/-- At the end of an appended admissible block the level is below the block's start. -/
theorem seqProduct_append_lt (w b : List Bool) (hb : Admissible b) :
    seqProduct (w ++ b) < seqProduct w := by
  rw [seqProduct_append]
  exact mul_lt_of_lt_one_right (seqProduct_pos w) hb.lt_one

/-- After an appended admissible block, the level ends at its minimum again. -/
theorem endIsMin_append (w b : List Bool) (hQ : EndIsMin w) (hb : Admissible b) :
    EndIsMin (w ++ b) := by
  intro j hj1 hj
  rw [List.length_append] at hj
  have hend := seqProduct_append_lt w b hb
  rcases Nat.lt_or_ge w.length j with hgt | hle
  · rcases Nat.lt_or_ge j (w.length + b.length) with hlt | hge
    · obtain ⟨r, rfl⟩ : ∃ r, j = w.length + r := ⟨j - w.length, by omega⟩
      have h := seqProduct_lt_inside w b r hb (by omega) (by omega)
      linarith
    · have hj' : j = (w ++ b).length := by
        rw [List.length_append]
        omega
      rw [hj', List.take_length]
  · rw [List.take_append_of_le_length hle]
    linarith [hQ j hj1 hle]

/-- Appending an admissible block adds exactly one record low, at its end. -/
theorem isRecordLow_append (w b : List Bool) (hw : w ≠ []) (hQ : EndIsMin w)
    (hb : Admissible b) (m : ℕ) :
    IsRecordLow (w ++ b) m ↔ IsRecordLow w m ∨ m = w.length + b.length := by
  have hwpos : 1 ≤ w.length := List.length_pos_iff.mpr hw
  have hend := seqProduct_append_lt w b hb
  constructor
  · rintro ⟨hm1, hmle, hlow⟩
    rw [List.length_append] at hmle
    rcases Nat.lt_or_ge w.length m with hgt | hle
    · right
      by_contra hne
      obtain ⟨r, rfl⟩ : ∃ r, m = w.length + r := ⟨m - w.length, by omega⟩
      have h1 := hlow w.length hwpos hgt
      rw [List.take_append_of_le_length le_rfl, List.take_length] at h1
      have h2 := seqProduct_lt_inside w b r hb (by omega) (by omega)
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
        have h := seqProduct_lt_inside w b r hb (by omega) (by omega)
        linarith
      · rw [List.take_append_of_le_length hle]
        linarith [hQ j hj1 hle]

/-- Record lows of w followed by admissible blocks: those of w, and the block ends. -/
theorem isRecordLow_append_flatten (cs : List (List Bool)) (hcs : ∀ c ∈ cs, Admissible c) :
    ∀ w : List Bool, w ≠ [] → EndIsMin w → ∀ m,
      (IsRecordLow (w ++ cs.flatten) m ↔
        IsRecordLow w m ∨
          ∃ i, 1 ≤ i ∧ i ≤ cs.length ∧ m = w.length + (cs.take i).flatten.length) := by
  induction cs with
  | nil =>
    intro w _ _ m
    simp
  | cons c cs ih =>
    intro w hw hQ m
    have hc : Admissible c := hcs c List.mem_cons_self
    have hcs' : ∀ c' ∈ cs, Admissible c' := fun c' h => hcs c' (List.mem_cons_of_mem c h)
    have hwc : w ++ c ≠ [] := by
      simp [hw]
    rw [List.flatten_cons, ← List.append_assoc,
      ih hcs' (w ++ c) hwc (endIsMin_append w c hQ hc) m,
      isRecordLow_append w c hw hQ hc m]
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
theorem isRecordLow_single (m : ℕ) : IsRecordLow [true] m ↔ m = 1 := by
  constructor
  · rintro ⟨hm1, hm, _⟩
    simp at hm
    omega
  · rintro rfl
    refine ⟨le_rfl, by simp, ?_⟩
    intro j hj1 hj
    omega

/-- [1] ends at its minimum level. -/
theorem endIsMin_single : EndIsMin [true] := by
  intro j hj1 hj
  simp at hj
  have hj' : j = 1 := by
    omega
  rw [hj']
  rfl

/-- The record-low times of 1 :: c_1 ... c_k (admissible c_i) are the cuts. -/
theorem isRecordLow_iff_cut (cs : List (List Bool)) (hcs : ∀ c ∈ cs, Admissible c) (m : ℕ) :
    IsRecordLow (true :: cs.flatten) m ↔
      ∃ i, i ≤ cs.length ∧ m = 1 + (cs.take i).flatten.length := by
  have h := isRecordLow_append_flatten cs hcs [true] (by simp) endIsMin_single m
  rw [List.singleton_append] at h
  rw [h, isRecordLow_single]
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

/-- The chain cuts of an admissible word are exactly its record-low times; the tail
    [0], if present, counts as a last block. -/
theorem exists_chain_recordLow (s : List Bool) (hA : Admissible s) (hord : 1 ≤ order s) :
    ∃ (bs : List (List Bool)) (t : List Bool),
      s = true :: (bs.flatten ++ t) ∧ (∀ b ∈ bs, IsChainBlock b) ∧ (t = [] ∨ t = [false]) ∧
      ∀ m, IsRecordLow s m ↔
        ∃ i, i ≤ (bs ++ t.map (fun _ => [false])).length ∧
          m = 1 + ((bs ++ t.map (fun _ => [false])).take i).flatten.length := by
  obtain ⟨bs, t, hs, hbs, ht, _⟩ := exists_chain s hA hord
  refine ⟨bs, t, hs, hbs, ht, ?_⟩
  have hflat : (bs ++ t.map (fun _ => [false])).flatten = bs.flatten ++ t := by
    rcases ht with rfl | rfl
    · simp
    · simp
  have hcs : ∀ c ∈ bs ++ t.map (fun _ => [false]), Admissible c := by
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact (hbs c hc).adm
    · rw [List.mem_map] at hc
      obtain ⟨_, _, rfl⟩ := hc
      exact admissible_singleton_false
  intro m
  rw [← isRecordLow_iff_cut _ hcs m, hflat, hs]

/-- `IsRecordLow` is decidable. -/
instance (s : List Bool) (m : ℕ) : Decidable (IsRecordLow s m) := by
  unfold IsRecordLow
  infer_instance

/-- The word 1100 (Order 2): block 10, tail [0]; record lows at 1, 3 and 4, not at 2. -/
example : Admissible [true, true, false, false] := by
  decide +kernel

example : IsRecordLow [true, true, false, false] 1 := by
  decide +kernel

example : ¬ IsRecordLow [true, true, false, false] 2 := by
  decide +kernel

example : IsRecordLow [true, true, false, false] 3 := by
  decide +kernel

example : IsRecordLow [true, true, false, false] 4 := by
  decide +kernel

/-!
## Main results in OEIS notation

`A100982 n` = a(n), the number of admissible words of Order n, and
m(j) = p2(j) - 1 = ⌊j log₂ 3⌋.
-/

/-- a(n) = A100982(n): the number of admissible words of Order n. -/
abbrev A100982 (n : ℕ) : ℕ := (admSet n).card

/-- m(j) = p2(j) - 1. -/
abbrev m (j : ℕ) : ℕ := p2_of j - 1

/-- a(n + 1) = Σ over valid compositions (o₁, …, oₖ) of n of Π a(oᵢ). -/
theorem A100982_succ (n : ℕ) :
    A100982 (n + 1) = ∑ os ∈ validComps n, (os.map A100982).prod :=
  card_admSet_succ n

/-- C(m(n), n - 1) = Σ_{i=1..n} a(i) C(m(n) - m(i), n - i). -/
theorem A100982_binomial (n : ℕ) (hn : 1 ≤ n) :
    (m n).choose (n - 1) = ∑ i ∈ Finset.Icc 1 n, A100982 i * (m n - m i).choose (n - i) := by
  unfold m
  rw [choose_eq_sum_admSet n hn]
  apply Finset.sum_congr rfl
  intro i _
  have hi := one_le_p2_of i
  have hn' := one_le_p2_of n
  congr 2
  omega

/-- For every M ≥ m(n - 1): C(M, n - 1) = a(n) + Σ_{i=1..n-1} a(i) C(M - m(i), n - i). -/
theorem A100982_range (n M : ℕ) (hn : 1 ≤ n) (hM : m (n - 1) ≤ M) :
    M.choose (n - 1) = A100982 n + ∑ i ∈ Finset.Ico 1 n, A100982 i * (M - m i).choose (n - i) :=
  choose_eq_sum_admSet_of_le n hn M hM

/-- Recurrence (M = m(n - 1)):
    a(n) = C(m(n - 1), n - 1) - Σ_{i=1..n-1} a(i) C(m(n - 1) - m(i), n - i). -/
theorem A100982_rec (n : ℕ) (hn : 1 ≤ n) :
    A100982 n = (m (n - 1)).choose (n - 1) -
      ∑ i ∈ Finset.Ico 1 n, A100982 i * (m (n - 1) - m i).choose (n - i) := by
  have h := A100982_range n (m (n - 1)) hn le_rfl
  omega

/-! ## Check: the first terms of A100982 -/

set_option linter.hashCommand false in
#guard (List.range 7).map (fun n => A100982 (n + 1)) = [1, 1, 2, 3, 7, 12, 30]

end ChainDecomposition
