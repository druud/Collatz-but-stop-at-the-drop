-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TEncode
import AcceleratedCollatz.Tree
import AcceleratedCollatz.TSieve

/-!
  sec:sorting (lexicographic enumeration). The accumulator tree
  (`treeLevel`, built from Tree.lean's `nextLevel` with increments
  p2(k+1) - p2(k)) has at level k exactly the encodings of the admissible
  sequences of Order k (`mem_treeLevel`), strictly increasing
  (`treeLevel_isChain_lt`). For equal lengths, increasing encodings are
  increasing lexicographic order (`encode_lt_iff_lex`).
  Parent/child in list form: parent a ++ 0^(i+1), child a ++ 1 :: 0^(i+m).
-/

namespace AcceleratedCollatz

variable (a : List Bool) (k : ℕ)

/-- Level k of the accumulator tree. -/
def treeLevel : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => nextLevel (treeLevel k) (p2_of (k + 1) - p2_of k)

/-- 3^k < 2^p2(k). -/
theorem two_pow_pred_p2_lt (hk : 1 ≤ k) : 2 ^ (p2_of k - 1) < 3 ^ k := by
  have hle : 2 ^ Nat.log 2 (3 ^ k) ≤ 3 ^ k := Nat.pow_log_le_self 2 (by positivity)
  have hp : p2_of k - 1 = Nat.log 2 (3 ^ k) := by
    simp [p2_of]
  rw [hp]
  rcases Nat.lt_or_ge (2 ^ Nat.log 2 (3 ^ k)) (3 ^ k) with h | h
  · exact h
  · exfalso
    have heq : 2 ^ Nat.log 2 (3 ^ k) = 3 ^ k := le_antisymm hle h
    have hodd : (3 ^ k) % 2 = 1 := Nat.odd_iff.mp ((by decide : Odd 3).pow)
    have hpos : 1 ≤ Nat.log 2 (3 ^ k) := by
      apply Nat.le_log_of_pow_le (by norm_num)
      calc 2 ^ 1 ≤ 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have heven : (2 ^ Nat.log 2 (3 ^ k)) % 2 = 0 := by
      obtain ⟨e, he⟩ : ∃ e, Nat.log 2 (3 ^ k) = e + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [he, pow_succ]
      simp
    omega

/-- p2 is monotone in one step. -/
theorem p2_of_le_succ : p2_of k ≤ p2_of (k + 1) := by
  have h : Nat.log 2 (3 ^ k) ≤ Nat.log 2 (3 ^ (k + 1)) :=
    Nat.log_mono_right (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [p2_of]
  omega

theorem order_replicate_false (r : ℕ) : order (List.replicate r false) = 0 := by
  simp [order]

theorem encode_eq_zero (l : List Bool) (h : encode l = 0) : l = List.replicate l.length false := by
  induction l with
  | nil =>
    rfl
  | cons b t ih =>
    cases b with
    | true =>
      simp only [encode, ↓reduceIte] at h
      have : 0 < 2 ^ t.length := by positivity
      omega
    | false =>
      simp only [encode, Bool.false_eq_true, ↓reduceIte, zero_add] at h
      rw [List.length_cons, List.replicate_succ, ← ih h]

/-- 2^r dividing the encoding means the last r bits are 0. -/
theorem eq_append_zeros_of_dvd (p : List Bool) (r : ℕ) (hr : r ≤ p.length)
    (h : 2 ^ r ∣ encode p) : p = p.take (p.length - r) ++ List.replicate r false := by
  have hsplit := List.take_append_drop (p.length - r) p
  have hdl : (p.drop (p.length - r)).length = r := by
    simp
    omega
  have henc : encode p =
      encode (p.take (p.length - r)) * 2 ^ r + encode (p.drop (p.length - r)) := by
    conv_lhs => rw [← hsplit]
    rw [encode_append, hdl]
  have hlt := encode_lt (p.drop (p.length - r))
  rw [hdl] at hlt
  have hz : encode (p.drop (p.length - r)) = 0 := by
    have h2 : 2 ^ r ∣ encode (p.drop (p.length - r)) := by
      have := (Nat.dvd_add_right (dvd_mul_left (2 ^ r) (encode (p.take (p.length - r))))).mp
        (henc ▸ h)
      exact this
    obtain ⟨c, hc⟩ := h2
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [hc, h0, mul_zero]
    · have : 2 ^ r ≤ 2 ^ r * c := Nat.le_mul_of_pos_right _ hpos
      omega
  have hrep := encode_eq_zero _ hz
  rw [hdl] at hrep
  conv_lhs => rw [← hsplit, hrep]

/-- A list containing a 1 splits at its last 1. -/
theorem exists_last_true (c : List Bool) (h : true ∈ c) :
    ∃ a r, c = a ++ true :: List.replicate r false := by
  induction c with
  | nil =>
    simp at h
  | cons b t ih =>
    by_cases ht : true ∈ t
    · obtain ⟨a, r, hr⟩ := ih ht
      rw [hr]
      exact ⟨b :: a, r, rfl⟩
    · have hb : b = true := by
        simp only [List.mem_cons] at h
        rcases h with h | h
        · exact h.symm
        · exact absurd h ht
      have hall : t = List.replicate t.length false := by
        apply List.eq_replicate_iff.mpr
        refine ⟨rfl, ?_⟩
        intro x hx
        cases x with
        | true =>
          exact absurd hx ht
        | false =>
          rfl
      refine ⟨[], t.length, ?_⟩
      rw [hb, ← hall]
      rfl

theorem order_pos_mem (c : List Bool) (h : 1 ≤ order c) : true ∈ c := by
  by_contra hn
  have : c.filter id = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    cases x with
    | true =>
      exact absurd hx hn
    | false =>
      simp
  simp [order, this] at h

/-- Prefixes of a ++ 1 :: 0^r beyond a have Order order a + 1. -/
theorem order_take_last_one (r l : ℕ) (hl : a.length < l) :
    order ((a ++ true :: List.replicate r false).take l) = order a + 1 := by
  rw [List.take_append, List.take_of_length_le (by omega), order_append]
  obtain ⟨e, he⟩ : ∃ e, l - a.length = e + 1 := ⟨l - a.length - 1, by omega⟩
  rw [he, List.take_succ_cons, order_cons, List.take_replicate, order_replicate_false]
  simp

/-- Prefixes of a ++ 0^r beyond a have Order order a. -/
theorem order_take_zeros (r l : ℕ) (hl : a.length ≤ l) :
    order ((a ++ List.replicate r false).take l) = order a := by
  rw [List.take_append, List.take_of_length_le hl, order_append, List.take_replicate,
    order_replicate_false, add_zero]

/-- Child of an admissible parent a ++ 0^(i+1) (Order k, length p2 k):
    a ++ 1 :: 0^(i+m), m = p2(k+1) - p2 k, is admissible. -/
theorem admissible_child (i k : ℕ)
    (hA : Admissible (a ++ List.replicate (i + 1) false))
    (hord : order (a ++ List.replicate (i + 1) false) = k)
    (hlen : (a ++ List.replicate (i + 1) false).length = p2_of k) :
    Admissible (a ++ true :: List.replicate (i + (p2_of (k + 1) - p2_of k)) false) ∧
      order (a ++ true :: List.replicate (i + (p2_of (k + 1) - p2_of k)) false) = k + 1 ∧
      (a ++ true :: List.replicate (i + (p2_of (k + 1) - p2_of k)) false).length =
        p2_of (k + 1) := by
  have hmono := p2_of_le_succ k
  have hoa : order a = k := by
    rw [order_append, order_replicate_false] at hord
    omega
  simp only [List.length_append, List.length_replicate] at hlen
  have hclen : (a ++ true :: List.replicate (i + (p2_of (k + 1) - p2_of k)) false).length =
      p2_of (k + 1) := by
    simp
    omega
  have hcord : order (a ++ true :: List.replicate (i + (p2_of (k + 1) - p2_of k)) false) =
      k + 1 := by
    rw [order_append, order_cons, order_replicate_false, hoa]
    simp
  refine ⟨?_, hcord, hclen⟩
  rw [admissible_iff_pow] at hA ⊢
  obtain ⟨hpre, _⟩ := hA
  refine ⟨?_, ?_⟩
  · intro l hl hl1
    rw [hclen] at hl
    by_cases hla : l ≤ a.length
    · have htake : (a ++ true :: List.replicate (i + (p2_of (k + 1) - p2_of k)) false).take l =
          (a ++ List.replicate (i + 1) false).take l := by
        rw [List.take_append_of_le_length hla, List.take_append_of_le_length hla]
      rw [htake]
      apply hpre l _ hl1
      simp
      omega
    · rw [order_take_last_one a _ l (by omega), hoa]
      calc 2 ^ l ≤ 2 ^ (p2_of (k + 1) - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 3 ^ (k + 1) := two_pow_pred_p2_lt (k + 1) (by omega)
  · rw [hcord, hclen]
    exact p2_of_spec (k + 1)

/-- Parent of an admissible c = a ++ 1 :: 0^r of Order k+1: the last 1 lies in the
    first p2 k positions, and a ++ 0^(p2 k - |a|) is admissible of Order k. -/
theorem admissible_parent (r k : ℕ)
    (hA : Admissible (a ++ true :: List.replicate r false))
    (hord : order (a ++ true :: List.replicate r false) = k + 1) :
    a.length < p2_of k ∧
      Admissible (a ++ List.replicate (p2_of k - a.length) false) ∧
      order (a ++ List.replicate (p2_of k - a.length) false) = k ∧
      (a ++ List.replicate (p2_of k - a.length) false).length = p2_of k := by
  have hoa : order a = k := by
    rw [order_append, order_cons, order_replicate_false] at hord
    simp at hord
    omega
  have h3k := p2_of_spec k
  rw [admissible_iff_pow] at hA
  obtain ⟨hpre, _⟩ := hA
  have hja : a.length < p2_of k := by
    rcases Nat.eq_zero_or_pos a.length with h0 | hpos
    · rw [h0]
      simp [p2_of]
    · have hc := hpre a.length (by simp) hpos
      rw [List.take_append_of_le_length le_rfl, List.take_length, hoa] at hc
      by_contra hge
      have : 2 ^ p2_of k ≤ 2 ^ a.length := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hplen : (a ++ List.replicate (p2_of k - a.length) false).length = p2_of k := by
    simp
    omega
  have hpord : order (a ++ List.replicate (p2_of k - a.length) false) = k := by
    rw [order_append, order_replicate_false, hoa, add_zero]
  refine ⟨hja, ?_, hpord, hplen⟩
  rw [admissible_iff_pow]
  refine ⟨?_, ?_⟩
  · intro l hl hl1
    rw [hplen] at hl
    by_cases hla : l ≤ a.length
    · have htake : (a ++ List.replicate (p2_of k - a.length) false).take l =
          (a ++ true :: List.replicate r false).take l := by
        rw [List.take_append_of_le_length hla, List.take_append_of_le_length hla]
      rw [htake]
      apply hpre l _ hl1
      simp
      omega
    · rw [order_take_zeros a _ l (by omega), hoa]
      have hk : 1 ≤ k := by
        by_contra hk0
        have : p2_of k = 1 := by
          have : k = 0 := by omega
          simp [this, p2_of]
        omega
      calc 2 ^ l ≤ 2 ^ (p2_of k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 3 ^ k := two_pow_pred_p2_lt k hk
  · rw [hpord, hplen]
    exact h3k

theorem encode_child (i m : ℕ) :
    encode (a ++ true :: List.replicate (i + m) false) =
      childAt (encode (a ++ List.replicate (i + 1) false)) m i := by
  simp only [childAt, Nat.shiftLeft_eq, encode_append, encode, List.length_replicate,
    encode_replicate_false, ↓reduceIte, add_zero, List.length_cons]
  rw [pow_add, pow_succ, pow_add]
  ring

/-- Level k of the tree = encodings of the admissible sequences of Order k. -/
theorem mem_treeLevel (k x : ℕ) :
    x ∈ treeLevel k ↔ ∃ s, Admissible s ∧ order s = k ∧ encode s = x := by
  induction k generalizing x with
  | zero =>
    constructor
    · intro hx
      simp only [treeLevel, List.mem_singleton] at hx
      refine ⟨[false], ?_, by simp [order], by simp [hx, encode]⟩
      rw [admissible_iff_pow]
      decide
    · rintro ⟨s, hA, h0, rfl⟩
      rw [admissible_order_zero s hA h0]
      simp [treeLevel, encode]
  | succ k ih =>
    simp only [treeLevel, nextLevel, List.mem_flatMap, childrenOf, List.mem_map,
      List.mem_range]
    constructor
    · rintro ⟨t, ht, i, hi, rfl⟩
      obtain ⟨p, hA, hord, rfl⟩ := (ih t).mp ht
      have hplen := admissible_length p hA
      rw [hord] at hplen
      have hdecomp : p = p.take (p.length - (i + 1)) ++ List.replicate (i + 1) false := by
        by_cases hk : k = 0
        · subst hk
          have hp := admissible_order_zero p hA hord
          subst hp
          simp only [childCount, encode, Bool.false_eq_true, ↓reduceIte, add_zero] at hi
          have hi0 : i = 0 := by
            simp at hi
            omega
          subst hi0
          rfl
        · have hne : encode p ≠ 0 := (encode_pos_of_order p hA (by omega)).ne'
          simp only [childCount, hne, ↓reduceIte] at hi
          have hi' : i + 1 ≤ padicValNat 2 (encode p) := by
            unfold trailingZeros at hi
            omega
          have hdvd : 2 ^ (i + 1) ∣ encode p :=
            (pow_dvd_pow 2 hi').trans pow_padicValNat_dvd
          have hr : i + 1 ≤ p.length := by
            have h1 : 2 ^ (i + 1) ≤ encode p := Nat.le_of_dvd (by omega) hdvd
            have h2 := encode_lt p
            by_contra hgt
            have : 2 ^ p.length ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          exact eq_append_zeros_of_dvd p (i + 1) hr hdvd
      set a := p.take (p.length - (i + 1)) with ha
      rw [hdecomp] at hA hord hplen
      obtain ⟨hcA, hcord, _⟩ := admissible_child a i k hA hord hplen
      refine ⟨_, hcA, hcord, ?_⟩
      rw [encode_child, ← hdecomp]
    · rintro ⟨c, hA, hord, rfl⟩
      obtain ⟨a, r, rfl⟩ := exists_last_true c (order_pos_mem c (by omega))
      obtain ⟨hja, hpA, hpord, hplen⟩ := admissible_parent a r k hA hord
      have hclen := admissible_length _ hA
      rw [hord] at hclen
      simp only [List.length_append, List.length_cons, List.length_replicate] at hclen
      have hmono := p2_of_le_succ k
      refine ⟨encode (a ++ List.replicate (p2_of k - a.length) false),
        (ih _).mpr ⟨_, hpA, hpord, rfl⟩, p2_of k - a.length - 1, ?_, ?_⟩
      · by_cases hk : k = 0
        · subst hk
          have hp : p2_of 0 = 1 := by
            simp [p2_of]
          simp [childCount, hp] at hja ⊢
          simp [hja, encode]
        · have hne : encode (a ++ List.replicate (p2_of k - a.length) false) ≠ 0 :=
            (encode_pos_of_order _ hpA (by omega)).ne'
          simp only [childCount, hne, ↓reduceIte]
          have hdvd : 2 ^ (p2_of k - a.length) ∣
              encode (a ++ List.replicate (p2_of k - a.length) false) := by
            rw [encode_append, encode_replicate_false, List.length_replicate, add_zero]
            exact dvd_mul_left _ _
          have hle := (padicValNat_dvd_iff_le hne).mp hdvd
          unfold trailingZeros
          omega
      · have hrep : p2_of k - a.length = p2_of k - a.length - 1 + 1 := by
          omega
        have hr : r = p2_of k - a.length - 1 + (p2_of (k + 1) - p2_of k) := by
          omega
        rw [hr, encode_child, ← hrep]

/-- The tree levels are strictly increasing. -/
theorem treeLevel_isChain_lt : (treeLevel k).IsChain (· < ·) := by
  have hgap : GapOk (treeLevel k) := by
    induction k with
    | zero =>
      exact gapOk_base
    | succ k ih =>
      exact gapOk_preserved _ _ ih
  exact hgap.imp_of_mem_imp (fun a b _ _ hR => by
    have : (1 : ℕ) ≤ 2 ^ (childCount a) := Nat.one_le_two_pow
    omega)

/-- For equal lengths, encode s < encode t iff s and t first differ with 0 in s. -/
theorem encode_lt_iff_lex (s t : List Bool) (hlen : s.length = t.length) :
    encode s < encode t ↔ ∃ u v w, s = u ++ false :: v ∧ t = u ++ true :: w := by
  constructor
  · intro h
    induction s generalizing t with
    | nil =>
      cases t with
      | nil =>
        simp at h
      | cons c t =>
        simp at hlen
    | cons b s ih =>
      cases t with
      | nil =>
        simp at hlen
      | cons c t =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        have hs := encode_lt s
        have ht := encode_lt t
        simp only [encode] at h
        rw [hlen] at hs h
        cases b with
        | true =>
          cases c with
          | true =>
            simp only [↓reduceIte, Nat.add_lt_add_iff_left] at h
            obtain ⟨u, v, w, rfl, rfl⟩ := ih t hlen h
            exact ⟨true :: u, v, w, rfl, rfl⟩
          | false =>
            simp only [↓reduceIte, Bool.false_eq_true] at h
            omega
        | false =>
          cases c with
          | true =>
            exact ⟨[], s, t, rfl, rfl⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h
            obtain ⟨u, v, w, rfl, rfl⟩ := ih t hlen h
            exact ⟨false :: u, v, w, rfl, rfl⟩
  · rintro ⟨u, v, w, rfl, rfl⟩
    simp only [List.length_append, List.length_cons, Nat.add_left_cancel_iff,
      Nat.add_right_cancel_iff] at hlen
    rw [encode_append, encode_append]
    simp only [List.length_cons, encode, Bool.false_eq_true, ↓reduceIte, zero_add]
    have hv := encode_lt v
    rw [hlen] at hv ⊢
    omega

/-- sec:sorting: within Order k, the tree lists the admissible sequences in strictly
    increasing lexicographic order of their parity vectors. -/
theorem lex_enumeration :
    (∀ x, x ∈ treeLevel k ↔ ∃ s, Admissible s ∧ order s = k ∧ encode s = x) ∧
      (treeLevel k).IsChain (· < ·) ∧
      ∀ s t, Admissible s → Admissible t → order s = k → order t = k →
        (encode s < encode t ↔ ∃ u v w, s = u ++ false :: v ∧ t = u ++ true :: w) := by
  refine ⟨mem_treeLevel k, treeLevel_isChain_lt k, ?_⟩
  intro s t hs ht hks hkt
  apply encode_lt_iff_lex
  rw [admissible_length s hs, admissible_length t ht, hks, hkt]

end AcceleratedCollatz
