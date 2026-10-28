-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBinomial

/-!
  Subwords of admissible words, counted by first passage. `occ s w` counts the occurrences
  of s as a block in w; across a cut, `occ s (a ++ r) = occ s a + occ s r + cross s a r`
  (`occ_append`). Over all words of length M and Order k, s ≠ [] occurs
  (M + 1 - |s|) C(M - |s|, k - order s) times (`sum_occ_wordSet`), and C(M - |y|, k - order y)
  words start (or end) with y (`card_filter_prefix`, `card_filter_suffix`).

  Cutting the start words of Order n at their first passage below 1 (as in
  `choose_eq_sum_admSet`) gives two identities. For the occurrences of s, with
  M = p2(n) - p2(i), k = n - i, occ(i) the occurrences in the admissible words of Order i and
  suf(x, i) those of them that end with x:
  [s starts with 1] C(p2(n) - |s|, n - order s) + (p2(n) - |s|) C(p2(n) - 1 - |s|, n - 1 - order s)
    = Σ_{i=1..n} (occ(i) C(M, k) + a(i) (M + 1 - |s|) C(M - |s|, k - order s)
        + Σ_{0<j<|s|} suf(s.take j, i) C(M - |s.drop j|, k - order (s.drop j)))
  (`occ_first_passage`), and for the suffixes x, |x| < p2(n),
  C(p2(n) - 1 - |x|, n - 1 - order x) = Σ_{i=1..n} [a(i) C(M - |x|, k - order x) if |x| ≤ M,
    else suf(x.take (|x| - M), i) [order (x.drop (|x| - M)) = k]]
  (`suffix_first_passage`). The part of Order n is occ(n), resp. suf(x, n): both follow from
  lower Orders (`occAdm_rec`, `sufAdm_rec`). (Every C(M', k') here is 0 unless the subword
  fits, see `pc`.)
-/

namespace AcceleratedCollatz

/-- s is a prefix of t ++ r: of t, or it covers t and goes on into r. -/
theorem prefix_append_iff_cut (s t r : List Bool) :
    s <+: t ++ r ↔
      s <+: t ∨ (t.length < s.length ∧ s.take t.length = t ∧ s.drop t.length <+: r) := by
  constructor
  · intro h
    rcases le_or_gt s.length t.length with hle | hlt
    · left
      rw [List.prefix_iff_eq_take] at h ⊢
      rw [h, List.take_append_of_le_length hle]
      simp [List.length_take, hle]
    · right
      refine ⟨hlt, ?_, ?_⟩
      · rw [List.prefix_iff_eq_take.mp h, List.take_take, min_eq_left hlt.le,
          List.take_append_of_le_length le_rfl, List.take_length]
      · obtain ⟨u, hu⟩ := h
        refine ⟨u, ?_⟩
        have := congrArg (List.drop t.length) hu
        rwa [List.drop_append_of_le_length hlt.le, List.drop_left] at this
  · rintro (h | ⟨_, h1, h2⟩)
    · exact h.trans (List.prefix_append t r)
    · rw [← List.take_append_drop t.length s, h1]
      exact (List.prefix_append_right_inj t).mpr h2


/-- The number of occurrences of `s` in `w` as a block of consecutive letters. -/
def occ (s : List Bool) : List Bool → ℕ
  | [] => 0
  | b :: t => (if s <+: b :: t then 1 else 0) + occ s t

/-- Occurrences of `s` across the cut of `a ++ r`: `s = x ++ y` with `x`, `y` nonempty,
    `x` a suffix of `a` and `y` a prefix of `r`. -/
def cross (s a r : List Bool) : ℕ :=
  ∑ j ∈ Finset.Ioo 0 s.length, if s.take j <:+ a ∧ s.drop j <+: r then 1 else 0

/-- Nothing crosses a cut after the empty word. -/
theorem cross_nil (s r : List Bool) : cross s [] r = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ioo] at hj
  rw [ite_eq_right_iff]
  rintro ⟨h, -⟩
  have := congrArg List.length (List.suffix_nil.mp h)
  rw [List.length_take, List.length_nil] at this
  omega

/-- One more letter b before the cut adds the occurrence that starts at b, if it crosses. -/
theorem cross_cons (s a r : List Bool) (b : Bool) :
    cross s (b :: a) r = cross s a r +
      if (b :: a).length < s.length ∧ s.take (b :: a).length = b :: a ∧
        s.drop (b :: a).length <+: r then 1 else 0 := by
  have hterm : ∀ j ∈ Finset.Ioo 0 s.length,
      (if s.take j <:+ b :: a ∧ s.drop j <+: r then 1 else 0) =
        (if s.take j <:+ a ∧ s.drop j <+: r then 1 else 0) +
          if j = (b :: a).length then
            (if s.take j = b :: a ∧ s.drop j <+: r then 1 else 0) else 0 := by
    intro j hj
    rw [Finset.mem_Ioo] at hj
    simp only [List.length_cons] at hj ⊢
    by_cases hj' : j = a.length + 1
    · subst hj'
      have hn : ¬ s.take (a.length + 1) <:+ a := by
        intro h
        have := h.length_le
        rw [List.length_take] at this
        omega
      simp [List.suffix_cons_iff, hn]
    · have hn : s.take j ≠ b :: a := by
        intro h
        have := congrArg List.length h
        rw [List.length_take, List.length_cons] at this
        omega
      simp [List.suffix_cons_iff, hn, hj']
  rw [cross, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← cross,
    Finset.sum_ite_eq' (Finset.Ioo 0 s.length)]
  congr 1
  simp only [Finset.mem_Ioo, List.length_cons]
  split_ifs <;> simp_all

/-- The occurrences of s ≠ [] in a ++ r: in a, in r, and across the cut. -/
theorem occ_append (s : List Bool) (hs : s ≠ []) :
    ∀ a r : List Bool, occ s (a ++ r) = occ s a + occ s r + cross s a r
  | [], r => by simp [occ, cross_nil]
  | b :: a, r => by
    rw [List.cons_append, occ, occ_append s hs a r, occ, cross_cons]
    have key : (if s <+: b :: a ++ r then 1 else 0) =
        (if s <+: b :: a then 1 else 0) +
          if (b :: a).length < s.length ∧ s.take (b :: a).length = b :: a ∧
            s.drop (b :: a).length <+: r then 1 else 0 := by
      by_cases h1 : s <+: b :: a
      · have hl := h1.length_le
        have h2 : ¬ ((b :: a).length < s.length ∧ s.take (b :: a).length = b :: a ∧
            s.drop (b :: a).length <+: r) := fun h => by omega
        have h3 : s <+: b :: a ++ r := h1.trans (List.prefix_append _ r)
        simp only [h1, h2, h3, ↓reduceIte]
      · have := prefix_append_iff_cut s (b :: a) r
        simp only [h1, false_or] at this
        simp only [this, h1, ite_false, zero_add]
    rw [List.cons_append] at key
    rw [key]
    ring


/-- C(M - |y|, k - order y) when y fits in length M and Order k, else 0: the number of words
    of length M and Order k that start (or end) with y. -/
def pc (y : List Bool) (M k : ℕ) : ℕ :=
  if y.length ≤ M ∧ order y ≤ k then (M - y.length).choose (k - order y) else 0

/-- The words of length M and Order k that start with y. -/
theorem card_filter_prefix (y : List Bool) (M k : ℕ) :
    ((wordSet M k).filter (fun r => y <+: r)).card = pc y M k := by
  unfold pc
  split_ifs with h
  · have himg : (wordSet M k).filter (fun r => y <+: r) =
        (wordSet (M - y.length) (k - order y)).image (y ++ ·) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_image, mem_wordSet]
      constructor
      · rintro ⟨⟨hl, ho⟩, t, rfl⟩
        rw [List.length_append] at hl
        rw [order_append] at ho
        exact ⟨t, ⟨by omega, by omega⟩, rfl⟩
      · rintro ⟨t, ⟨hl, ho⟩, rfl⟩
        rw [List.length_append, order_append]
        exact ⟨⟨by omega, by omega⟩, List.prefix_append y t⟩
    rw [himg, Finset.card_image_of_injective _ (List.append_right_injective y), card_wordSet]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r hr ⟨t, ht⟩
    rw [mem_wordSet] at hr
    rw [← ht, List.length_append, order_append] at hr
    omega

/-- The words of length M and Order k that end with x. -/
theorem card_filter_suffix (x : List Bool) (M k : ℕ) :
    ((wordSet M k).filter (fun r => x <:+ r)).card = pc x M k := by
  unfold pc
  split_ifs with h
  · have himg : (wordSet M k).filter (fun r => x <:+ r) =
        (wordSet (M - x.length) (k - order x)).image (· ++ x) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_image, mem_wordSet]
      constructor
      · rintro ⟨⟨hl, ho⟩, t, rfl⟩
        rw [List.length_append] at hl
        rw [order_append] at ho
        exact ⟨t, ⟨by omega, by omega⟩, rfl⟩
      · rintro ⟨t, ⟨hl, ho⟩, rfl⟩
        rw [List.length_append, order_append]
        exact ⟨⟨by omega, by omega⟩, List.suffix_append t x⟩
    rw [himg, Finset.card_image_of_injective _ (List.append_left_injective x), card_wordSet]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r hr ⟨t, ht⟩
    rw [mem_wordSet] at hr
    rw [← ht, List.length_append, order_append] at hr
    omega

/-- A sum over the words of length M + 1, split by the first letter. -/
theorem sum_wordSet_succ (f : List Bool → ℕ) (M k : ℕ) :
    ∑ r ∈ wordSet (M + 1) k, f r =
      ∑ t ∈ wordSet M k, f (false :: t) +
        if k = 0 then 0 else ∑ t ∈ wordSet M (k - 1), f (true :: t) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun s => s.head? = some true),
    wordSet_head_false, Finset.sum_image (fun _ _ _ _ h => List.cons_injective h), add_comm]
  congr 1
  cases k with
  | zero => simp [wordSet_head_true_zero]
  | succ k =>
    rw [wordSet_head_true, Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
    simp

/-- Pascal's rule for `pc`, for a word y that fits in length M. -/
theorem pc_succ (y : List Bool) (M k : ℕ) (hy : y.length ≤ M) :
    pc y (M + 1) k = pc y M k + if k = 0 then 0 else pc y M (k - 1) := by
  unfold pc
  rcases k with _ | k
  · simp only [↓reduceIte, add_zero]
    by_cases ho : order y ≤ 0
    · simp [ho, show y.length ≤ M + 1 by omega, hy]
    · simp [ho]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases h1 : order y ≤ k
    · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨hy, by omega⟩, ite_eq_left ⟨hy, h1⟩,
        show M + 1 - y.length = (M - y.length) + 1 by omega,
        show k + 1 - order y = (k - order y) + 1 by omega, Nat.choose_succ_succ']
      ring
    · by_cases h2 : order y = k + 1
      · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨hy, by omega⟩, ite_eq_right (by omega)]
        simp [h2]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The occurrences of s in all words of length M and Order k:
    (M + 1 - |s|) C(M - |s|, k - order s). -/
theorem sum_occ_wordSet (s : List Bool) (hs : s ≠ []) :
    ∀ M k : ℕ, ∑ r ∈ wordSet M k, occ s r = (M + 1 - s.length) * pc s M k
  | 0, k => by
    have : s.length ≠ 0 := by simpa using hs
    rw [show 0 + 1 - s.length = 0 by omega, zero_mul]
    apply Finset.sum_eq_zero
    intro r hr
    rw [mem_wordSet, List.length_eq_zero_iff] at hr
    rw [hr.1, occ]
  | M + 1, k => by
    have hpre : ∀ k', ∑ t ∈ wordSet M k', occ s (false :: t) =
        ((wordSet M k').filter (fun t => s <+: false :: t)).card +
          (M + 1 - s.length) * pc s M k' := by
      intro k'
      simp only [occ, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id,
        sum_occ_wordSet s hs M k']
    have hpre' : ∀ k', ∑ t ∈ wordSet M k', occ s (true :: t) =
        ((wordSet M k').filter (fun t => s <+: true :: t)).card +
          (M + 1 - s.length) * pc s M k' := by
      intro k'
      simp only [occ, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id,
        sum_occ_wordSet s hs M k']
    have hcard := card_filter_prefix s (M + 1) k
    rw [Finset.card_filter, sum_wordSet_succ] at hcard
    rw [sum_wordSet_succ, hpre]
    have hsl : 1 ≤ s.length := by
      rcases s with _ | ⟨b, s⟩
      · exact absurd rfl hs
      · simp
    by_cases hk : k = 0
    · subst hk
      simp only [↓reduceIte, add_zero] at hcard ⊢
      have hc : ((wordSet M 0).filter (fun t => s <+: false :: t)).card = pc s (M + 1) 0 := by
        rw [Finset.card_filter]
        exact hcard
      rw [hc]
      by_cases hl : s.length ≤ M
      · rw [pc_succ s M 0 hl]
        simp only [↓reduceIte, add_zero]
        rw [show M + 1 + 1 - s.length = (M + 1 - s.length) + 1 by omega]
        ring
      · have h0 : pc s M 0 = 0 := by unfold pc; rw [ite_eq_right (by omega)]
        rw [h0, mul_zero, add_zero]
        by_cases he : s.length = M + 1
        · rw [show M + 1 + 1 - s.length = 1 by omega, one_mul]
        · have h0' : pc s (M + 1) 0 = 0 := by unfold pc; rw [ite_eq_right (by omega)]
          rw [h0', mul_zero]
    · simp only [hk, ↓reduceIte] at hcard ⊢
      rw [hpre']
      have hc : ((wordSet M k).filter (fun t => s <+: false :: t)).card +
          ((wordSet M (k - 1)).filter (fun t => s <+: true :: t)).card = pc s (M + 1) k := by
        rw [Finset.card_filter, Finset.card_filter]
        exact hcard
      by_cases hl : s.length ≤ M
      · rw [pc_succ s M k hl, ite_eq_right hk] at hc ⊢
        rw [show M + 1 + 1 - s.length = (M + 1 - s.length) + 1 by omega]
        nlinarith [hc]
      · have h0 : ∀ k', pc s M k' = 0 := fun k' => by unfold pc; rw [ite_eq_right (by omega)]
        rw [h0, h0, mul_zero, add_zero, add_zero]
        by_cases he : s.length = M + 1
        · rw [show M + 1 + 1 - s.length = 1 by omega, one_mul, ← hc]
        · have h0' : pc s (M + 1) k = 0 := by unfold pc; rw [ite_eq_right (by omega)]
          rw [h0'] at hc
          rw [h0', mul_zero]
          omega


/-- x is a suffix of a ++ r: of r, or it covers r and goes back into a. -/
theorem suffix_append_iff_cut (x a r : List Bool) :
    x <:+ a ++ r ↔ x <:+ r ∨ (r.length < x.length ∧ x.drop (x.length - r.length) = r ∧
      x.take (x.length - r.length) <:+ a) := by
  rw [← List.reverse_prefix, List.reverse_append, prefix_append_iff_cut, List.reverse_prefix,
    List.length_reverse, List.length_reverse, List.take_reverse, List.drop_reverse,
    List.reverse_inj, List.reverse_prefix]

/-- Occurrences of s in the admissible words of Order i. -/
def occAdm (s : List Bool) (i : ℕ) : ℕ := ∑ a ∈ admSet i, occ s a

/-- The number of admissible words of Order i that end with x. -/
def sufAdm (x : List Bool) (i : ℕ) : ℕ := ((admSet i).filter (fun a => x <:+ a)).card

/-- The part of Order i in the first-passage identity for occurrences of s:
    with M = p2(n) - p2(i) and k = n - i,
    occ(i) C(M, k) + a(i) (M + 1 - |s|) C(M - |s|, k - order s)
      + Σ_{0<j<|s|} suf(s.take j, i) C(M - |s.drop j|, k - order (s.drop j)). -/
def occTerm (s : List Bool) (n i : ℕ) : ℕ :=
  occAdm s i * (p2_of n - p2_of i).choose (n - i) +
    (admSet i).card * ((p2_of n - p2_of i + 1 - s.length) * pc s (p2_of n - p2_of i) (n - i)) +
    ∑ j ∈ Finset.Ioo 0 s.length, sufAdm (s.take j) i * pc (s.drop j) (p2_of n - p2_of i) (n - i)

/-- The part of Order i in the first-passage identity for the suffix x. -/
def sufTerm (x : List Bool) (n i : ℕ) : ℕ :=
  if x.length ≤ p2_of n - p2_of i then (admSet i).card * pc x (p2_of n - p2_of i) (n - i)
  else sufAdm (x.take (x.length - (p2_of n - p2_of i))) i *
    if order (x.drop (x.length - (p2_of n - p2_of i))) = n - i then 1 else 0

/-- A sum over the start words, as a sum over their first-passage splits. -/
theorem sum_startWords (n : ℕ) (hn : 1 ≤ n) (f : List Bool → ℕ) :
    ∑ w ∈ startWords n, f w =
      ∑ i ∈ Finset.Icc 1 n, ∑ a ∈ admSet i, ∑ r ∈ wordSet (p2_of n - p2_of i) (n - i),
        f (a ++ r) := by
  rw [← image_firstPassageSplits n hn, Finset.sum_image (injOn_firstPassageSplits n),
    firstPassageSplits, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_product]

/-- The occurrences of s in the start words of Order n. -/
theorem sum_occ_startWords (s : List Bool) (hs : s ≠ []) (n : ℕ) :
    ∑ w ∈ startWords n, occ s w =
      (if s.head? = some true then pc s.tail (p2_of n - 1) (n - 1) else 0) +
        (p2_of n - s.length) * pc s (p2_of n - 1) (n - 1) := by
  have hp : 1 ≤ p2_of n := by simp [p2_of]
  rw [startWords, Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
  simp only [occ, Finset.sum_add_distrib, sum_occ_wordSet s hs]
  rw [show p2_of n - 1 + 1 - s.length = p2_of n - s.length by omega]
  congr 1
  obtain ⟨b, s', rfl⟩ := List.exists_cons_of_ne_nil hs
  rw [← Finset.card_filter]
  simp only [List.cons_prefix_cons, List.head?_cons, Option.some.injEq, List.tail_cons]
  cases b
  · simp
  · simp [card_filter_prefix]

/-- First-passage identity for the occurrences of a subword s ≠ []: the occurrences of s
    in the start words of Order n, cut at their first passage below 1. -/
theorem occ_first_passage (s : List Bool) (hs : s ≠ []) (n : ℕ) (hn : 1 ≤ n) :
    (if s.head? = some true then pc s.tail (p2_of n - 1) (n - 1) else 0) +
        (p2_of n - s.length) * pc s (p2_of n - 1) (n - 1) =
      ∑ i ∈ Finset.Icc 1 n, occTerm s n i := by
  rw [← sum_occ_startWords s hs n, sum_startWords n hn]
  apply Finset.sum_congr rfl
  intro i _
  rw [occTerm, occAdm]
  set M := p2_of n - p2_of i
  set k := n - i
  simp only [occ_append s hs, Finset.sum_add_distrib, Finset.sum_const, card_wordSet,
    smul_eq_mul, sum_occ_wordSet s hs]
  have e1 : ∑ a ∈ admSet i, M.choose k * occ s a = (∑ a ∈ admSet i, occ s a) * M.choose k := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have e3 : ∑ a ∈ admSet i, ∑ r ∈ wordSet M k, cross s a r =
      ∑ j ∈ Finset.Ioo 0 s.length, sufAdm (s.take j) i * pc (s.drop j) M k := by
    simp only [cross]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := wordSet M k)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [sufAdm, ← card_filter_prefix, Finset.card_filter, Finset.card_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h1 : s.take j <:+ a <;> by_cases h2 : s.drop j <+: r <;> simp [h1, h2]
  rw [e1, e3]

/-- The suffixes x of the start words of Order n, for |x| < p2(n). -/
theorem card_suffix_startWords (x : List Bool) (n : ℕ) (hx : x.length < p2_of n) :
    ((startWords n).filter (fun w => x <:+ w)).card = pc x (p2_of n - 1) (n - 1) := by
  rw [← card_filter_suffix, startWords, Finset.filter_image,
    Finset.card_image_of_injective _ List.cons_injective]
  congr 1
  apply Finset.filter_congr
  intro u hu
  rw [mem_wordSet] at hu
  rw [List.suffix_cons_iff]
  constructor
  · rintro (h | h)
    · have := congrArg List.length h
      simp at this
      omega
    · exact h
  · exact Or.inr

/-- First-passage identity for the suffix x: the start words of Order n that end with x,
    cut at their first passage below 1. -/
theorem suffix_first_passage (x : List Bool) (n : ℕ) (hn : 1 ≤ n) (hx : x.length < p2_of n) :
    pc x (p2_of n - 1) (n - 1) = ∑ i ∈ Finset.Icc 1 n, sufTerm x n i := by
  rw [← card_suffix_startWords x n hx, Finset.card_filter, sum_startWords n hn]
  apply Finset.sum_congr rfl
  intro i _
  rw [sufTerm]
  set M := p2_of n - p2_of i
  set k := n - i
  have hlen : ∀ r ∈ wordSet M k, r.length = M := fun r hr => ((mem_wordSet _ _ _).mp hr).1
  by_cases hxM : x.length ≤ M
  · rw [ite_eq_left hxM]
    have hrow : ∀ a ∈ admSet i,
        (∑ r ∈ wordSet M k, if x <:+ a ++ r then 1 else 0) = pc x M k := by
      intro a _
      rw [← card_filter_suffix, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro r hr
      have hiff : x <:+ a ++ r ↔ x <:+ r := by
        rw [suffix_append_iff_cut, hlen r hr]
        simp [show ¬ M < x.length by omega]
      simp only [hiff]
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, smul_eq_mul]
  · rw [ite_eq_right hxM, sufAdm, Finset.card_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    have hcnt : ∀ r ∈ wordSet M k, (if x <:+ a ++ r then 1 else 0) =
        (if x.take (x.length - M) <:+ a then 1 else 0) *
          if r = x.drop (x.length - M) then 1 else 0 := by
      intro r hr
      have hiff : x <:+ a ++ r ↔ x.take (x.length - M) <:+ a ∧ r = x.drop (x.length - M) := by
        rw [suffix_append_iff_cut, hlen r hr]
        have hnr : ¬ x <:+ r := fun h => by
          have := h.length_le
          rw [hlen r hr] at this
          omega
        simp only [hnr, false_or, show M < x.length by omega, true_and]
        constructor
        · exact fun ⟨h1, h2⟩ => ⟨h2, h1.symm⟩
        · exact fun ⟨h1, h2⟩ => ⟨h2.symm, h1⟩
      simp only [hiff]
      by_cases h1 : x.take (x.length - M) <:+ a <;> by_cases h2 : r = x.drop (x.length - M) <;>
        simp [h1, h2]
    rw [Finset.sum_congr rfl hcnt, ← Finset.mul_sum, Finset.sum_ite_eq']
    congr 1
    have hmem : x.drop (x.length - M) ∈ wordSet M k ↔ order (x.drop (x.length - M)) = k := by
      rw [mem_wordSet, List.length_drop]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    simp only [hmem]


/-- The part of Order n in `occ_first_passage` is occ(n). -/
theorem occTerm_self (s : List Bool) (hs : s ≠ []) (n : ℕ) : occTerm s n n = occAdm s n := by
  have hsl : 1 ≤ s.length := List.length_pos_of_ne_nil hs
  have hpc : ∀ j ∈ Finset.Ioo 0 s.length, pc (s.drop j) 0 0 = 0 := by
    intro j hj
    rw [Finset.mem_Ioo] at hj
    unfold pc
    rw [ite_eq_right]
    rw [List.length_drop]
    omega
  rw [occTerm, Nat.sub_self, Nat.sub_self, Finset.sum_congr rfl
    (fun j hj => by rw [hpc j hj, mul_zero])]
  simp [show 0 + 1 - s.length = 0 by omega]

/-- The part of Order n in `suffix_first_passage` is suf(x, n). -/
theorem sufTerm_self (x : List Bool) (hx : x ≠ []) (n : ℕ) : sufTerm x n n = sufAdm x n := by
  have hxl : 1 ≤ x.length := List.length_pos_of_ne_nil hx
  rw [sufTerm, Nat.sub_self, Nat.sub_self, ite_eq_right (by omega)]
  simp [order]

/-- The occurrences of s ≠ [] in the admissible words of Order n, from those of lower
    Orders: the first-passage identity solved for its part of Order n. -/
theorem occAdm_rec (s : List Bool) (hs : s ≠ []) (n : ℕ) (hn : 1 ≤ n) :
    occAdm s n =
      (if s.head? = some true then pc s.tail (p2_of n - 1) (n - 1) else 0) +
        (p2_of n - s.length) * pc s (p2_of n - 1) (n - 1) -
      ∑ i ∈ Finset.Ico 1 n, occTerm s n i := by
  have h := occ_first_passage s hs n hn
  rw [← Finset.Ico_insert_right hn, Finset.sum_insert Finset.right_notMem_Ico,
    occTerm_self s hs] at h
  omega

/-- The admissible words of Order n that end with x ≠ [], |x| < p2(n), from lower Orders. -/
theorem sufAdm_rec (x : List Bool) (hx : x ≠ []) (n : ℕ) (hn : 1 ≤ n)
    (hxl : x.length < p2_of n) :
    sufAdm x n = pc x (p2_of n - 1) (n - 1) - ∑ i ∈ Finset.Ico 1 n, sufTerm x n i := by
  have h := suffix_first_passage x n hn hxl
  rw [← Finset.Ico_insert_right hn, Finset.sum_insert Finset.right_notMem_Ico,
    sufTerm_self x hx] at h
  omega

/-! ## Check: Order 5 (words of length 8) -/

set_option linter.hashCommand false in
#guard occAdm [true, false] 5 = 15 ∧ sufAdm [true, false, false] 5 = 3

end AcceleratedCollatz
