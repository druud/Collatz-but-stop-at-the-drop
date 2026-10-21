-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TAdmSet
import AcceleratedCollatz.TUds

/-!
  The letter words of the product rule, counted (paper sec:three). A 1 followed by z
  zeros splits in exactly one way into letters (`udsDecode_udsBits`, `udsBits_udsDecode`).
  The bits of a letter word of the product rule are an admissible word, or one followed
  by 0 (`admissible_or_of_udsStopWord`), and each admissible word of Order m ≥ 1 gives
  both (`udsStopWord_udsDecode`, `udsStopWord_udsDecode_append`): for m ≥ 1 there are
  2 A100982(m) such words with M = m (`card_udsStopSet`), A100982(m) of them with p2(m)
  bits and as many with p2(m) + 1 (`card_udsStopSet_filter_p2`,
  `card_udsStopSet_filter_p2_succ`); with `udsWord_class` they fix k modulo 2^(p2(m) + 1)
  and 2^(p2(m) + 2).
-/

namespace AcceleratedCollatz

/-- Reversed bits back to letters, read from the right: 1 is U, 10 is D, 00 is S. -/
def udsDecodeRev : List Bool → List UDS
  | [] => []
  | true :: r => .U :: udsDecodeRev r
  | false :: true :: r => .D :: udsDecodeRev r
  | false :: false :: r => .S :: udsDecodeRev r
  | [false] => []

/-- Bits back to letters. -/
def udsDecode (b : List Bool) : List UDS := (udsDecodeRev b.reverse).reverse

/-- The letter words of the product rule with M = m. -/
def udsStopSet (m : ℕ) : Finset (List UDS) :=
  (admSet m).image udsDecode ∪ (admSet m).image (fun s => udsDecode (s ++ [false]))

theorem udsDecodeRev_reverse (w : List UDS) :
    udsDecodeRev (udsBits w.reverse).reverse = w := by
  induction w with
  | nil =>
    rfl
  | cons c w ih =>
    rw [List.reverse_cons, udsBits_append, List.reverse_append]
    cases c with
    | U =>
      simp only [udsBits, UDS.bits, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.reverse_singleton, List.singleton_append, udsDecodeRev]
      rw [← udsBits, ih]
    | D =>
      simp only [udsBits, UDS.bits, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        udsDecodeRev]
      rw [← udsBits, ih]
    | S =>
      simp only [udsBits, UDS.bits, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        udsDecodeRev]
      rw [← udsBits, ih]

/-- The bits of a letter word decode to it. -/
theorem udsDecode_udsBits (w : List UDS) : udsDecode (udsBits w) = w := by
  have h := udsDecodeRev_reverse w.reverse
  rw [List.reverse_reverse] at h
  rw [udsDecode, h, List.reverse_reverse]

theorem udsBits_injective : Function.Injective udsBits := by
  intro v w h
  rw [← udsDecode_udsBits v, h, udsDecode_udsBits]

theorem udsBits_udsDecodeRev (r : List Bool) (hr : r.getLast? ≠ some false) :
    udsBits (udsDecodeRev r).reverse = r.reverse := by
  induction r using udsDecodeRev.induct with
  | case1 =>
    rfl
  | case2 r ih =>
    have hr' : r.getLast? ≠ some false := by
      intro h
      rw [List.getLast?_cons, h] at hr
      exact hr rfl
    rw [udsDecodeRev, List.reverse_cons, udsBits_append, ih hr', List.reverse_cons]
    rfl
  | case3 r ih =>
    have hr' : r.getLast? ≠ some false := by
      intro h
      rw [List.getLast?_cons, List.getLast?_cons, h] at hr
      exact hr rfl
    rw [udsDecodeRev, List.reverse_cons, udsBits_append, ih hr']
    simp [udsBits, UDS.bits]
  | case4 r ih =>
    have hr' : r.getLast? ≠ some false := by
      intro h
      rw [List.getLast?_cons, List.getLast?_cons, h] at hr
      exact hr rfl
    rw [udsDecodeRev, List.reverse_cons, udsBits_append, ih hr']
    simp [udsBits, UDS.bits]
  | case5 =>
    exact absurd rfl hr

/-- A bit word that starts with 1 splits in exactly one way into letters. -/
theorem udsBits_udsDecode (b : List Bool) (hb : b.head? = some true) :
    udsBits (udsDecode b) = b := by
  have hr : b.reverse.getLast? ≠ some false := by
    rw [List.getLast?_reverse, hb]
    simp
  rw [udsDecode, udsBits_udsDecodeRev _ hr, List.reverse_reverse]

/-- No letter word has the bits 0. -/
theorem udsBits_ne_singleton_false (v : List UDS) : udsBits v ≠ [false] := by
  cases v with
  | nil =>
    simp
  | cons c v =>
    cases c with
    | U =>
      simp [UDS.bits]
    | D =>
      simp [UDS.bits]
    | S =>
      simp [UDS.bits]

/-- An admissible word of Order at least 1 starts with 1. -/
theorem Admissible.head_true {s : List Bool} (hA : Admissible s) (hm : 1 ≤ order s) :
    s.head? = some true := by
  cases s with
  | nil =>
    simp [order] at hm
  | cons b t =>
    cases b with
    | true =>
      rfl
    | false =>
      cases t with
      | nil =>
        simp [order] at hm
      | cons b' t' =>
        have h := hA.prefix_gt 1 le_rfl (by simp)
        norm_num [seqProduct, factor] at h

theorem seqProduct_singleton_true : seqProduct [true] = 3 / 2 := by
  norm_num [seqProduct, factor]

theorem one_le_seqProduct_udsBits (v : List UDS)
    (hv : ∀ i, 1 ≤ i → i ≤ v.length → 1 < seqProduct (udsBits (v.take i))) :
    1 ≤ seqProduct (udsBits v) := by
  rcases Nat.eq_zero_or_pos v.length with h0 | hpos
  · rw [List.length_eq_zero_iff.mp h0, udsBits_nil, seqProduct_nil]
  · have h := hv v.length hpos le_rfl
    rw [List.take_length] at h
    exact h.le

/-- Above 1 at every letter boundary: above 1 at every nonempty bit prefix. -/
theorem one_lt_seqProduct_take_udsBits (v : List UDS)
    (hv : ∀ i, 1 ≤ i → i ≤ v.length → 1 < seqProduct (udsBits (v.take i)))
    (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ (udsBits v).length) :
    1 < seqProduct ((udsBits v).take m) := by
  induction v using List.reverseRecOn generalizing m with
  | nil =>
    simp at hm
    omega
  | append_singleton v c ih =>
    have hv' : ∀ i, 1 ≤ i → i ≤ v.length → 1 < seqProduct (udsBits (v.take i)) := by
      intro i hi1 hi
      have hi' : i ≤ (v ++ [c]).length := by
        rw [List.length_append, List.length_singleton]
        omega
      have h := hv i hi1 hi'
      rwa [List.take_append_of_le_length hi] at h
    have hfull : 1 < seqProduct (udsBits v ++ c.bits) := by
      have h := hv (v.length + 1) (by omega) (by simp)
      rwa [List.take_of_length_le (by simp), udsBits_append, udsBits_cons, udsBits_nil,
        List.append_nil] at h
    have h0 := one_le_seqProduct_udsBits v hv'
    rw [udsBits_append, udsBits_cons, udsBits_nil, List.append_nil] at hm ⊢
    rw [List.length_append] at hm
    by_cases hle : m ≤ (udsBits v).length
    · rw [List.take_append_of_le_length hle]
      exact ih hv' m hm1 hle
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.mp hle)
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_assoc,
        Nat.add_sub_cancel_left, seqProduct_append]
      by_cases hr : r + 1 = c.bits.length
      · rw [List.take_of_length_le (by omega), ← seqProduct_append]
        exact hfull
      · cases c with
        | U =>
          simp [UDS.bits] at hm hr
          omega
        | D =>
          have hr0 : r = 0 := by
            simp [UDS.bits] at hm hr
            omega
          have ht : UDS.D.bits.take (r + 1) = [true] := by
            rw [hr0]
            rfl
          rw [ht, seqProduct_singleton_true]
          linarith
        | S =>
          have hr0 : r = 0 := by
            simp [UDS.bits] at hm hr
            omega
          rw [hr0]
          rw [seqProduct_append] at hfull
          norm_num [UDS.bits, seqProduct, factor] at hfull ⊢
          linarith

/-- The bits of a letter word of the product rule: an admissible word, or one followed
    by 0. -/
theorem admissible_or_of_udsStopWord (w : List UDS) (hw : UdsStopWord w) :
    Admissible (udsBits w) ∨ ∃ s, Admissible s ∧ udsBits w = s ++ [false] := by
  obtain ⟨hlt, hgt⟩ := hw
  induction w using List.reverseRecOn with
  | nil =>
    rw [udsBits_nil, seqProduct_nil] at hlt
    exact absurd hlt (lt_irrefl 1)
  | append_singleton v c _ =>
    have hv : ∀ i, 1 ≤ i → i ≤ v.length → 1 < seqProduct (udsBits (v.take i)) := by
      intro i hi1 hi
      have hi' : i < (v ++ [c]).length := by
        rw [List.length_append, List.length_singleton]
        omega
      have h := hgt i hi1 hi'
      rwa [List.take_append_of_le_length hi] at h
    have hpre := one_lt_seqProduct_take_udsBits v hv
    have h0 := one_le_seqProduct_udsBits v hv
    rw [udsBits_append, udsBits_cons, udsBits_nil, List.append_nil] at hlt ⊢
    have hinner : ∀ (t : List Bool), (∀ m, 1 ≤ m → m < t.length →
        1 < seqProduct ((udsBits v ++ t).take ((udsBits v).length + m))) →
        seqProduct (udsBits v ++ t) < 1 → Admissible (udsBits v ++ t) := by
      intro t ht htl
      refine ⟨fun m hm1 hm => ?_, htl⟩
      by_cases hle : m ≤ (udsBits v).length
      · rw [List.take_append_of_le_length hle]
        exact hpre m hm1 hle
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.mp hle)
        rw [List.length_append] at hm
        exact ht (r + 1) (by omega) (by omega)
    cases c with
    | U =>
      rw [seqProduct_append] at hlt
      have hU : seqProduct UDS.U.bits = 3 / 2 := seqProduct_singleton_true
      rw [hU] at hlt
      linarith
    | D =>
      left
      refine hinner _ (fun m hm1 hm => ?_) hlt
      have hm' : m = 1 := by
        simp [UDS.bits] at hm
        omega
      rw [hm', List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
        seqProduct_append]
      have ht : UDS.D.bits.take 1 = [true] := rfl
      rw [ht, seqProduct_singleton_true]
      linarith
    | S =>
      by_cases hS : seqProduct (udsBits v ++ [false]) < 1
      · right
        refine ⟨udsBits v ++ [false], hinner _ (fun m hm1 hm => ?_) hS, ?_⟩
        · simp at hm
          omega
        · simp [UDS.bits]
      · left
        have hne : seqProduct (udsBits v ++ [false]) ≠ 1 := seqProduct_ne_one _ (by simp)
        have hgt1 : 1 < seqProduct (udsBits v ++ [false]) :=
          lt_of_le_of_ne (not_lt.mp hS) (Ne.symm hne)
        refine hinner _ (fun m hm1 hm => ?_) hlt
        have hm' : m = 1 := by
          simp [UDS.bits] at hm
          omega
        rw [hm', List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
        exact hgt1

/-- A letter word whose bits are b: its proper nonempty letter prefixes are proper
    nonempty bit prefixes of b. -/
theorem udsBits_take_eq (w : List UDS) (i : ℕ) (hi1 : 1 ≤ i) (hi : i < w.length) :
    (udsBits w).take (udsBits (w.take i)).length = udsBits (w.take i) ∧
      1 ≤ (udsBits (w.take i)).length ∧
        (udsBits (w.take i)).length < (udsBits w).length ∧
          udsBits w = udsBits (w.take i) ++ udsBits (w.drop i) := by
  have hsplit : udsBits w = udsBits (w.take i) ++ udsBits (w.drop i) := by
    rw [← udsBits_append, List.take_append_drop]
  have hne1 : w.take i ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_take, List.length_nil] at this
    omega
  have hne2 : w.drop i ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_drop, List.length_nil] at this
    omega
  have h1 := List.length_pos_of_ne_nil (udsBits_ne_nil _ hne1)
  have h2 := List.length_pos_of_ne_nil (udsBits_ne_nil _ hne2)
  refine ⟨?_, h1, ?_, hsplit⟩
  · rw [hsplit, List.take_left]
  · rw [hsplit, List.length_append]
    omega

/-- An admissible word of Order at least 1 is the bits of a letter word of the product
    rule. -/
theorem udsStopWord_udsDecode (s : List Bool) (hA : Admissible s) (hm : 1 ≤ order s) :
    udsBits (udsDecode s) = s ∧ UdsStopWord (udsDecode s) := by
  have hb := udsBits_udsDecode s (hA.head_true hm)
  refine ⟨hb, ?_, fun i hi1 hi => ?_⟩
  · rw [hb]
    exact hA.lt_one
  · obtain ⟨htake, hl1, hl, -⟩ := udsBits_take_eq (udsDecode s) i hi1 hi
    rw [← htake, hb]
    rw [hb] at hl
    exact hA.prefix_gt _ hl1 hl

/-- An admissible word of Order at least 1 followed by 0 is the bits of a letter word of
    the product rule. -/
theorem udsStopWord_udsDecode_append (s : List Bool) (hA : Admissible s) (hm : 1 ≤ order s) :
    udsBits (udsDecode (s ++ [false])) = s ++ [false] ∧
      UdsStopWord (udsDecode (s ++ [false])) := by
  have hhead : (s ++ [false]).head? = some true := by
    rw [List.head?_append, hA.head_true hm]
    rfl
  have hb := udsBits_udsDecode (s ++ [false]) hhead
  refine ⟨hb, ?_, fun i hi1 hi => ?_⟩
  · rw [hb, seqProduct_append]
    have h := hA.lt_one
    have hpos := seqProduct_pos s
    norm_num [seqProduct, factor]
    rw [seqProduct] at h
    linarith
  · obtain ⟨htake, hl1, hl, hsplit⟩ := udsBits_take_eq (udsDecode (s ++ [false])) i hi1 hi
    set w := udsDecode (s ++ [false])
    rw [hb, List.length_append, List.length_singleton] at hl
    have hne : (udsBits (w.take i)).length ≠ s.length := by
      intro heq
      have hp : udsBits (w.take i) = s := by
        have h := htake
        rw [hb, heq, List.take_left] at h
        exact h.symm
      rw [hb, hp] at hsplit
      exact udsBits_ne_singleton_false _ (List.append_cancel_left hsplit).symm
    have hlt' : (udsBits (w.take i)).length < s.length := by omega
    have h := hA.prefix_gt _ hl1 hlt'
    rwa [← List.take_append_of_le_length hlt'.le (l₂ := [false]), ← hb, htake] at h

/-- The letter words of `udsStopSet m`, m ≥ 1, are those of the product rule with M = m. -/
theorem mem_udsStopSet (m : ℕ) (hm : 1 ≤ m) (w : List UDS) :
    w ∈ udsStopSet m ↔ UdsStopWord w ∧ order (udsBits w) = m := by
  simp only [udsStopSet, Finset.mem_union, Finset.mem_image, mem_admSet]
  constructor
  · rintro (⟨s, ⟨hA, ho⟩, rfl⟩ | ⟨s, ⟨hA, ho⟩, rfl⟩)
    · obtain ⟨hb, hw⟩ := udsStopWord_udsDecode s hA (by omega)
      exact ⟨hw, by rw [hb, ho]⟩
    · obtain ⟨hb, hw⟩ := udsStopWord_udsDecode_append s hA (by omega)
      exact ⟨hw, by rw [hb, order_append_false, ho]⟩
  · rintro ⟨hw, ho⟩
    rcases admissible_or_of_udsStopWord w hw with hA | ⟨s, hA, hs⟩
    · exact Or.inl ⟨udsBits w, ⟨hA, ho⟩, udsDecode_udsBits w⟩
    · refine Or.inr ⟨s, ⟨hA, ?_⟩, ?_⟩
      · rw [← order_append_false, ← hs, ho]
      · rw [← hs, udsDecode_udsBits]

theorem udsBits_length_of_mem_image (m : ℕ) (hm : 1 ≤ m) (w : List UDS)
    (hw : w ∈ (admSet m).image udsDecode) : (udsBits w).length = p2_of m := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hA, ho⟩ := (mem_admSet m s).mp hs
  rw [(udsStopWord_udsDecode s hA (by omega)).1, admissible_length s hA, ho]

theorem udsBits_length_of_mem_image_append (m : ℕ) (hm : 1 ≤ m) (w : List UDS)
    (hw : w ∈ (admSet m).image (fun s => udsDecode (s ++ [false]))) :
    (udsBits w).length = p2_of m + 1 := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hA, ho⟩ := (mem_admSet m s).mp hs
  rw [(udsStopWord_udsDecode_append s hA (by omega)).1, List.length_append,
    admissible_length s hA, ho, List.length_singleton]

theorem card_image_udsDecode (m : ℕ) (hm : 1 ≤ m) :
    ((admSet m).image udsDecode).card = (admSet m).card := by
  apply Finset.card_image_of_injOn
  intro s hs s' hs' h
  obtain ⟨hA, ho⟩ := (mem_admSet m s).mp hs
  obtain ⟨hA', ho'⟩ := (mem_admSet m s').mp hs'
  have hb := (udsStopWord_udsDecode s hA (by omega)).1
  have hb' := (udsStopWord_udsDecode s' hA' (by omega)).1
  rw [← hb, ← hb']
  exact congrArg udsBits h

theorem card_image_udsDecode_append (m : ℕ) (hm : 1 ≤ m) :
    ((admSet m).image (fun s => udsDecode (s ++ [false]))).card = (admSet m).card := by
  apply Finset.card_image_of_injOn
  intro s hs s' hs' h
  obtain ⟨hA, ho⟩ := (mem_admSet m s).mp hs
  obtain ⟨hA', ho'⟩ := (mem_admSet m s').mp hs'
  have hb := (udsStopWord_udsDecode_append s hA (by omega)).1
  have hb' := (udsStopWord_udsDecode_append s' hA' (by omega)).1
  have h' := congrArg udsBits h
  simp only at h'
  rw [hb, hb'] at h'
  exact List.append_cancel_right h'

/-- For m ≥ 1 there are 2 A100982(m) letter words of the product rule with M = m. -/
theorem card_udsStopSet (m : ℕ) (hm : 1 ≤ m) : (udsStopSet m).card = 2 * (admSet m).card := by
  rw [udsStopSet, Finset.card_union_of_disjoint, card_image_udsDecode m hm,
    card_image_udsDecode_append m hm]
  · ring
  · rw [Finset.disjoint_left]
    intro w hw hw'
    have h1 := udsBits_length_of_mem_image m hm w hw
    have h2 := udsBits_length_of_mem_image_append m hm w hw'
    omega

/-- A100982(m) of them have p2(m) bits. -/
theorem card_udsStopSet_filter_p2 (m : ℕ) (hm : 1 ≤ m) :
    ((udsStopSet m).filter (fun w => (udsBits w).length = p2_of m)).card = (admSet m).card := by
  have hne : ∀ w ∈ (admSet m).image (fun s => udsDecode (s ++ [false])),
      ¬ (udsBits w).length = p2_of m := by
    intro w hw
    rw [udsBits_length_of_mem_image_append m hm w hw]
    omega
  rw [udsStopSet, Finset.filter_union, Finset.filter_true_of_mem
    (fun w hw => udsBits_length_of_mem_image m hm w hw), Finset.filter_false_of_mem hne,
    Finset.union_empty, card_image_udsDecode m hm]

/-- A100982(m) of them have p2(m) + 1 bits. -/
theorem card_udsStopSet_filter_p2_succ (m : ℕ) (hm : 1 ≤ m) :
    ((udsStopSet m).filter (fun w => (udsBits w).length = p2_of m + 1)).card =
      (admSet m).card := by
  have hne : ∀ w ∈ (admSet m).image udsDecode, ¬ (udsBits w).length = p2_of m + 1 := by
    intro w hw
    rw [udsBits_length_of_mem_image m hm w hw]
    omega
  rw [udsStopSet, Finset.filter_union, Finset.filter_false_of_mem hne,
    Finset.filter_true_of_mem (fun w hw => udsBits_length_of_mem_image_append m hm w hw),
    Finset.empty_union, card_image_udsDecode_append m hm]

end AcceleratedCollatz
