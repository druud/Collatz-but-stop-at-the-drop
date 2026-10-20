-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TWordQ

/-!
  First-drop split of the words of the q-family (odd q ≥ 3). Every admissible s of
  Order ≥ 1 is 1 :: (B1 ++ ... ++ Bm) with every block Bi admissible, of any Order
  (`exists_splitQ`); an Order-0 block is the word [0] (`admissibleQ_singleton_false`).
  The blocks are unique (`splitQ_unique`, from `flatten_inj_of_admissibleQ`) and their
  Orders sum to order s - 1 (`order_splitQ`). Conversely, for admissible blocks,
  1 :: (B1 ++ ... ++ Bm) is admissible iff the level is above 1 at every inner block
  boundary and below 1 at the end (`admissibleQ_split_iff`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

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

end AcceleratedCollatz
