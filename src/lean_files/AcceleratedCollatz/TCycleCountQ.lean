-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCycleCount
import AcceleratedCollatz.TSplitQ

/-!
  The mass per Order for odd q ≥ 3 (C107, M. Winkler's item 6): `TCycleCount` in the q-family of
  `TWordQ`, a one being x ↦ (qx + 1)/2 (factor q/2), a zero x ↦ x/2 (factor 1/2).

  The proof of `choose_p2_eq_split` uses of 3 only that it is odd and at least 3: distinct
  prefixes have distinct levels (`lvQ_inj`, from `q_pow_mul_two_pow_ne`), and
  2^(p2(m) - 1) < q^m < 2^p2(m). So, with p2Q q n the least L with q^n < 2^L and
  N_q(n) = |admSetQ q n|,

    C(p2Q q n, n) = p2Q q n · N_q(n) + Σ_m N_q(m) C(p2Q q (n - m), n - m)   (`choose_p2Q_eq_split`),

  the sum over 1 ≤ m < n with p2Q q m + p2Q q (n - m) = p2Q q n, that is with
  2^p2Q q m · q^n < 2^p2Q q n · q^m (`mem_splitOrdersQ_iff`). For q = 3 this is
  `choose_p2_eq_split` (`p2Q_three`, `admissibleQ_three`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-! ### Words, levels and powers -/

theorem seqProductQ_eq (q : ℕ) (l : List Bool) :
    seqProductQ q l = (q : ℚ) ^ order l / 2 ^ l.length := by
  rw [eq_div_iff (by positivity), seqProductQ_mul_pow]

theorem seqProductQ_rotate (q : ℕ) (l : List Bool) (k : ℕ) :
    seqProductQ q (l.rotate k) = seqProductQ q l := by
  rw [seqProductQ_eq, seqProductQ_eq, order_rotate, List.length_rotate]

theorem seqProductQ_lt_one_iff (q : ℕ) (l : List Bool) :
    seqProductQ q l < 1 ↔ q ^ order l < 2 ^ l.length := by
  rw [seqProductQ_eq, div_lt_one₀ (by positivity)]
  constructor <;> intro h <;> exact_mod_cast h

/-- q^a 2^x ≠ q^b 2^y for a < b (q odd). -/
theorem q_pow_mul_two_pow_ne (hodd : Odd q) (hq : 3 ≤ q) {a b : ℕ} (hab : a < b) (x y : ℕ) :
    q ^ a * 2 ^ x ≠ q ^ b * 2 ^ y := by
  intro h
  have hb : q ^ b = q ^ a * q ^ (b - a) := by rw [← pow_add]; congr 1; omega
  rw [hb, mul_assoc] at h
  have h' : 2 ^ x = q ^ (b - a) * 2 ^ y := Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) _) h
  have h1 : 1 < q ^ (b - a) := Nat.one_lt_pow (by omega) (by omega)
  rcases le_or_gt x y with hxy | hxy
  · have h2 : 2 ^ x ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) hxy
    have h3 : 0 < 2 ^ y := by positivity
    nlinarith
  · have hx : 2 ^ x = 2 ^ (x - y) * 2 ^ y := by rw [← pow_add]; congr 1; omega
    rw [hx] at h'
    exact two_pow_ne_q_pow hodd hq (by omega)
      (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ y) h')

/-- The level of the first i letters. -/
abbrev lvQ (q : ℕ) (v : List Bool) (i : ℕ) : ℚ := seqProductQ q (v.take i)

theorem lvQ_pos (hq0 : 0 < q) (v : List Bool) (i : ℕ) : 0 < lvQ q v i := seqProductQ_pos hq0 _

theorem lvQ_zero (q : ℕ) (v : List Bool) : lvQ q v 0 = 1 := by simp [lvQ, seqProductQ]

theorem lvQ_length (q : ℕ) (v : List Bool) : lvQ q v v.length = seqProductQ q v := by simp [lvQ]

/-- Distinct prefixes have distinct levels (q odd). -/
theorem lvQ_inj (hodd : Odd q) (hq : 3 ≤ q) {v : List Bool} {i j : ℕ} (hi : i ≤ v.length)
    (hj : j ≤ v.length) (h : lvQ q v i = lvQ q v j) : i = j := by
  have h1 := seqProductQ_mul_pow q (v.take i)
  have h2 := seqProductQ_mul_pow q (v.take j)
  rw [List.length_take, min_eq_left hi] at h1
  rw [List.length_take, min_eq_left hj] at h2
  have key : (q : ℚ) ^ order (v.take i) * 2 ^ j = (q : ℚ) ^ order (v.take j) * 2 ^ i := by
    rw [← h1, ← h2]; unfold lvQ at h; rw [h]; ring
  have keyN : q ^ order (v.take i) * 2 ^ j = q ^ order (v.take j) * 2 ^ i := by
    exact_mod_cast key
  rcases lt_trichotomy (order (v.take i)) (order (v.take j)) with hlt | heq | hgt
  · exact absurd keyN (q_pow_mul_two_pow_ne hodd hq hlt _ _)
  · rw [heq] at keyN
    have : 2 ^ j = 2 ^ i := Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) _) keyN
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  · exact absurd keyN.symm (q_pow_mul_two_pow_ne hodd hq hgt _ _)

/-! ### Ladder words and their rotations -/

/-- A ladder word: its whole level lies below the level of every proper prefix (the empty one
    too). -/
def LadderQ (q : ℕ) (v : List Bool) : Prop := ∀ i < v.length, seqProductQ q v < lvQ q v i

instance (q : ℕ) (v : List Bool) : Decidable (LadderQ q v) := by unfold LadderQ; infer_instance

theorem lvQ_rotate_le {u : List Bool} {r t : ℕ} (hr : r ≤ u.length) (ht : t ≤ u.length - r) :
    lvQ q (u.rotate r) t * lvQ q u r = lvQ q u (r + t) := by
  unfold lvQ
  rw [List.rotate_eq_drop_append_take hr, List.take_append_of_le_length (by simp; omega),
    List.take_add, seqProductQ_append, mul_comm]

theorem lvQ_rotate_gt {u : List Bool} {r t : ℕ} (hr : r ≤ u.length) (ht : u.length - r < t)
    (htL : t ≤ u.length) :
    lvQ q (u.rotate r) t * lvQ q u r = seqProductQ q u * lvQ q u (t - (u.length - r)) := by
  unfold lvQ
  have hsplit : u = u.take r ++ u.drop r := (List.take_append_drop r u).symm
  have hP : seqProductQ q u = seqProductQ q (u.take r) * seqProductQ q (u.drop r) := by
    conv_lhs => rw [hsplit]
    rw [seqProductQ_append]
  rw [List.rotate_eq_drop_append_take hr, List.take_append, List.length_drop,
    List.take_of_length_le (by simp; omega), List.take_take, min_eq_left (by omega),
    seqProductQ_append, hP]
  ring

/-- A rotation is a ladder word iff its start lies below all earlier prefixes, and the whole
    level from there stays below all later ones. -/
theorem ladderQ_rotate_iff (hq0 : 0 < q) {u : List Bool} {r : ℕ} (hr : r < u.length) :
    LadderQ q (u.rotate r) ↔ (∀ j < r, lvQ q u r < lvQ q u j) ∧
      ∀ s, r ≤ s → s < u.length → lvQ q u r * seqProductQ q u < lvQ q u s := by
  set L := u.length with hL
  have hPr := lvQ_pos hq0 u r
  have hP := seqProductQ_pos hq0 u
  unfold LadderQ
  rw [List.length_rotate, seqProductQ_rotate]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun s hs1 hs2 => ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have ht := h (L - r) (by omega)
        have e := lvQ_rotate_le (q := q) (u := u) (r := r) (t := L - r) hr.le le_rfl
        rw [show r + (L - r) = L by omega, hL, lvQ_length] at e
        rw [lvQ_zero]
        have : seqProductQ q u * lvQ q u r < lvQ q (u.rotate r) (L - r) * lvQ q u r :=
          mul_lt_mul_of_pos_right ht hPr
        rw [e] at this
        nlinarith
      · have ht := h (j + (L - r)) (by omega)
        have e := lvQ_rotate_gt (q := q) (u := u) (r := r) (t := j + (L - r)) hr.le (by omega)
          (by omega)
        rw [show j + (L - r) - (L - r) = j by omega] at e
        have : seqProductQ q u * lvQ q u r < lvQ q (u.rotate r) (j + (L - r)) * lvQ q u r :=
          mul_lt_mul_of_pos_right ht hPr
        rw [e] at this
        nlinarith
    · have ht := h (s - r) (by omega)
      have e := lvQ_rotate_le (q := q) (u := u) (r := r) (t := s - r) hr.le (by omega)
      rw [show r + (s - r) = s by omega] at e
      have : seqProductQ q u * lvQ q u r < lvQ q (u.rotate r) (s - r) * lvQ q u r :=
        mul_lt_mul_of_pos_right ht hPr
      rw [e] at this
      linarith
  · rintro ⟨h1, h2⟩ t ht
    rcases Nat.lt_or_ge (L - r) t with hgt | hle
    · have e := lvQ_rotate_gt (q := q) (u := u) (r := r) (t := t) hr.le hgt ht.le
      have hj := h1 (t - (L - r)) (by omega)
      have : seqProductQ q u * lvQ q u r < lvQ q (u.rotate r) t * lvQ q u r := by
        rw [e]; exact mul_lt_mul_of_pos_left hj hP
      exact lt_of_mul_lt_mul_right this hPr.le
    · have e := lvQ_rotate_le (q := q) (u := u) (r := r) (t := t) hr.le hle
      have : seqProductQ q u * lvQ q u r < lvQ q (u.rotate r) t * lvQ q u r := by
        rw [e]
        rcases Nat.lt_or_ge (r + t) L with hs | hs
        · rw [mul_comm]; exact h2 (r + t) (by omega) hs
        · have hrt : r + t = L := by omega
          rw [hrt, hL, lvQ_length]
          have h0 := h1 0 (by omega)
          rw [lvQ_zero] at h0
          nlinarith
      exact lt_of_mul_lt_mul_right this hPr.le

/-- A rotation of a ladder word, by 0 < r < L, is a ladder word iff level r is below all
    earlier levels. -/
theorem ladderQ_rotate_iff_of_ladderQ (hq0 : 0 < q) {v : List Bool} (hv : LadderQ q v) {r : ℕ}
    (h0 : 0 < r) (hr : r < v.length) :
    LadderQ q (v.rotate r) ↔ ∀ j < r, lvQ q v r < lvQ q v j := by
  rw [ladderQ_rotate_iff hq0 hr]
  refine ⟨fun h => h.1, fun h => ⟨h, fun s _ hs => ?_⟩⟩
  have h1 : lvQ q v r < 1 := by have := h 0 h0; rwa [lvQ_zero] at this
  calc lvQ q v r * seqProductQ q v < 1 * seqProductQ q v :=
        mul_lt_mul_of_pos_right h1 (seqProductQ_pos hq0 _)
    _ = seqProductQ q v := one_mul _
    _ < lvQ q v s := hv s hs

/-- A word with level below 1 has a ladder rotation (at its lowest level). -/
theorem exists_ladderQ_rotate (hodd : Odd q) (hq : 3 ≤ q) {u : List Bool} (hu : u ≠ [])
    (hsp : seqProductQ q u < 1) : ∃ r, r < u.length ∧ LadderQ q (u.rotate r) := by
  have hq0 : 0 < q := by omega
  have hL : 0 < u.length := List.length_pos_iff.mpr hu
  obtain ⟨r, hr, hmin⟩ := (Finset.range u.length).exists_min_image (lvQ q u)
    ⟨0, Finset.mem_range.2 hL⟩
  rw [Finset.mem_range] at hr
  refine ⟨r, hr, (ladderQ_rotate_iff hq0 hr).2 ⟨fun j hj => ?_, fun s hrs hs => ?_⟩⟩
  · rcases (hmin j (Finset.mem_range.2 (by omega))).lt_or_eq with h | h
    · exact h
    · exact absurd (lvQ_inj hodd hq hr.le (by omega) h) (by omega)
  · calc lvQ q u r * seqProductQ q u < lvQ q u r * 1 :=
          mul_lt_mul_of_pos_left hsp (lvQ_pos hq0 _ _)
      _ = lvQ q u r := mul_one _
      _ ≤ lvQ q u s := hmin s (Finset.mem_range.2 hs)

/-- The places r < L such that no rotation of v by L - r .. L - 1 is a ladder word. -/
def tsetQ (q : ℕ) (v : List Bool) : Finset ℕ :=
  (Finset.range v.length).filter
    (fun r => ∀ s ∈ Finset.Ico (v.length - r) v.length, ¬ LadderQ q (v.rotate s))

/-- The ladder words of length p2Q q n and Order n. -/
def ladSetQ (q n : ℕ) : Finset (List Bool) := (wordSet (p2Q q n) n).filter (LadderQ q)

theorem first_of_tsetQ {v : List Bool} (hv : LadderQ q v) {r : ℕ} (hr : r ∈ tsetQ q v) :
    LadderQ q ((v.rotate (v.length - r)).rotate r) ∧
      ∀ s < r, ¬ LadderQ q ((v.rotate (v.length - r)).rotate s) := by
  rw [tsetQ, Finset.mem_filter, Finset.mem_range] at hr
  refine ⟨by rw [rotate_sub_rotate v hr.1.le]; exact hv, fun s hs => ?_⟩
  rw [List.rotate_rotate]
  exact hr.2 _ (Finset.mem_Ico.2 ⟨by omega, by omega⟩)

/-- Every word of length p2Q q n and Order n is v rotated back by r, for exactly one ladder
    word v and r ∈ tsetQ q v. -/
theorem card_wordSet_eq_sum_tsetQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (wordSet (p2Q q n) n).card = ∑ v ∈ ladSetQ q n, (tsetQ q v).card := by
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_bij (fun (p : Σ _ : List Bool, ℕ) _ => p.1.rotate (p.1.length - p.2))
  · rintro ⟨v, r⟩ hp
    simp only [Finset.mem_sigma, ladSetQ, Finset.mem_filter, mem_wordSet] at hp ⊢
    exact ⟨by rw [List.length_rotate]; exact hp.1.1.1, by rw [order_rotate]; exact hp.1.1.2⟩
  · rintro ⟨v, r⟩ hp ⟨v', r'⟩ hp' he
    simp only [Finset.mem_sigma, ladSetQ, Finset.mem_filter, mem_wordSet] at hp hp' he
    obtain ⟨h1, h2⟩ := first_of_tsetQ hp.1.2 hp.2
    obtain ⟨h1', h2'⟩ := first_of_tsetQ hp'.1.2 hp'.2
    rw [he] at h1 h2
    have hrr : r = r' := by
      rcases lt_trichotomy r r' with h | h | h
      · exact absurd h1 (h2' r h)
      · exact h
      · exact absurd h1' (h2 r' h)
    subst hrr
    have hr1 := (Finset.mem_range.1 (Finset.mem_filter.1 hp.2).1).le
    have hr2 := (Finset.mem_range.1 (Finset.mem_filter.1 hp'.2).1).le
    have hvv : v = v' := by
      rw [← rotate_sub_rotate v hr1, ← rotate_sub_rotate v' hr2, he]
    subst hvv
    rfl
  · intro u hu
    rw [mem_wordSet] at hu
    have hLpos : 1 ≤ p2Q q n := one_le_p2Q q n
    have hune : u ≠ [] := by
      intro h; rw [h] at hu; simp at hu; omega
    have hsp : seqProductQ q u < 1 := by
      rw [seqProductQ_lt_one_iff, hu.1, hu.2]; exact p2Q_spec hq n
    have hex := exists_ladderQ_rotate hodd hq hune hsp
    classical
    obtain ⟨hrL, hrlad⟩ := Nat.find_spec hex
    refine ⟨⟨u.rotate (Nat.find hex), Nat.find hex⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, ladSetQ, Finset.mem_filter, mem_wordSet, tsetQ,
        Finset.mem_range, List.length_rotate, order_rotate, Finset.mem_Ico]
      refine ⟨⟨⟨hu.1, hu.2⟩, hrlad⟩, hrL, fun s hs hl => ?_⟩
      rw [List.rotate_rotate, ← List.rotate_mod,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hl
      exact Nat.find_min hex (show Nat.find hex + s - u.length < Nat.find hex by omega)
        ⟨by omega, hl⟩
    · change (u.rotate (Nat.find hex)).rotate ((u.rotate (Nat.find hex)).length - Nat.find hex) = u
      rw [List.length_rotate, List.rotate_rotate, Nat.add_sub_cancel' hrL.le, List.rotate_length]

/-! ### Admissible words in front of ladder words -/

theorem lvQ_append_left {d w : List Bool} {i : ℕ} (hi : i ≤ d.length) :
    lvQ q (d ++ w) i = lvQ q d i := by
  simp only [lvQ, List.take_append_of_le_length hi]

theorem lvQ_append_right (d w : List Bool) (j : ℕ) :
    lvQ q (d ++ w) (d.length + j) = seqProductQ q d * lvQ q w j := by
  simp only [lvQ, List.take_length_add_append, seqProductQ_append]

theorem one_le_lvQ_of_admissibleQ {d : List Bool} (hd : AdmissibleQ q d) {i : ℕ}
    (hi : i < d.length) : 1 ≤ lvQ q d i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h, lvQ_zero]
  · exact (hd.prefix_gt i h hi).le

theorem ladderQ_of_admissibleQ {d : List Bool} (hd : AdmissibleQ q d) : LadderQ q d :=
  fun _ hi => lt_of_lt_of_le hd.lt_one (one_le_lvQ_of_admissibleQ hd hi)

theorem seqProductQ_lt_one_of_ladderQ {v : List Bool} (hv : LadderQ q v) (hne : v ≠ []) :
    seqProductQ q v < 1 := by
  have := hv 0 (List.length_pos_iff.mpr hne); rwa [lvQ_zero] at this

/-- No rotation of an admissible word by 0 < s < L is a ladder word. -/
theorem not_ladderQ_rotate_of_admissibleQ (hq0 : 0 < q) {d : List Bool} (hd : AdmissibleQ q d)
    {s : ℕ} (h0 : 0 < s) (hs : s < d.length) : ¬ LadderQ q (d.rotate s) := by
  rw [ladderQ_rotate_iff_of_ladderQ hq0 (ladderQ_of_admissibleQ hd) h0 hs]
  intro h
  have h1 := h 0 h0
  rw [lvQ_zero] at h1
  exact absurd (hd.prefix_gt s h0 hs) (not_lt.2 h1.le)

theorem tsetQ_of_admissibleQ (hq0 : 0 < q) {d : List Bool} (hd : AdmissibleQ q d) :
    tsetQ q d = Finset.range d.length := by
  apply Finset.filter_true_of_mem
  intro r hr s hs
  rw [Finset.mem_range] at hr
  rw [Finset.mem_Ico] at hs
  exact not_ladderQ_rotate_of_admissibleQ hq0 hd (by omega) hs.2

/-- An admissible word followed by a nonempty ladder word is a ladder word. -/
theorem ladderQ_append (hq0 : 0 < q) {d w : List Bool} (hd : AdmissibleQ q d)
    (hw : LadderQ q w) (hne : w ≠ []) : LadderQ q (d ++ w) := by
  have hw1 := seqProductQ_lt_one_of_ladderQ hw hne
  intro i hi
  rw [seqProductQ_append]
  rcases le_or_gt d.length i with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [lvQ_append_right]
    rw [List.length_append] at hi
    exact mul_lt_mul_of_pos_left (hw j (by omega)) (seqProductQ_pos hq0 _)
  · rw [lvQ_append_left h.le]
    calc seqProductQ q d * seqProductQ q w < 1 * 1 :=
          mul_lt_mul'' hd.lt_one hw1 (seqProductQ_pos hq0 _).le (seqProductQ_pos hq0 _).le
      _ = 1 := one_mul 1
      _ ≤ lvQ q d i := one_le_lvQ_of_admissibleQ hd h

/-- The ladder rotations of d ++ w from |d| on are those of w, shifted by |d|. -/
theorem ladderQ_rotate_append (hq0 : 0 < q) {d w : List Bool} (hd : AdmissibleQ q d)
    (hw : LadderQ q w) (hne : w ≠ []) {j : ℕ} (hj : j < w.length) :
    LadderQ q ((d ++ w).rotate (d.length + j)) ↔ LadderQ q (w.rotate j) := by
  have hdpos : 0 < d.length := by
    rcases Nat.eq_zero_or_pos d.length with h | h
    · have := hd.lt_one; rw [List.length_eq_zero_iff.1 h] at this; simp [seqProductQ] at this
    · exact h
  have hv := ladderQ_append hq0 hd hw hne
  have hlen : d.length + j < (d ++ w).length := by rw [List.length_append]; omega
  rw [ladderQ_rotate_iff_of_ladderQ hq0 hv (by omega) hlen, lvQ_append_right]
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    rw [List.rotate_zero, lvQ_zero, mul_one]
    refine ⟨fun _ => hw, fun _ i hi => ?_⟩
    rw [Nat.add_zero] at hi
    rw [lvQ_append_left hi.le]
    exact lt_of_lt_of_le hd.lt_one (one_le_lvQ_of_admissibleQ hd hi)
  rw [ladderQ_rotate_iff_of_ladderQ hq0 hw h0 hj]
  have hsd := seqProductQ_pos hq0 d
  constructor
  · intro h i hi
    have := h (d.length + i) (by omega)
    rw [lvQ_append_right] at this
    exact lt_of_mul_lt_mul_left this hsd.le
  · intro h i hi
    rcases le_or_gt d.length i with hle | hlt
    · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [lvQ_append_right]
      exact mul_lt_mul_of_pos_left (h i' (by omega)) hsd
    · rw [lvQ_append_left hlt.le]
      have h1 := h 0 h0
      rw [lvQ_zero] at h1
      calc seqProductQ q d * lvQ q w j < 1 * 1 :=
            mul_lt_mul'' hd.lt_one h1 hsd.le (lvQ_pos hq0 _ _).le
        _ = 1 := one_mul 1
        _ ≤ lvQ q d i := one_le_lvQ_of_admissibleQ hd hlt

/-- tsetQ q (d ++ w) = tsetQ q w. -/
theorem tsetQ_append (hq0 : 0 < q) {d w : List Bool} (hd : AdmissibleQ q d) (hw : LadderQ q w)
    (hne : w ≠ []) : tsetQ q (d ++ w) = tsetQ q w := by
  have hdl : (d ++ w).length = d.length + w.length := List.length_append
  have hwpos : 0 < w.length := List.length_pos_iff.mpr hne
  have hat : LadderQ q ((d ++ w).rotate (d.length + 0)) :=
    (ladderQ_rotate_append hq0 hd hw hne hwpos).2 (by rw [List.rotate_zero]; exact hw)
  ext r
  simp only [tsetQ, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, hdl]
  constructor
  · rintro ⟨hr, h⟩
    have hrw : r < w.length := by
      by_contra hc
      exact h (d.length + 0) ⟨by omega, by omega⟩ hat
    refine ⟨hrw, fun s hs => ?_⟩
    have := h (d.length + s) ⟨by omega, by omega⟩
    rwa [ladderQ_rotate_append hq0 hd hw hne hs.2] at this
  · rintro ⟨hrw, h⟩
    refine ⟨by omega, fun s hs => ?_⟩
    obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le (show d.length ≤ s by omega)
    rw [ladderQ_rotate_append hq0 hd hw hne (by omega)]
    exact h s' ⟨by omega, by omega⟩

/-! ### The split -/

/-- The split Orders of n: 1 ≤ m < n with p2Q q m + p2Q q (n - m) = p2Q q n. -/
def splitOrdersQ (q n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun m => p2Q q m + p2Q q (n - m) = p2Q q n)

/-- Admissible words of a split Order m with a ladder word of Order n - m. -/
def splitSetQ (q n : ℕ) : Finset (Σ _ : ℕ, List Bool × List Bool) :=
  (splitOrdersQ q n).sigma (fun m => admSetQ q m ×ˢ ladSetQ q (n - m))

theorem admSetQ_subset_ladSetQ (hq : 3 ≤ q) (n : ℕ) : admSetQ q n ⊆ ladSetQ q n := by
  intro d hd
  rw [mem_admSetQ (by omega)] at hd
  simp only [ladSetQ, Finset.mem_filter, mem_wordSet]
  exact ⟨⟨by rw [admissibleQ_length (by omega) hd.1, hd.2], hd.2⟩, ladderQ_of_admissibleQ hd.1⟩

theorem append_mem_ladSetQ (hq : 3 ≤ q) {n m : ℕ} (hm : m ∈ splitOrdersQ q n) {d w : List Bool}
    (hd : d ∈ admSetQ q m) (hw : w ∈ ladSetQ q (n - m)) : d ++ w ∈ ladSetQ q n \ admSetQ q n := by
  simp only [splitOrdersQ, Finset.mem_filter, Finset.mem_Ico] at hm
  rw [mem_admSetQ (by omega)] at hd
  simp only [ladSetQ, Finset.mem_filter, mem_wordSet] at hw
  have hdl : d.length = p2Q q m := by rw [admissibleQ_length (by omega) hd.1, hd.2]
  have hwpos : 0 < w.length := by have := one_le_p2Q q (n - m); omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  rw [Finset.mem_sdiff, mem_admSetQ (by omega)]
  refine ⟨?_, fun h => ?_⟩
  · simp only [ladSetQ, Finset.mem_filter, mem_wordSet, List.length_append, order_append]
    exact ⟨⟨by rw [hdl, hw.1.1, hm.2], by rw [hd.2, hw.1.2]; omega⟩,
      ladderQ_append (by omega) hd.1 hw.2 hwne⟩
  · have hdpos : 1 ≤ d.length := by have := one_le_p2Q q m; omega
    have h1 := h.1.prefix_gt d.length hdpos (by rw [List.length_append]; omega)
    have e : seqProductQ q ((d ++ w).take d.length) = seqProductQ q d :=
      (lvQ_append_left le_rfl).trans (lvQ_length q d)
    rw [e] at h1
    exact absurd hd.1.lt_one (not_lt.2 h1.le)

/-- A non-admissible ladder word of Order n splits at its first level below 1. -/
theorem exists_ladderQ_split (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {v : List Bool}
    (hv : v ∈ ladSetQ q n \ admSetQ q n) :
    ∃ m d w, m ∈ splitOrdersQ q n ∧ d ∈ admSetQ q m ∧ w ∈ ladSetQ q (n - m) ∧ d ++ w = v := by
  have hq0 : 0 < q := by omega
  rw [Finset.mem_sdiff, mem_admSetQ (by omega)] at hv
  obtain ⟨hv, hna⟩ := hv
  simp only [ladSetQ, Finset.mem_filter, mem_wordSet] at hv
  obtain ⟨⟨hvl, hvo⟩, hvlad⟩ := hv
  have hsp : seqProductQ q v < 1 := by
    rw [seqProductQ_lt_one_iff, hvl, hvo]; exact p2Q_spec hq n
  have hex : ∃ g, 1 ≤ g ∧ g < v.length ∧ lvQ q v g < 1 := by
    by_contra hc
    apply hna
    refine ⟨⟨fun k hk1 hk2 => ?_, hsp⟩, hvo⟩
    have hge : 1 ≤ lvQ q v k := by
      by_contra h1
      exact hc ⟨k, hk1, hk2, lt_of_not_ge h1⟩
    rcases hge.lt_or_eq with h | h
    · exact h
    · have := lvQ_inj hodd hq (v := v) (i := 0) (j := k) (by omega) hk2.le
        (by rw [lvQ_zero]; exact h)
      omega
  classical
  obtain ⟨g, ⟨hg1, hgL, hglt⟩, hmin⟩ : ∃ g, (1 ≤ g ∧ g < v.length ∧ lvQ q v g < 1) ∧
      ∀ k < g, ¬ (1 ≤ k ∧ k < v.length ∧ lvQ q v k < 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  obtain ⟨d, w, hdw, hdl⟩ : ∃ d w, d ++ w = v ∧ d.length = g :=
    ⟨v.take g, v.drop g, List.take_append_drop g v, by rw [List.length_take]; omega⟩
  subst hdw hdl
  rw [List.length_append] at hgL hvl
  rw [order_append] at hvo
  have hwpos : 0 < w.length := by omega
  have hwne : w ≠ [] := List.ne_nil_of_length_pos hwpos
  rw [lvQ_append_left le_rfl, lvQ_length] at hglt
  have hdadm : AdmissibleQ q d := by
    refine ⟨fun k hk1 hk2 => ?_, hglt⟩
    have hk := hmin k hk2
    rw [lvQ_append_left hk2.le] at hk
    have hge : 1 ≤ lvQ q d k := by
      by_contra h1
      exact hk ⟨hk1, by rw [List.length_append]; omega, lt_of_not_ge h1⟩
    rcases hge.lt_or_eq with h | h
    · exact h
    · have := lvQ_inj hodd hq (v := d) (i := 0) (j := k) (by omega) hk2.le
        (by rw [lvQ_zero]; exact h)
      omega
  have hwlad : LadderQ q w := by
    intro j hj
    have h := hvlad (d.length + j) (by rw [List.length_append]; omega)
    rw [seqProductQ_append, lvQ_append_right] at h
    exact lt_of_mul_lt_mul_left h (seqProductQ_pos hq0 d).le
  have hdl := admissibleQ_length (by omega) hdadm
  have hw3 : q ^ order w < 2 ^ w.length :=
    (seqProductQ_lt_one_iff q w).1 (seqProductQ_lt_one_of_ladderQ hwlad hwne)
  have hd3 : q ^ order d < 2 ^ d.length := (seqProductQ_lt_one_iff q d).1 hdadm.lt_one
  have hlow := p2Q_spec_lower hq n
  rw [← hvl, ← hvo] at hlow
  have hw2 : 2 ^ (w.length - 1) < q ^ order w := by
    have h1 : 2 ^ d.length * 2 ^ (w.length - 1) < 2 ^ d.length * q ^ order w := by
      calc 2 ^ d.length * 2 ^ (w.length - 1) = 2 ^ (d.length + w.length - 1) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ q ^ (order d + order w) := hlow
        _ = q ^ order d * q ^ order w := pow_add _ _ _
        _ < 2 ^ d.length * q ^ order w :=
            Nat.mul_lt_mul_of_pos_right hd3 (pow_pos hq0 _)
    exact Nat.lt_of_mul_lt_mul_left h1
  have hpw : p2Q q (order w) = w.length :=
    le_antisymm ((q_pow_lt_two_pow_iff hq).mp hw3) (by
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp
        (lt_of_lt_of_le hw2 (p2Q_spec hq _).le)
      omega)
  have hp1 : 1 ≤ p2Q q (order d) := one_le_p2Q q _
  have hm0 : order d ≠ 0 := by
    intro h0
    have : order w = n := by omega
    rw [this] at hpw
    omega
  have hmn : order d ≠ n := by
    intro h
    rw [h] at hdl
    omega
  refine ⟨order d, d, w, ?_, ?_, ?_, rfl⟩
  · simp only [splitOrdersQ, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show n - order d = order w by omega, hpw, ← hdl]
    omega
  · rw [mem_admSetQ (by omega)]; exact ⟨hdadm, rfl⟩
  · simp only [ladSetQ, Finset.mem_filter, mem_wordSet]
    rw [show n - order d = order w by omega, hpw]
    exact ⟨⟨rfl, rfl⟩, hwlad⟩

theorem sum_tsetQ_split (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    ∑ v ∈ ladSetQ q n \ admSetQ q n, (tsetQ q v).card =
      ∑ p ∈ splitSetQ q n, (tsetQ q p.2.2).card := by
  symm
  apply Finset.sum_bij (fun (p : Σ _ : ℕ, List Bool × List Bool) _ => p.2.1 ++ p.2.2)
  · rintro ⟨m, d, w⟩ hp
    simp only [splitSetQ, Finset.mem_sigma, Finset.mem_product] at hp
    exact append_mem_ladSetQ hq hp.1 hp.2.1 hp.2.2
  · rintro ⟨m, d, w⟩ hp ⟨m', d', w'⟩ hp' h
    simp only [splitSetQ, Finset.mem_sigma, Finset.mem_product, mem_admSetQ (show 2 ≤ q by omega)]
      at hp hp' h
    have hpre : d <+: d ++ w := List.prefix_append d w
    have hpre' : d' <+: d ++ w := by rw [h]; exact List.prefix_append d' w'
    have hdd : d = d' := by
      by_contra hne
      rcases le_total d.length d'.length with hle | hle
      · exact admissibleQ_not_prefix hp.2.1.1 hp'.2.1.1 hne
          (List.prefix_of_prefix_length_le hpre hpre' hle)
      · exact admissibleQ_not_prefix hp'.2.1.1 hp.2.1.1 (Ne.symm hne)
          (List.prefix_of_prefix_length_le hpre' hpre hle)
    subst hdd
    have hww : w = w' := List.append_cancel_left h
    subst hww
    have hmm : m = m' := by rw [← hp.2.1.2, ← hp'.2.1.2]
    subst hmm
    rfl
  · intro v hv
    obtain ⟨m, d, w, hm, hd, hw, rfl⟩ := exists_ladderQ_split hodd hq hv
    refine ⟨⟨m, d, w⟩, ?_, rfl⟩
    simp only [splitSetQ, Finset.mem_sigma, Finset.mem_product]
    exact ⟨hm, hd, hw⟩
  · rintro ⟨m, d, w⟩ hp
    simp only [splitSetQ, Finset.mem_sigma, Finset.mem_product,
      mem_admSetQ (show 2 ≤ q by omega), ladSetQ, Finset.mem_filter, mem_wordSet] at hp
    have hwne : w ≠ [] :=
      List.ne_nil_of_length_pos (by rw [hp.2.2.1.1]; exact one_le_p2Q q _)
    rw [tsetQ_append (by omega) hp.2.1.1 hp.2.2.2 hwne]

/-- C107 (b): for odd q ≥ 3, C(p2Q q n, n) = p2Q q n N_q(n) + Σ_{m split} N_q(m) C(p2Q q (n - m),
    n - m), where N_q(n) = |admSetQ q n| and the split Orders are 1 ≤ m < n with
    p2Q q m + p2Q q (n - m) = p2Q q n. -/
theorem choose_p2Q_eq_split (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (p2Q q n).choose n = p2Q q n * (admSetQ q n).card +
      ∑ m ∈ splitOrdersQ q n, (admSetQ q m).card * (p2Q q (n - m)).choose (n - m) := by
  rw [← card_wordSet, card_wordSet_eq_sum_tsetQ hodd hq,
    ← Finset.sum_sdiff (admSetQ_subset_ladSetQ hq n), add_comm, sum_tsetQ_split hodd hq]
  congr 1
  · rw [Finset.sum_congr rfl (g := fun _ => p2Q q n), Finset.sum_const, smul_eq_mul, mul_comm]
    intro d hd
    rw [mem_admSetQ (by omega)] at hd
    rw [tsetQ_of_admissibleQ (by omega) hd.1, Finset.card_range,
      admissibleQ_length (by omega) hd.1, hd.2]
  · rw [splitSetQ, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_product]
    simp only
    rw [Finset.sum_congr rfl (g := fun _ => (p2Q q (n - m)).choose (n - m)), Finset.sum_const,
      smul_eq_mul]
    intro _ _
    rw [← card_wordSet_eq_sum_tsetQ hodd hq, card_wordSet]

/-- The split Orders by the floors: for 1 ≤ m < n, p2Q q m + p2Q q (n - m) = p2Q q n iff
    2^p2Q q m q^n < 2^p2Q q n q^m. -/
theorem mem_splitOrdersQ_iff (hq : 3 ≤ q) {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m < n) :
    m ∈ splitOrdersQ q n ↔ 2 ^ p2Q q m * q ^ n < 2 ^ p2Q q n * q ^ m := by
  simp only [splitOrdersQ, Finset.mem_filter, Finset.mem_Ico]
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have e : 2 ^ p2Q q m * q ^ (m + k) = (2 ^ p2Q q m * q ^ k) * q ^ m := by ring
  rw [e, Nat.mul_lt_mul_right (pow_pos (by omega) _)]
  have hb1 := one_le_p2Q q k
  have ha1 := one_le_p2Q q m
  have h3a := p2Q_spec hq m
  have h3b := p2Q_spec hq k
  have hla := p2Q_spec_lower hq m
  have hlb := p2Q_spec_lower hq k
  have hL := p2Q_spec hq (m + k)
  have hup : p2Q q (m + k) ≤ p2Q q m + p2Q q k :=
    (q_pow_lt_two_pow_iff hq).mp (by
      rw [pow_add, pow_add]
      exact mul_lt_mul'' h3a h3b (by positivity) (by positivity))
  have hlow : p2Q q m + p2Q q k - 2 < p2Q q (m + k) := by
    have : 2 ^ (p2Q q m + p2Q q k - 2) < 2 ^ p2Q q (m + k) :=
      calc 2 ^ (p2Q q m + p2Q q k - 2) = 2 ^ (p2Q q m - 1) * 2 ^ (p2Q q k - 1) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ q ^ m * q ^ k := Nat.mul_le_mul hla hlb
        _ = q ^ (m + k) := (pow_add _ _ _).symm
        _ < 2 ^ p2Q q (m + k) := hL
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  constructor
  · rintro ⟨_, h⟩
    rw [← h, pow_add]
    exact Nat.mul_lt_mul_of_pos_left h3b (by positivity)
  · intro h
    refine ⟨⟨hm1, by omega⟩, ?_⟩
    by_contra hne
    have hL' : p2Q q (m + k) = p2Q q m + (p2Q q k - 1) := by omega
    rw [hL', pow_add] at h
    exact absurd h (not_lt.2 (Nat.mul_le_mul_left _ hlb))

/-- For q = 3 the identity is `choose_p2_eq_split`. -/
example (n : ℕ) : (p2Q 3 n).choose n = p2Q 3 n * (admSetQ 3 n).card +
    ∑ m ∈ splitOrdersQ 3 n, (admSetQ 3 m).card * (p2Q 3 (n - m)).choose (n - m) :=
  choose_p2Q_eq_split (by decide) le_rfl n

end AcceleratedCollatz
