-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSubwordSuffix
import AcceleratedCollatz.TBlockRecord
import AcceleratedCollatz.TSplitGrammar

/-!
  The cycle lemma at the record Orders, and the cyclic subword counts.

  At an upper record Order n, every word of length p2(n) with n ones has exactly one
  admissible rotation: the one that starts at its last lowest point
  (`exists_admissible_rotate`; at most one at every Order, `not_admissible_rotate`). So
  p2(n) a(n) = C(p2(n), n) (`p2_mul_card_admSet`, M. Winkler's upper bound, attained). At a
  lower record Order n, every word of length p2(n) - 1 with n ones has exactly one persistent
  rotation (`exists_persistent_rotate`, at every Order; `not_persistent_rotate`), and these
  are the admissible words of Order n without their last 0, so
  (p2(n) - 1) a(n) = C(p2(n) - 1, n) (`pred_p2_mul_card_admSet`).

  Counted cyclically (`cycOcc`), a subword s ≠ [] with |s| ≤ L then occurs
  C(L - |s|, n - order s) times in all these words together, L = p2(n) resp. p2(n) - 1
  (`sum_cycOcc_admSet`, `sum_cycOcc_persLen`). The plain count is the cyclic one less the
  occurrences across the end, `cross s w w` (`cycOcc_eq`): so at an upper record Order
  occ(n) + Σ_w cross s w w = C(p2(n) - |s|, n - order s) (`occAdm_add_wrap_of_upperRecord`),
  and at a lower record Order the same for the words without their last 0, with the
  occurrences that last 0 adds (`occAdm_add_wrap_of_lowerRecord`).
-/

namespace AcceleratedCollatz

/-! ## Stretches against the whole word -/

/-- At an upper record Order n: a stretch of 1 ≤ b < p2(n) letters with a ≤ n ones whose
    level 3^a / 2^b is below 1 is below 3^n / 2^p2(n). -/
theorem upper_seg {n : ℕ} (hn : 1 ≤ n) (hR : UpperRecord n) {a b : ℕ} (ha : a ≤ n)
    (hb1 : 1 ≤ b) (hbL : b < p2_of n) (hlt : 3 ^ a < 2 ^ b) :
    3 ^ a * 2 ^ p2_of n < 3 ^ n * 2 ^ b := by
  have hlow := p2_of_spec_lower n
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    have h1 := two_pow_pred_p2_lt n hn
    have h2 : 2 ^ p2_of n = 2 ^ (p2_of n - 1) * 2 := by
      rw [← pow_succ, show p2_of n - 1 + 1 = p2_of n by omega]
    have h3 : 2 ≤ 2 ^ b := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
    rw [pow_zero, one_mul, h2]
    calc 2 ^ (p2_of n - 1) * 2 < 3 ^ n * 2 := by omega
      _ ≤ 3 ^ n * 2 ^ b := Nat.mul_le_mul_left _ h3
  rcases Nat.lt_or_ge a n with han | han
  · have hpb : p2_of a ≤ b := by
      by_contra h
      have h1 : 2 ^ b ≤ 2 ^ (p2_of a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 := p2_of_spec_lower a
      omega
    have hbf := (upperRecord_iff_blockFactor n).mp hR a hapos han
    rw [blockFactor_eq, blockFactor_eq, div_lt_div_iff₀ (by positivity) (by positivity)] at hbf
    have hint : 3 ^ a * 2 ^ p2_of n < 3 ^ n * 2 ^ p2_of a := by exact_mod_cast hbf
    have h2 : 2 ^ p2_of a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hpb
    calc 3 ^ a * 2 ^ p2_of n < 3 ^ n * 2 ^ p2_of a := hint
      _ ≤ 3 ^ n * 2 ^ b := Nat.mul_le_mul_left _ h2
  · have han' : a = n := by omega
    subst han'
    have h1 : 2 ^ b ≤ 2 ^ (p2_of a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- At a lower record Order n: a stretch of b < p2(n) - 1 letters with a ≤ n ones whose
    level 3^a / 2^b is above 1 is above 3^n / 2^(p2(n) - 1). -/
theorem lower_seg {n : ℕ} (hR : LowerRecord n) {a b : ℕ} (ha : a ≤ n)
    (hbL : b < p2_of n - 1) (hgt : 2 ^ b < 3 ^ a) :
    3 ^ n * 2 ^ b < 3 ^ a * 2 ^ (p2_of n - 1) := by
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    have := Nat.one_le_two_pow (n := b)
    rw [pow_zero] at hgt
    omega
  rcases Nat.lt_or_ge a n with han | han
  · have hpb : b ≤ p2_of a - 1 := by
      by_contra h
      have h1 : 2 ^ p2_of a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 := p2_of_spec a
      omega
    have hbf := (lowerRecord_iff_blockFactor n).mp hR a hapos han
    rw [blockFactor_eq, blockFactor_eq, div_lt_div_iff₀ (by positivity) (by positivity)] at hbf
    have hint : 3 ^ n * 2 ^ p2_of a < 3 ^ a * 2 ^ p2_of n := by exact_mod_cast hbf
    have hpa := one_le_p2_of a
    have hpn := one_le_p2_of n
    have e1 : 2 ^ p2_of a = 2 ^ (p2_of a - 1) * 2 := by
      rw [← pow_succ, show p2_of a - 1 + 1 = p2_of a by omega]
    have e2 : 2 ^ p2_of n = 2 ^ (p2_of n - 1) * 2 := by
      rw [← pow_succ, show p2_of n - 1 + 1 = p2_of n by omega]
    rw [e1, e2] at hint
    have hint' : 3 ^ n * 2 ^ (p2_of a - 1) < 3 ^ a * 2 ^ (p2_of n - 1) := by nlinarith
    have h2 : 2 ^ b ≤ 2 ^ (p2_of a - 1) := Nat.pow_le_pow_right (by norm_num) hpb
    calc 3 ^ n * 2 ^ b ≤ 3 ^ n * 2 ^ (p2_of a - 1) := Nat.mul_le_mul_left _ h2
      _ < 3 ^ a * 2 ^ (p2_of n - 1) := hint'
  · have han' : a = n := by omega
    subst han'
    have h2 : 2 ^ b < 2 ^ (p2_of a - 1) := Nat.pow_lt_pow_right (by norm_num) hbL
    exact Nat.mul_lt_mul_of_pos_left h2 (by positivity)

/-- The level of a word as 3^order / 2^length. -/
theorem seqProduct_eq_div (l : List Bool) :
    seqProduct l = (3 : ℚ) ^ order l / 2 ^ l.length := by
  rw [eq_div_iff (by positivity)]
  exact seqProduct_mul_pow l

/-! ## Rotations -/

theorem order_rotate (l : List Bool) (k : ℕ) : order (l.rotate k) = order l := by
  unfold order
  exact ((List.rotate_perm l k).filter id).length_eq

theorem seqProduct_rotate (l : List Bool) (k : ℕ) : seqProduct (l.rotate k) = seqProduct l := by
  rw [seqProduct_eq, seqProduct_eq, order_rotate, List.length_rotate]

theorem order_le_of_infix {x l : List Bool} (h : x <:+: l) : order x ≤ order l := by
  obtain ⟨s, t, rfl⟩ := h
  rw [order_append, order_append]
  omega

/-- The first j letters of the rotation by k ≤ |v|. -/
theorem take_rotate (v : List Bool) {k j : ℕ} (hk : k ≤ v.length) (hj : j ≤ v.length) :
    (v.rotate k).take j =
      if k + j ≤ v.length then (v.drop k).take j else v.drop k ++ v.take (k + j - v.length) := by
  rw [List.rotate_eq_drop_append_take hk]
  split_ifs with h
  · rw [List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  · rw [List.take_append, List.take_of_length_le (by rw [List.length_drop]; omega),
      List.take_take, List.length_drop, min_eq_left (by omega)]
    congr 2
    omega

/-- A word has a last lowest point among its first |v| points. -/
theorem exists_last_min (v : List Bool) (hL : 0 < v.length) :
    ∃ k < v.length, (∀ i < v.length, seqProduct (v.take k) ≤ seqProduct (v.take i)) ∧
      ∀ i, k < i → i < v.length → seqProduct (v.take k) < seqProduct (v.take i) := by
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (Finset.range v.length)
    (fun i => seqProduct (v.take i)) ⟨0, Finset.mem_range.mpr hL⟩
  obtain ⟨k, hkT, hkmax⟩ := Finset.exists_max_image ((Finset.range v.length).filter
    (fun i => seqProduct (v.take i) = seqProduct (v.take i0))) id
    ⟨i0, Finset.mem_filter.mpr ⟨hi0, rfl⟩⟩
  rw [Finset.mem_filter, Finset.mem_range] at hkT
  refine ⟨k, hkT.1, fun i hi => ?_, fun i hki hi => ?_⟩
  · rw [hkT.2]
    exact hmin i (Finset.mem_range.mpr hi)
  · rw [hkT.2]
    rcases (hmin i (Finset.mem_range.mpr hi)).lt_or_eq with h | h
    · exact h
    · exfalso
      have := hkmax i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, h.symm⟩)
      simp only [id] at this
      omega

/-- The level from point i to point k > i of v, as a stretch. -/
theorem seqProduct_take_split (v : List Bool) {i k : ℕ} (hik : i ≤ k) :
    seqProduct (v.take k) = seqProduct (v.take i) * seqProduct ((v.drop i).take (k - i)) := by
  rw [← seqProduct_append, ← List.take_add, Nat.add_sub_cancel' hik]

/-! ## Upper record Orders: exactly one admissible rotation -/

/-- An admissible word has no other admissible rotation. -/
theorem not_admissible_rotate {a : List Bool} (hA : Admissible a) {j : ℕ} (hj0 : 0 < j)
    (hjL : j < a.length) : ¬ Admissible (a.rotate j) := by
  intro hR
  rw [List.rotate_eq_drop_append_take hjL.le] at hR
  have h1 := hA.prefix_gt j hj0 hjL
  have h2 := hR.prefix_gt (a.drop j).length (by rw [List.length_drop]; omega)
    (by simp; omega)
  rw [List.take_left] at h2
  have h3 := hA.lt_one
  rw [← List.take_append_drop j a, seqProduct_append] at h3
  nlinarith

/-- At an upper record Order n, every word of length p2(n) with n ones has an admissible
    rotation: the one from its last lowest point. -/
theorem exists_admissible_rotate {n : ℕ} (hn : 1 ≤ n) (hR : UpperRecord n) (v : List Bool)
    (hl : v.length = p2_of n) (ho : order v = n) : ∃ k < v.length, Admissible (v.rotate k) := by
  have hL : 0 < v.length := by have := one_le_p2_of n; omega
  obtain ⟨k, hkL, hge, hgt⟩ := exists_last_min v hL
  have hpos : ∀ l : List Bool, 0 < seqProduct l := seqProduct_pos
  -- every earlier point i lies above the last lowest point by more than the whole word
  have hseg : ∀ i < k, seqProduct (v.take k) < seqProduct v * seqProduct (v.take i) := by
    intro i hik
    set x := (v.drop i).take (k - i) with hx
    have hsplit := seqProduct_take_split v hik.le
    rw [← hx] at hsplit
    have hxl : x.length = k - i := by rw [hx, List.length_take, List.length_drop]; omega
    have hx1 : seqProduct x < 1 := by
      have hle : seqProduct x ≤ 1 := by
        have := hge i (by omega)
        rw [hsplit] at this
        have hp := hpos (v.take i)
        nlinarith
      have hne : seqProduct x ≠ 1 := seqProduct_ne_one x (by
        intro h
        rw [h] at hxl
        simp at hxl
        omega)
      exact lt_of_le_of_ne hle hne
    have hox : order x ≤ n := by
      rw [← ho]
      exact order_le_of_infix ((List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix)
    have hint := upper_seg hn hR hox (by omega) (by omega) ((seqProduct_lt_one_iff x).mp hx1)
    have hxv : seqProduct x < seqProduct v := by
      rw [seqProduct_eq_div x, seqProduct_eq_div v, hl, ho,
        div_lt_div_iff₀ (by positivity) (by positivity)]
      exact_mod_cast hint
    rw [hsplit, mul_comm (seqProduct v)]
    exact mul_lt_mul_of_pos_left hxv (hpos _)
  have hvk : seqProduct v = seqProduct (v.take k) * seqProduct (v.drop k) := by
    rw [← seqProduct_append, List.take_append_drop]
  refine ⟨k, hkL, ⟨fun j hj1 hjL => ?_, ?_⟩⟩
  · rw [List.length_rotate] at hjL
    rw [take_rotate v hkL.le hjL.le]
    split_ifs with hkj
    · have h1 := seqProduct_take_split v (show k ≤ k + j by omega)
      rw [Nat.add_sub_cancel_left] at h1
      rcases Nat.lt_or_ge (k + j) v.length with hlt | hge'
      · have h2 := hgt (k + j) (by omega) hlt
        rw [h1] at h2
        have hp := hpos (v.take k)
        nlinarith
      · have hkj' : k + j = v.length := by omega
        rw [hkj', List.take_length] at h1
        have h0 := hseg 0 (by omega)
        rw [List.take_zero, show seqProduct [] = 1 from rfl, mul_one] at h0
        rw [List.take_of_length_le (by rw [List.length_drop]; omega)]
        rw [hvk] at h0
        have hp := hpos (v.take k)
        nlinarith
    · rw [seqProduct_append]
      have h0 := hseg (k + j - v.length) (by omega)
      rw [hvk] at h0
      have hp := hpos (v.take k)
      nlinarith
  · rw [seqProduct_rotate, seqProduct_lt_one_iff, hl, ho]
    exact p2_of_spec n

/-! ## Lower record Orders: exactly one persistent rotation -/

/-- At a lower record Order n, a persistent word of length p2(n) - 1 with n ones has no
    other persistent rotation. -/
theorem not_persistent_rotate {n : ℕ} (hR : LowerRecord n) {a : List Bool}
    (hP : Persistent a) (hl : a.length = p2_of n - 1) (ho : order a = n) {j : ℕ}
    (hj0 : 0 < j) (hjL : j < a.length) : ¬ Persistent (a.rotate j) := by
  intro hR'
  rw [List.rotate_eq_drop_append_take hjL.le] at hR'
  have h1 := hP j hj0 hjL.le
  have h2 := hR' (a.drop j).length (by rw [List.length_drop]; omega) (by simp)
  rw [List.take_left] at h2
  have hx := (one_lt_seqProduct_iff _).mp h1
  have hox : order (a.take j) ≤ n := by rw [← ho]; exact order_take_le a j
  have hint := lower_seg hR hox (by rw [List.length_take]; omega) hx
  have hxa : seqProduct a < seqProduct (a.take j) := by
    rw [seqProduct_eq_div (a.take j), seqProduct_eq_div a, hl, ho,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast hint
  have hsplit : seqProduct a = seqProduct (a.take j) * seqProduct (a.drop j) := by
    rw [← seqProduct_append, List.take_append_drop]
  rw [hsplit] at hxa
  have hp := seqProduct_pos (a.take j)
  nlinarith

/-- Every word of length p2(n) - 1 with n ≥ 1 ones has a persistent rotation: the one from
    its last lowest point. -/
theorem exists_persistent_rotate {n : ℕ} (hn : 1 ≤ n) (v : List Bool)
    (hl : v.length = p2_of n - 1) (ho : order v = n) :
    ∃ k < v.length, Persistent (v.rotate k) := by
  have hp2 : 2 ≤ p2_of n := by
    have := p2_of_mono hn
    have := p2_of_lt_succ 0
    have := one_le_p2_of 0
    simp only [zero_add] at *
    omega
  have hL : 0 < v.length := by omega
  obtain ⟨k, hkL, hge, hgt⟩ := exists_last_min v hL
  have hpos : ∀ l : List Bool, 0 < seqProduct l := seqProduct_pos
  have hv1 : 1 < seqProduct v := by
    rw [one_lt_seqProduct_iff, hl, ho]
    exact two_pow_pred_p2_lt n hn
  have hvk : seqProduct v = seqProduct (v.take k) * seqProduct (v.drop k) := by
    rw [← seqProduct_append, List.take_append_drop]
  refine ⟨k, hkL, fun j hj1 hjL => ?_⟩
  rw [List.length_rotate] at hjL
  rw [take_rotate v hkL.le hjL]
  split_ifs with hkj
  · have h1 := seqProduct_take_split v (show k ≤ k + j by omega)
    rw [Nat.add_sub_cancel_left] at h1
    rcases Nat.lt_or_ge (k + j) v.length with hlt | hge'
    · have h2 := hgt (k + j) (by omega) hlt
      rw [h1] at h2
      have hp := hpos (v.take k)
      nlinarith
    · have hkj' : k + j = v.length := by omega
      rw [hkj', List.take_length] at h1
      rw [List.take_of_length_le (by rw [List.length_drop]; omega)]
      have h3 := hge 0 hL
      rw [List.take_zero, show seqProduct [] = 1 from rfl] at h3
      rw [hvk] at hv1
      have hp := hpos (v.take k)
      nlinarith
  · rw [seqProduct_append]
    have h0 := hge (k + j - v.length) (by omega)
    rw [hvk] at hv1
    have hp := hpos (v.take k)
    have hp' := hpos (v.drop k)
    nlinarith

/-! ## Counting through the rotations -/

/-- A sum over the words of length L > 0 and Order n, as a sum over a set A that holds
    exactly one rotation of each word, and its rotations. -/
theorem sum_wordSet_rotations {L n : ℕ} (hL : 0 < L) (A : Finset (List Bool))
    (hA : ∀ a ∈ A, a ∈ wordSet L n) (hex : ∀ v ∈ wordSet L n, ∃ k < L, v.rotate k ∈ A)
    (huniq : ∀ a ∈ A, ∀ j, 0 < j → j < L → a.rotate j ∉ A) (f : List Bool → ℕ) :
    ∑ v ∈ wordSet L n, f v = ∑ a ∈ A, ∑ k ∈ Finset.range L, f (a.rotate k) := by
  have hlen : ∀ a ∈ A, a.length = L := fun a ha => ((mem_wordSet _ _ _).mp (hA a ha)).1
  have himg : (A ×ˢ Finset.range L).image (fun p => p.1.rotate p.2) = wordSet L n := by
    ext v
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · rintro ⟨a, k, ⟨ha, -⟩, rfl⟩
      obtain ⟨hl, ho⟩ := (mem_wordSet _ _ _).mp (hA a ha)
      rw [mem_wordSet, List.length_rotate, order_rotate]
      exact ⟨hl, ho⟩
    · intro hv
      obtain ⟨k, hk, hka⟩ := hex v hv
      have hvl := ((mem_wordSet _ _ _).mp hv).1
      refine ⟨v.rotate k, (L - k) % L, ⟨hka, Nat.mod_lt _ hL⟩, ?_⟩
      have e : (L - k) % L = (L - k) % (v.rotate k).length := by rw [List.length_rotate, hvl]
      rw [e, List.rotate_mod, List.rotate_rotate, show k + (L - k) = v.length by omega,
        List.rotate_length]
  have hinj : Set.InjOn (fun p : List Bool × ℕ => p.1.rotate p.2)
      ↑(A ×ˢ Finset.range L) := by
    rintro ⟨a, k⟩ hp ⟨a', k'⟩ hq h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hq h
    have ha' : a' = a.rotate ((k + (L - k')) % L) := by
      have e : (k + (L - k')) % L = (k + (L - k')) % a.length := by rw [hlen a hp.1]
      rw [e, List.rotate_mod, ← List.rotate_rotate, h, List.rotate_rotate,
        show k' + (L - k') = a'.length by rw [hlen a' hq.1]; omega, List.rotate_length]
    have hj : (k + (L - k')) % L = 0 := by
      by_contra hj
      have := huniq a hp.1 _ (Nat.pos_of_ne_zero hj) (Nat.mod_lt _ hL)
      rw [← ha'] at this
      exact this hq.1
    have hkk : k = k' := by
      rcases Nat.lt_or_ge k k' with hlt | hge
      · rw [Nat.mod_eq_of_lt (by omega)] at hj
        omega
      · rw [show k + (L - k') = (k - k') + L by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)] at hj
        omega
    rw [hj, List.rotate_zero] at ha'
    rw [ha', hkk]
  rw [← himg, Finset.sum_image hinj, Finset.sum_product]

/-- Occurrences of s around the cycle of w: the rotations of w that start with s. -/
def cycOcc (s w : List Bool) : ℕ :=
  ((Finset.range w.length).filter (fun i => s <+: w.rotate i)).card

/-- Counted around the cycle, s ≠ [] with |s| ≤ L occurs C(L - |s|, n - order s) times in a
    set that holds exactly one rotation of each word of length L and Order n. -/
theorem sum_cycOcc_of_rotations {L n : ℕ} (hL : 0 < L) (A : Finset (List Bool))
    (hA : ∀ a ∈ A, a ∈ wordSet L n) (hex : ∀ v ∈ wordSet L n, ∃ k < L, v.rotate k ∈ A)
    (huniq : ∀ a ∈ A, ∀ j, 0 < j → j < L → a.rotate j ∉ A) (s : List Bool) :
    ∑ a ∈ A, cycOcc s a = pc s L n := by
  have h := sum_wordSet_rotations hL A hA hex huniq (fun v => if s <+: v then 1 else 0)
  rw [← Finset.card_filter, card_filter_prefix] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro a ha
  rw [cycOcc, Finset.card_filter, ((mem_wordSet _ _ _).mp (hA a ha)).1]

/-- In the same way, A holds C(L, n) / L words. -/
theorem card_mul_of_rotations {L n : ℕ} (hL : 0 < L) (A : Finset (List Bool))
    (hA : ∀ a ∈ A, a ∈ wordSet L n) (hex : ∀ v ∈ wordSet L n, ∃ k < L, v.rotate k ∈ A)
    (huniq : ∀ a ∈ A, ∀ j, 0 < j → j < L → a.rotate j ∉ A) :
    A.card * L = L.choose n := by
  have h := sum_wordSet_rotations hL A hA hex huniq (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h
  rw [← card_wordSet, h]

/-- Plain occurrences, position by position. -/
theorem occ_eq_sum (s : List Bool) :
    ∀ w : List Bool, occ s w = ∑ i ∈ Finset.range w.length, if s <+: w.drop i then 1 else 0
  | [] => rfl
  | b :: t => by
    rw [occ, occ_eq_sum s t, List.length_cons, Finset.sum_range_succ']
    simp only [List.drop_succ_cons, List.drop_zero]
    ring

/-- Around the cycle: the plain occurrences and those across the end of w. -/
theorem cycOcc_eq (s w : List Bool) (hsw : s.length ≤ w.length) :
    cycOcc s w = occ s w + cross s w w := by
  set L := w.length
  have hterm : ∀ i ∈ Finset.range L, (if s <+: w.rotate i then 1 else 0) =
      (if s <+: w.drop i then 1 else 0) +
        if L - i < s.length ∧ s.take (L - i) = w.drop i ∧ s.drop (L - i) <+: w.take i
        then 1 else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [List.rotate_eq_drop_append_take hi.le]
    have hiff := prefix_append_iff_cut s (w.drop i) (w.take i)
    rw [List.length_drop] at hiff
    change (s <+: _ ↔ s <+: w.drop i ∨ (L - i < s.length ∧ s.take (L - i) = w.drop i ∧
      s.drop (L - i) <+: w.take i)) at hiff
    by_cases h1 : s <+: w.drop i
    · have hl := h1.length_le
      rw [List.length_drop] at hl
      have h2 : ¬ (L - i < s.length ∧ s.take (L - i) = w.drop i ∧
          s.drop (L - i) <+: w.take i) := fun h => by omega
      simp only [hiff, h1, h2, true_or, ↓reduceIte, add_zero]
    · simp only [hiff, h1, false_or, ↓reduceIte, zero_add]
  rw [cycOcc, Finset.card_filter, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    ← occ_eq_sum]
  congr 1
  -- the occurrences across the end, reindexed by j = L - i = t + 1
  rw [← Finset.sum_range_reflect, cross]
  have hset : Finset.Ioo 0 s.length = (Finset.range (s.length - 1)).image (· + 1) := by
    ext j
    simp only [Finset.mem_Ioo, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      exact ⟨j - 1, by omega, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      omega
  rw [hset, Finset.sum_image (fun _ _ _ _ h => by simpa using h),
    ← Finset.sum_range_add_sum_Ico _ (show s.length - 1 ≤ L by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (s.length - 1) L), add_zero]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    have hsuf : s.take (t + 1) <:+ w ↔ s.take (t + 1) = w.drop (L - 1 - t) := by
      rw [List.suffix_iff_eq_drop, List.length_take, min_eq_left (by omega),
        show L - 1 - t = L - (t + 1) by omega]
    have hpre : s.drop (t + 1) <+: w ↔ s.drop (t + 1) <+: w.take (L - 1 - t) := by
      rw [List.prefix_take_iff, List.length_drop]
      constructor
      · exact fun h => ⟨h, by omega⟩
      · exact fun h => h.1
    simp only [show L - (L - 1 - t) = t + 1 by omega, hsuf, hpre,
      show t + 1 < s.length from by omega, true_and]
  · intro t ht
    rw [Finset.mem_Ico] at ht
    rw [ite_eq_right_iff]
    rintro ⟨h, -⟩
    omega

/-! ## The record Orders -/

/-- At an upper record Order n ≥ 1: p2(n) a(n) = C(p2(n), n). -/
theorem p2_mul_card_admSet {n : ℕ} (hn : 1 ≤ n) (hR : UpperRecord n) :
    (admSet n).card * p2_of n = (p2_of n).choose n := by
  apply card_mul_of_rotations (by have := one_le_p2_of n; omega)
  · intro a ha
    obtain ⟨hA, ho⟩ := (mem_admSet n a).mp ha
    rw [mem_wordSet, admissible_length a hA, ho]
    exact ⟨rfl, rfl⟩
  · intro v hv
    obtain ⟨hl, ho⟩ := (mem_wordSet _ _ _).mp hv
    obtain ⟨k, hk, hA⟩ := exists_admissible_rotate hn hR v hl ho
    exact ⟨k, hl ▸ hk, (mem_admSet n _).mpr ⟨hA, by rw [order_rotate, ho]⟩⟩
  · intro a ha j hj0 hjL hmem
    obtain ⟨hA, ho⟩ := (mem_admSet n a).mp ha
    exact not_admissible_rotate hA hj0 (by rw [admissible_length a hA, ho]; exact hjL)
      ((mem_admSet n _).mp hmem).1

/-- At an upper record Order n ≥ 1, s ≠ [] with |s| ≤ p2(n) occurs C(p2(n) - |s|, n - order s)
    times around the cycles of the admissible words of Order n. -/
theorem sum_cycOcc_admSet {n : ℕ} (hn : 1 ≤ n) (hR : UpperRecord n) (s : List Bool) :
    ∑ a ∈ admSet n, cycOcc s a = pc s (p2_of n) n := by
  apply sum_cycOcc_of_rotations (by have := one_le_p2_of n; omega)
  · intro a ha
    obtain ⟨hA, ho⟩ := (mem_admSet n a).mp ha
    rw [mem_wordSet, admissible_length a hA, ho]
    exact ⟨rfl, rfl⟩
  · intro v hv
    obtain ⟨hl, ho⟩ := (mem_wordSet _ _ _).mp hv
    obtain ⟨k, hk, hA⟩ := exists_admissible_rotate hn hR v hl ho
    exact ⟨k, hl ▸ hk, (mem_admSet n _).mpr ⟨hA, by rw [order_rotate, ho]⟩⟩
  · intro a ha j hj0 hjL hmem
    obtain ⟨hA, ho⟩ := (mem_admSet n a).mp ha
    exact not_admissible_rotate hA hj0 (by rw [admissible_length a hA, ho]; exact hjL)
      ((mem_admSet n _).mp hmem).1

/-- At an upper record Order n ≥ 1, for |s| ≤ p2(n): the plain occurrences of s in the
    admissible words of Order n and those across their ends add up to
    C(p2(n) - |s|, n - order s). -/
theorem occAdm_add_wrap_of_upperRecord {n : ℕ} (hn : 1 ≤ n) (hR : UpperRecord n)
    (s : List Bool) (hsL : s.length ≤ p2_of n) :
    occAdm s n + ∑ a ∈ admSet n, cross s a a = pc s (p2_of n) n := by
  rw [← sum_cycOcc_admSet hn hR s, occAdm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨hA, ho⟩ := (mem_admSet n a).mp ha
  rw [cycOcc_eq s a (by rw [admissible_length a hA, ho]; exact hsL)]

/-- The persistent words of Order n and length p2(n) - 1 hold one rotation of each word of
    that length and Order, at a lower record Order n ≥ 1. -/
theorem persLen_rotations {n : ℕ} (hn : 1 ≤ n) (hR : LowerRecord n) :
    (∀ a ∈ persLen n (p2_of n - 1), a ∈ wordSet (p2_of n - 1) n) ∧
    (∀ v ∈ wordSet (p2_of n - 1) n, ∃ k < p2_of n - 1, v.rotate k ∈ persLen n (p2_of n - 1)) ∧
    (∀ a ∈ persLen n (p2_of n - 1), ∀ j, 0 < j → j < p2_of n - 1 →
      a.rotate j ∉ persLen n (p2_of n - 1)) := by
  refine ⟨fun a ha => ?_, fun v hv => ?_, fun a ha j hj0 hjL hmem => ?_⟩
  · obtain ⟨-, ho, hl⟩ := (mem_persLen _ _ _).mp ha
    exact (mem_wordSet _ _ _).mpr ⟨hl, ho⟩
  · obtain ⟨hl, ho⟩ := (mem_wordSet _ _ _).mp hv
    obtain ⟨k, hk, hP⟩ := exists_persistent_rotate hn v hl ho
    exact ⟨k, hl ▸ hk, (mem_persLen _ _ _).mpr
      ⟨hP, by rw [order_rotate, ho], by rw [List.length_rotate, hl]⟩⟩
  · obtain ⟨hP, ho, hl⟩ := (mem_persLen _ _ _).mp ha
    exact not_persistent_rotate hR hP hl ho hj0 (by rw [hl]; exact hjL)
      ((mem_persLen _ _ _).mp hmem).1

/-- At a lower record Order n ≥ 1: (p2(n) - 1) a(n) = C(p2(n) - 1, n). -/
theorem pred_p2_mul_card_admSet {n : ℕ} (hn : 1 ≤ n) (hR : LowerRecord n) :
    (admSet n).card * (p2_of n - 1) = (p2_of n - 1).choose n := by
  have hp : 0 < p2_of n - 1 := by
    have := p2_of_mono hn
    have := p2_of_lt_succ 0
    have := one_le_p2_of 0
    simp only [zero_add] at *
    omega
  obtain ⟨h1, h2, h3⟩ := persLen_rotations hn hR
  rw [← card_persLen_max]
  exact card_mul_of_rotations hp _ h1 h2 h3

/-- At a lower record Order n ≥ 1, s occurs C(p2(n) - 1 - |s|, n - order s) times around the
    cycles of the admissible words of Order n without their last 0. -/
theorem sum_cycOcc_persLen {n : ℕ} (hn : 1 ≤ n) (hR : LowerRecord n) (s : List Bool) :
    ∑ p ∈ persLen n (p2_of n - 1), cycOcc s p = pc s (p2_of n - 1) n := by
  have hp : 0 < p2_of n - 1 := by
    have := p2_of_mono hn
    have := p2_of_lt_succ 0
    have := one_le_p2_of 0
    simp only [zero_add] at *
    omega
  obtain ⟨h1, h2, h3⟩ := persLen_rotations hn hR
  exact sum_cycOcc_of_rotations hp _ h1 h2 h3 s

/-- At a lower record Order n ≥ 1, for s ≠ [] with |s| ≤ p2(n) - 1: the occurrences of s in
    the admissible words of Order n, from those around the cycles of the words without their
    last 0 (`sum_cycOcc_persLen`): the ones across the end of such a word p leave, and the
    ones the last 0 adds come in. -/
theorem occAdm_add_wrap_of_lowerRecord {n : ℕ} (hn : 1 ≤ n) (hR : LowerRecord n)
    (s : List Bool) (hs : s ≠ []) (hsL : s.length ≤ p2_of n - 1) :
    occAdm s n + ∑ p ∈ persLen n (p2_of n - 1), cross s p p =
      pc s (p2_of n - 1) n +
        ∑ p ∈ persLen n (p2_of n - 1), (occ s [false] + cross s p [false]) := by
  rw [← sum_cycOcc_persLen hn hR s, occAdm, ← image_persLen_max,
    Finset.sum_image (fun _ _ _ _ h => List.append_left_injective [false] h),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨-, -, hl⟩ := (mem_persLen _ _ _).mp hp
  rw [occ_append s hs, cycOcc_eq s p (by rw [hl]; exact hsL)]
  ring

/-! ## Check: Orders 5 (upper record) and 7 (lower record) -/

set_option linter.hashCommand false in
#guard occAdm [false, true] 5 = 8 ∧ (admSet 7).card * 11 = Nat.choose 11 7

end AcceleratedCollatz
