-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TFirstWord
import AcceleratedCollatz.TRecordFloor

/-!
  At a record Order the first word is an upper Christoffel word (paper 3, sec:rhomax;
  Berstel, Lauve, Reutenauer, Saliola, *Combinatorics on Words*, Definition 1.1). The upper
  Christoffel path from (0, 0) to (a, b) stays above the segment between them, closest to
  it: after k steps it stands at height ⌈k b/(a + b)⌉ (`christoffelHeight`), so its k-th step
  is y (`true`) exactly when that height rises (`christoffelUpper`), that is, when
  ⌊i (a + b)/b⌋ = k for some i (`christoffelHeight_lt_iff`). The first word of Order n has
  its odd steps at p2(i) - 1, i < n (`getElem?_firstWord`), and ⌊i P/n⌋ + 1 = p2(i) for the
  fraction P/n of a record Order n (`div_record_add_one`). So its first P letters are the
  upper Christoffel word of slope n/(P - n) (`take_firstWord_recordFrac`): all of it at an
  upper record Order (`firstWord_upperRecord`), all but the final halving at a lower one
  (`firstBody_lowerRecord`). n and P are coprime (`RecordFrac.coprime`), as the definition
  asks of P - n and n (`RecordFrac.coprime_sub`).
-/

namespace AcceleratedCollatz

/-- ⌈k b/(a + b)⌉: the height of the upper Christoffel path from (0, 0) to (a, b) after k
    steps. -/
def christoffelHeight (a b k : ℕ) : ℕ := (k * b + (a + b) - 1) / (a + b)

/-- The upper Christoffel word with a letters x (`false`) and b letters y (`true`): its
    k-th letter is y when the height of the upper path rises at step k. -/
def christoffelUpper (a b : ℕ) : List Bool :=
  (List.range (a + b)).map fun k => decide (christoffelHeight a b k < christoffelHeight a b (k + 1))

/-- ⌈x/P⌉ ≤ i ↔ x ≤ i P. -/
theorem ceilDiv_le_iff {x P i : ℕ} (hP : 0 < P) : (x + P - 1) / P ≤ i ↔ x ≤ i * P := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hP, Nat.succ_mul]
  omega

/-- The height rises at step k exactly when ⌊i (a + b)/b⌋ = k for some i. -/
theorem christoffelHeight_lt_iff {a b k : ℕ} (hb : 0 < b) :
    christoffelHeight a b k < christoffelHeight a b (k + 1) ↔ ∃ i, i * (a + b) / b = k := by
  have hP : 0 < a + b := by omega
  unfold christoffelHeight
  set c := (k * b + (a + b) - 1) / (a + b) with hc
  have hcP : k * b ≤ c * (a + b) := (ceilDiv_le_iff hP).1 le_rfl
  have hiff : ∀ i, (i * (a + b) / b = k ↔ k * b ≤ i * (a + b) ∧ i * (a + b) < (k + 1) * b) := by
    intro i
    rw [Nat.div_eq_iff hb, Nat.succ_mul]
    omega
  constructor
  · intro hlt
    refine ⟨c, (hiff c).2 ⟨hcP, ?_⟩⟩
    by_contra hge
    push Not at hge
    have := (ceilDiv_le_iff hP).2 hge
    omega
  · rintro ⟨i, hi⟩
    obtain ⟨hlo, hhi⟩ := (hiff i).1 hi
    have hci : c ≤ i := (ceilDiv_le_iff hP).2 hlo
    have hlt : i < ((k + 1) * b + (a + b) - 1) / (a + b) := by
      by_contra hge
      push Not at hge
      have := (ceilDiv_le_iff hP).1 hge
      omega
    omega

theorem getElem?_christoffelUpper (a b k : ℕ) : (christoffelUpper a b)[k]? =
    if k < a + b then
      some (decide (christoffelHeight a b k < christoffelHeight a b (k + 1)))
    else none := by
  unfold christoffelUpper
  rw [List.getElem?_map]
  by_cases hk : k < a + b
  · rw [List.getElem?_range hk]
    simp only [hk, ↓reduceIte, Option.map_some]
  · have hnone : (List.range (a + b))[k]? = none := by
      rw [List.getElem?_eq_none_iff, List.length_range]
      omega
    rw [hnone]
    simp only [hk, ↓reduceIte, Option.map_none]

/-- p2 is strictly increasing. -/
theorem p2_of_lt_of_lt {i n : ℕ} (h : i < n) : p2_of i < p2_of n := by
  have hlo := p2_of_spec_lower i
  have hhi := p2_of_spec n
  have hp1 : 1 ≤ p2_of i := by
    unfold p2_of
    omega
  have h3 : 3 ^ (i + 1) ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
  have h2 : 2 ^ p2_of i = 2 * 2 ^ (p2_of i - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp1]
  have : 2 ^ p2_of i < 2 ^ p2_of n := by
    rw [pow_succ] at h3
    omega
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this

/-- The letters of `firstBody n`: odd steps exactly at p2(i) - 1, i < n. -/
theorem getElem?_firstBody (n k : ℕ) : (firstBody n)[k]? =
    if k + 1 < p2_of n then some (decide (∃ i < n, p2_of i = k + 1)) else none := by
  induction n generalizing k with
  | zero =>
    rw [p2_of_zero]
    simp [firstBody]
  | succ n ih =>
    have hlen := length_firstBody n
    have hmono : p2_of n < p2_of (n + 1) := p2_of_lt_of_lt (Nat.lt_succ_self n)
    rw [firstBody_succ]
    rcases Nat.lt_or_ge k (firstBody n).length with hk | hk
    · rw [List.getElem?_append_left hk, ih]
      have hk1 : k + 1 < p2_of n := by omega
      have hk2 : k + 1 < p2_of (n + 1) := by omega
      simp only [hk1, hk2, ↓reduceIte]
      congr 2
      apply propext
      constructor
      · rintro ⟨i, hi, he⟩
        exact ⟨i, by omega, he⟩
      · rintro ⟨i, hi, he⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
        · exact ⟨i, hi', he⟩
        · subst hi'
          omega
    · rw [List.getElem?_append_right hk]
      rcases Nat.eq_or_lt_of_le hk with he | hgt
      · have h0 : k - (firstBody n).length = 0 := by omega
        rw [h0, List.getElem?_cons_zero]
        have hk2 : k + 1 < p2_of (n + 1) := by omega
        simp only [hk2, ↓reduceIte]
        have hex : ∃ i < n + 1, p2_of i = k + 1 := ⟨n, Nat.lt_succ_self n, by omega⟩
        simp only [hex, decide_true]
      · obtain ⟨j, hj⟩ : ∃ j, k - (firstBody n).length = j + 1 :=
          ⟨k - (firstBody n).length - 1, by omega⟩
        rw [hj, List.getElem?_cons_succ, List.getElem?_replicate]
        have hnone : ¬ ∃ i < n + 1, p2_of i = k + 1 := by
          rintro ⟨i, hi, he⟩
          have := p2_of_mono (Nat.lt_succ_iff.1 hi)
          omega
        by_cases hj' : j < p2_of (n + 1) - p2_of n - 1
        · have hk2 : k + 1 < p2_of (n + 1) := by omega
          simp only [hj', hk2, ↓reduceIte, hnone, decide_false]
        · have hk2 : ¬ k + 1 < p2_of (n + 1) := by omega
          simp only [hj', hk2, ↓reduceIte]

/-- The letters of `firstWord n`: odd steps exactly at p2(i) - 1, i < n. -/
theorem getElem?_firstWord (n k : ℕ) : (firstWord n)[k]? =
    if k < p2_of n then some (decide (∃ i < n, p2_of i = k + 1)) else none := by
  have hlen := length_firstBody n
  unfold firstWord
  rcases Nat.lt_or_ge k (firstBody n).length with hk | hk
  · have h1 : k + 1 < p2_of n := by omega
    have h2 : k < p2_of n := by omega
    rw [List.getElem?_append_left hk, getElem?_firstBody]
    simp only [h1, h2, ↓reduceIte]
  · rw [List.getElem?_append_right hk]
    rcases Nat.eq_or_lt_of_le hk with he | hgt
    · have h0 : k - (firstBody n).length = 0 := by omega
      have h2 : k < p2_of n := by omega
      rw [h0, List.getElem?_cons_zero]
      have hnone : ¬ ∃ i < n, p2_of i = k + 1 := by
        rintro ⟨i, hi, he'⟩
        have := p2_of_lt_of_lt hi
        omega
      simp only [h2, ↓reduceIte, hnone, decide_false]
    · have h2 : ¬ k < p2_of n := by omega
      simp only [h2, ↓reduceIte, List.getElem?_eq_none_iff, List.length_singleton]
      omega

/-- n < p2(n): the Order is below the length of its words. -/
theorem self_lt_p2_of (n : ℕ) : n < p2_of n := by
  have h1 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h2 := p2_of_spec n
  exact (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 (by omega)

/-- The fraction P/n of a record Order n is in lowest terms: a common factor would make
    Q/g an Order below Q with ⌊(Q/g) P/Q⌋ exact. -/
theorem RecordFrac.coprime {P Q : ℕ} (h : RecordFrac P Q) : Nat.Coprime Q P := by
  have hQ1 := h.1
  by_contra hcop
  set g := Nat.gcd Q P with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left P (by omega)
  have hg2 : 2 ≤ g := by
    unfold Nat.Coprime at hcop
    omega
  have hgQ : g ∣ Q := Nat.gcd_dvd_left Q P
  have hgP : g ∣ P := Nat.gcd_dvd_right Q P
  obtain ⟨u, hu⟩ := hgQ
  obtain ⟨v, hv⟩ := hgP
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0, Nat.mul_zero] at hu
      omega
    · exact h0
  have huQ : u < Q := by
    rw [hu]
    calc u = 1 * u := (Nat.one_mul u).symm
      _ < g * u := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  obtain ⟨hlo, hhi⟩ := record_mul_bounds h hu1 huQ
  have hprod : u * P = Q * v := by
    rw [hu, hv]
    ring
  rw [hprod, Nat.mul_comm (p2_of u - 1) Q] at hlo
  rw [hprod, Nat.mul_comm (p2_of u) Q] at hhi
  have h1 := Nat.lt_of_mul_lt_mul_left hlo
  have h2 := Nat.lt_of_mul_lt_mul_left hhi
  omega

/-- P - n and n are coprime: the slope n/(P - n) in lowest terms. -/
theorem RecordFrac.coprime_sub {P Q : ℕ} (h : RecordFrac P Q) : Nat.Coprime (P - Q) Q := by
  have hle : Q ≤ P := by
    have := recordFrac_bounds h
    have := self_lt_p2_of Q
    omega
  rw [Nat.coprime_sub_self_left hle]
  exact (RecordFrac.coprime h).symm

/-- At a record Order n with fraction P/n, the first P letters of the first word are the
    upper Christoffel word of slope n/(P - n). -/
theorem take_firstWord_recordFrac {P n : ℕ} (h : RecordFrac P n) :
    (firstWord n).take P = christoffelUpper (P - n) n := by
  have hn1 := h.1
  have hbP := recordFrac_bounds h
  have hnp := self_lt_p2_of n
  have hnP : n ≤ P := by omega
  have hsum : P - n + n = P := Nat.sub_add_cancel hnP
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, getElem?_christoffelUpper, hsum]
  by_cases hk : k < P
  · have hk' : k < p2_of n := by omega
    rw [getElem?_firstWord]
    simp only [hk, hk', ↓reduceIte]
    congr 2
    apply propext
    rw [christoffelHeight_lt_iff (by omega), hsum]
    constructor
    · rintro ⟨i, hi, he⟩
      refine ⟨i, ?_⟩
      rcases Nat.eq_zero_or_pos i with h0 | hi1
      · subst h0
        rw [p2_of_zero] at he
        simp only [Nat.zero_mul, Nat.zero_div]
        omega
      · have := div_record_add_one h hi1 hi
        omega
    · rintro ⟨i, hi⟩
      have hin : i < n := by
        have hlt : i * P / n < P := by omega
        rw [Nat.div_lt_iff_lt_mul (by omega)] at hlt
        exact Nat.lt_of_mul_lt_mul_right (a := P) (by linarith)
      refine ⟨i, hin, ?_⟩
      rcases Nat.eq_zero_or_pos i with h0 | hi1
      · subst h0
        rw [p2_of_zero]
        simp only [Nat.zero_mul, Nat.zero_div] at hi
        omega
      · have := div_record_add_one h hi1 hin
        omega
  · simp only [hk, ↓reduceIte]

/-- At an upper record Order n the first word is the upper Christoffel word of slope
    n/(p2(n) - n). -/
theorem firstWord_upperRecord {n : ℕ} (hn : 1 ≤ n) (hR : UpperRecord n) :
    firstWord n = christoffelUpper (p2_of n - n) n := by
  rw [← take_firstWord_recordFrac (P := p2_of n) ⟨hn, Or.inl ⟨hR, rfl⟩⟩]
  rw [List.take_of_length_le (by rw [length_firstWord])]

/-- At a lower record Order n the first word without its final halving is the upper
    Christoffel word of slope n/(p2(n) - 1 - n). -/
theorem firstBody_lowerRecord {n : ℕ} (hn : 1 ≤ n) (hR : LowerRecord n) :
    firstBody n = christoffelUpper (p2_of n - 1 - n) n := by
  rw [← take_firstWord_recordFrac (P := p2_of n - 1) ⟨hn, Or.inr ⟨hR, rfl⟩⟩]
  have hlen := length_firstBody n
  unfold firstWord
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

end AcceleratedCollatz
