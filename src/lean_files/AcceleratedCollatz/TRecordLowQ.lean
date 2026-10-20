-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TWordQ

/-!
  Record lows of the words of the q-family. A strict record-low time m of a word s: the
  level after its first m letters is below every earlier level (`IsRecordLowQ`).
  Appending an admissible block to a word whose level ends at its minimum adds exactly
  one record low, at the block's end (`isRecordLowQ_append`). So for
  1 :: (B1 ++ ... ++ Bm) with admissible Bi, of any Orders, the record-low times are
  exactly the cut positions 1 + |B1 ... Bi| (`isRecordLowQ_iff_cut`): the blocks of an
  admissible word are cut at its record lows.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- m is a strict record-low time of s: the level after m letters is below every
    earlier level. -/
def IsRecordLowQ (q : ℕ) (s : List Bool) (m : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ s.length ∧
    ∀ j, 1 ≤ j → j < m → seqProductQ q (s.take m) < seqProductQ q (s.take j)

/-- The level at the end of w is at most every level along w. -/
def EndIsMinQ (q : ℕ) (w : List Bool) : Prop :=
  ∀ j, 1 ≤ j → j ≤ w.length → seqProductQ q w ≤ seqProductQ q (w.take j)

/-- Inside an appended admissible block the level stays above the block's start. -/
theorem seqProductQ_lt_inside (hq0 : 0 < q) (w b : List Bool) (r : ℕ)
    (hb : AdmissibleQ q b) (hr1 : 1 ≤ r) (hr : r < b.length) :
    seqProductQ q w < seqProductQ q ((w ++ b).take (w.length + r)) := by
  rw [List.take_length_add_append, seqProductQ_append]
  exact lt_mul_of_one_lt_right (seqProductQ_pos hq0 w) (hb.prefix_gt r hr1 hr)

/-- At the end of an appended admissible block the level is below the block's start. -/
theorem seqProductQ_append_lt (hq0 : 0 < q) (w b : List Bool) (hb : AdmissibleQ q b) :
    seqProductQ q (w ++ b) < seqProductQ q w := by
  rw [seqProductQ_append]
  exact mul_lt_of_lt_one_right (seqProductQ_pos hq0 w) hb.lt_one

/-- After an appended admissible block, the level ends at its minimum again. -/
theorem endIsMinQ_append (hq0 : 0 < q) (w b : List Bool) (hQ : EndIsMinQ q w)
    (hb : AdmissibleQ q b) : EndIsMinQ q (w ++ b) := by
  intro j hj1 hj
  rw [List.length_append] at hj
  have hend := seqProductQ_append_lt hq0 w b hb
  rcases Nat.lt_or_ge w.length j with hgt | hle
  · rcases Nat.lt_or_ge j (w.length + b.length) with hlt | hge
    · obtain ⟨r, rfl⟩ : ∃ r, j = w.length + r := ⟨j - w.length, by omega⟩
      have h := seqProductQ_lt_inside hq0 w b r hb (by omega) (by omega)
      linarith
    · have hj' : j = (w ++ b).length := by
        rw [List.length_append]
        omega
      rw [hj', List.take_length]
  · rw [List.take_append_of_le_length hle]
    linarith [hQ j hj1 hle]

/-- Appending an admissible block adds exactly one record low, at its end. -/
theorem isRecordLowQ_append (hq0 : 0 < q) (w b : List Bool) (hw : w ≠ [])
    (hQ : EndIsMinQ q w) (hb : AdmissibleQ q b) (m : ℕ) :
    IsRecordLowQ q (w ++ b) m ↔ IsRecordLowQ q w m ∨ m = w.length + b.length := by
  have hwpos : 1 ≤ w.length := List.length_pos_iff.mpr hw
  have hend := seqProductQ_append_lt hq0 w b hb
  constructor
  · rintro ⟨hm1, hmle, hlow⟩
    rw [List.length_append] at hmle
    rcases Nat.lt_or_ge w.length m with hgt | hle
    · right
      by_contra hne
      obtain ⟨r, rfl⟩ : ∃ r, m = w.length + r := ⟨m - w.length, by omega⟩
      have h1 := hlow w.length hwpos hgt
      rw [List.take_append_of_le_length le_rfl, List.take_length] at h1
      have h2 := seqProductQ_lt_inside hq0 w b r hb (by omega) (by omega)
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
        have h := seqProductQ_lt_inside hq0 w b r hb (by omega) (by omega)
        linarith
      · rw [List.take_append_of_le_length hle]
        linarith [hQ j hj1 hle]

/-- Record lows of w followed by admissible blocks: those of w, and the block ends. -/
theorem isRecordLowQ_append_flatten (hq0 : 0 < q) (cs : List (List Bool))
    (hcs : ∀ c ∈ cs, AdmissibleQ q c) :
    ∀ w : List Bool, w ≠ [] → EndIsMinQ q w → ∀ m,
      (IsRecordLowQ q (w ++ cs.flatten) m ↔
        IsRecordLowQ q w m ∨
          ∃ i, 1 ≤ i ∧ i ≤ cs.length ∧ m = w.length + (cs.take i).flatten.length) := by
  induction cs with
  | nil =>
    intro w _ _ m
    simp
  | cons c cs ih =>
    intro w hw hQ m
    have hc : AdmissibleQ q c := hcs c List.mem_cons_self
    have hcs' : ∀ c' ∈ cs, AdmissibleQ q c' := fun c' h => hcs c' (List.mem_cons_of_mem c h)
    have hwc : w ++ c ≠ [] := by
      simp [hw]
    rw [List.flatten_cons, ← List.append_assoc,
      ih hcs' (w ++ c) hwc (endIsMinQ_append hq0 w c hQ hc) m,
      isRecordLowQ_append hq0 w c hw hQ hc m]
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
theorem isRecordLowQ_single (q m : ℕ) : IsRecordLowQ q [true] m ↔ m = 1 := by
  constructor
  · rintro ⟨hm1, hm, _⟩
    simp at hm
    omega
  · rintro rfl
    refine ⟨le_rfl, by simp, ?_⟩
    intro j hj1 hj
    omega

/-- [1] ends at its minimum level. -/
theorem endIsMinQ_single (q : ℕ) : EndIsMinQ q [true] := by
  intro j hj1 hj
  simp at hj
  have hj' : j = 1 := by
    omega
  rw [hj']
  rfl

/-- The record-low times of 1 :: (B1 ++ ... ++ Bm), with admissible Bi, are the cuts. -/
theorem isRecordLowQ_iff_cut (hq0 : 0 < q) (cs : List (List Bool))
    (hcs : ∀ c ∈ cs, AdmissibleQ q c) (m : ℕ) :
    IsRecordLowQ q (true :: cs.flatten) m ↔
      ∃ i, i ≤ cs.length ∧ m = 1 + (cs.take i).flatten.length := by
  have h := isRecordLowQ_append_flatten hq0 cs hcs [true] (by simp) (endIsMinQ_single q) m
  rw [List.singleton_append] at h
  rw [h, isRecordLowQ_single]
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

/-- `IsRecordLowQ` is decidable. -/
instance (q : ℕ) (s : List Bool) (m : ℕ) : Decidable (IsRecordLowQ q s m) := by
  unfold IsRecordLowQ
  infer_instance

end AcceleratedCollatz
