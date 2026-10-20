-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TVectorLex

/-!
  The point of a word: the word read as a path down the Stern-Brocot tree from 1/1, a 1
  to the right and a 0 to the left (`sbPoint`; high to low in K. Ryde, Trees of
  Rationals: the right subtree is y + 1 and the left one y/(y + 1) for every point y of
  the tree). A run of a 1s in front of a word adds a, a run of b 0s maps y to
  1/(b + 1/y) (`sbPoint_replicate_true_append`, `sbPoint_replicate_false_append`), so
  the runs of the word are the quotients of the continued fraction of its point
  (`sbPoint_runs`), the last run counted with 1 more (`sbPoint_replicate_true`,
  `sbPoint_replicate_false`). In a marked vector an entry v is a quotient v followed by a
  quotient 1 + w, where -w is the next entry if that is negative and w = 0 otherwise
  (`sbPoint_expandEntry_natCast`, `sbPoint_expandEntry_neg_natCast`). The points are in
  the in-order of the tree: every word that continues u with a 0 lies below u, every
  word that continues u with a 1 above it (`sbPoint_append_false_lt`,
  `sbPoint_lt_append_true`). So admissible words, of any Orders, are sorted like their
  points (`sbPoint_lt_iff_lt`).
-/

namespace AcceleratedCollatz

/-- The point of a word on the Stern-Brocot tree: 1 for the empty word; a 1 in front maps
    y to y + 1, a 0 in front maps y to y/(y + 1). -/
def sbPoint : List Bool → ℚ
  | [] => 1
  | true :: s => sbPoint s + 1
  | false :: s => sbPoint s / (sbPoint s + 1)

theorem sbPoint_nil : sbPoint [] = 1 := rfl

theorem sbPoint_true_cons (s : List Bool) : sbPoint (true :: s) = sbPoint s + 1 := rfl

theorem sbPoint_false_cons (s : List Bool) :
    sbPoint (false :: s) = sbPoint s / (sbPoint s + 1) := rfl

theorem sbPoint_pos (s : List Bool) : 0 < sbPoint s := by
  induction s with
  | nil =>
    rw [sbPoint_nil]
    exact one_pos
  | cons b s ih =>
    cases b
    · rw [sbPoint_false_cons]
      exact div_pos ih (by linarith)
    · rw [sbPoint_true_cons]
      linarith

/-- A word that starts with a 0 has its point below 1. -/
theorem sbPoint_false_lt_one (s : List Bool) : sbPoint (false :: s) < 1 := by
  have h := sbPoint_pos s
  rw [sbPoint_false_cons, div_lt_iff₀ (by linarith)]
  linarith

/-- A word that starts with a 1 has its point above 1. -/
theorem one_lt_sbPoint_true (s : List Bool) : 1 < sbPoint (true :: s) := by
  have h := sbPoint_pos s
  rw [sbPoint_true_cons]
  linarith

/-- A common first letter keeps the order of two points. -/
theorem sbPoint_cons_lt_iff (b : Bool) (s t : List Bool) :
    sbPoint (b :: s) < sbPoint (b :: t) ↔ sbPoint s < sbPoint t := by
  have hs := sbPoint_pos s
  have ht := sbPoint_pos t
  cases b
  · rw [sbPoint_false_cons, sbPoint_false_cons, div_lt_div_iff₀ (by linarith) (by linarith)]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  · rw [sbPoint_true_cons, sbPoint_true_cons]
    exact add_lt_add_iff_right 1

/-- A common prefix keeps the order of two points. -/
theorem sbPoint_append_lt_iff (u s t : List Bool) :
    sbPoint (u ++ s) < sbPoint (u ++ t) ↔ sbPoint s < sbPoint t := by
  induction u with
  | nil =>
    rfl
  | cons b u ih =>
    rw [List.cons_append, List.cons_append, sbPoint_cons_lt_iff, ih]

/-- In-order, to the left: a word that continues u with a 0 has its point below that of
    u. -/
theorem sbPoint_append_false_lt (u v : List Bool) : sbPoint (u ++ false :: v) < sbPoint u := by
  have h1 : sbPoint (false :: v) < sbPoint [] := sbPoint_false_lt_one v
  have h := (sbPoint_append_lt_iff u (false :: v) []).mpr h1
  rw [List.append_nil] at h
  exact h

/-- In-order, to the right: a word that continues u with a 1 has its point above that of
    u. -/
theorem sbPoint_lt_append_true (u w : List Bool) : sbPoint u < sbPoint (u ++ true :: w) := by
  have h1 : sbPoint [] < sbPoint (true :: w) := one_lt_sbPoint_true w
  have h := (sbPoint_append_lt_iff u [] (true :: w)).mpr h1
  rw [List.append_nil] at h
  exact h

/-- Two words that part at a first place: the one with the 0 there has the lower point. -/
theorem sbPoint_split_lt (u v w : List Bool) :
    sbPoint (u ++ false :: v) < sbPoint (u ++ true :: w) :=
  lt_trans (sbPoint_append_false_lt u v) (sbPoint_lt_append_true u w)

/-- Of two words one is a prefix of the other, or they part at a first place. -/
theorem prefix_or_split (s t : List Bool) :
    s <+: t ∨ t <+: s ∨ (∃ u v w, s = u ++ false :: v ∧ t = u ++ true :: w) ∨
      ∃ u v w, s = u ++ true :: v ∧ t = u ++ false :: w := by
  induction s generalizing t with
  | nil =>
    exact Or.inl List.nil_prefix
  | cons a s ih =>
    cases t with
    | nil =>
      exact Or.inr (Or.inl List.nil_prefix)
    | cons b t =>
      by_cases hab : a = b
      · subst hab
        rcases ih t with h | h | ⟨u, v, w, hs, ht⟩ | ⟨u, v, w, hs, ht⟩
        · exact Or.inl ((List.prefix_cons_inj a).mpr h)
        · exact Or.inr (Or.inl ((List.prefix_cons_inj a).mpr h))
        · exact Or.inr (Or.inr (Or.inl
            ⟨a :: u, v, w, congrArg (List.cons a) hs, congrArg (List.cons a) ht⟩))
        · exact Or.inr (Or.inr (Or.inr
            ⟨a :: u, v, w, congrArg (List.cons a) hs, congrArg (List.cons a) ht⟩))
      · cases a
        · cases b
          · exact absurd rfl hab
          · exact Or.inr (Or.inr (Or.inl ⟨[], s, t, rfl, rfl⟩))
        · cases b
          · exact Or.inr (Or.inr (Or.inr ⟨[], s, t, rfl, rfl⟩))
          · exact absurd rfl hab

/-- Admissible words, of any Orders, are sorted like their points. -/
theorem sbPoint_lt_iff_lt {s t : List Bool} (hs : Admissible s) (ht : Admissible t) :
    sbPoint s < sbPoint t ↔ s < t := by
  by_cases hst : s = t
  · rw [hst]
    exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
  · rcases prefix_or_split s t with h | h | ⟨u, v, w, rfl, rfl⟩ | ⟨u, v, w, rfl, rfl⟩
    · exact absurd h (admissible_not_prefix s t hs ht hst)
    · exact absurd h (admissible_not_prefix t s ht hs (Ne.symm hst))
    · exact ⟨fun _ => split_lt u v w, fun _ => sbPoint_split_lt u v w⟩
    · exact ⟨fun h => absurd h (lt_asymm (sbPoint_split_lt u w v)),
        fun h => absurd h (lt_asymm (split_lt u w v))⟩

/-- A run of a 1s in front of a word adds a to its point. -/
theorem sbPoint_replicate_true_append (a : ℕ) (s : List Bool) :
    sbPoint (List.replicate a true ++ s) = a + sbPoint s := by
  induction a with
  | zero =>
    rw [List.replicate_zero, List.nil_append, Nat.cast_zero, zero_add]
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, sbPoint_true_cons, ih]
    push_cast
    ring

/-- A run of b 0s in front of a word maps its point y to 1/(b + 1/y). -/
theorem sbPoint_replicate_false_append (b : ℕ) (s : List Bool) :
    sbPoint (List.replicate b false ++ s) = 1 / (b + 1 / sbPoint s) := by
  have hs := sbPoint_pos s
  induction b with
  | zero =>
    rw [List.replicate_zero, List.nil_append, Nat.cast_zero, zero_add, one_div_one_div]
  | succ b ih =>
    rw [List.replicate_succ, List.cons_append, sbPoint_false_cons, ih]
    push_cast
    field_simp
    ring

/-- A run of a 1s and a run of b 0s in front of a word: two more quotients, a and b, in
    front of the continued fraction of its point. -/
theorem sbPoint_runs (a b : ℕ) (s : List Bool) :
    sbPoint (List.replicate a true ++ (List.replicate b false ++ s)) =
      a + 1 / (b + 1 / sbPoint s) := by
  rw [sbPoint_replicate_true_append, sbPoint_replicate_false_append]

/-- A last run of a 1s: the last quotient is a + 1. -/
theorem sbPoint_replicate_true (a : ℕ) : sbPoint (List.replicate a true) = a + 1 := by
  have h := sbPoint_replicate_true_append a []
  rw [List.append_nil, sbPoint_nil] at h
  exact h

/-- A last run of b 0s: the last quotient is b + 1. -/
theorem sbPoint_replicate_false (b : ℕ) : sbPoint (List.replicate b false) = 1 / (b + 1) := by
  have h := sbPoint_replicate_false_append b []
  rw [List.append_nil, sbPoint_nil, div_one] at h
  exact h

/-- An entry v ≥ 1 of a marked vector, a run of v 1s and its closing 0: the quotient v
    and a quotient that starts at 1. -/
theorem sbPoint_expandEntry_natCast (v : ℕ) (hv : 1 ≤ v) (s : List Bool) :
    sbPoint (expandEntry (v : ℤ) ++ s) = v + 1 / (1 + 1 / sbPoint s) := by
  have h := sbPoint_runs v 1 s
  rw [expandEntry_natCast v hv, List.append_assoc]
  rw [Nat.cast_one] at h
  exact h

/-- An entry -w of a marked vector, w more 0s: the quotient that started at 1 grows by
    w. -/
theorem sbPoint_expandEntry_neg_natCast (w : ℕ) (s : List Bool) :
    sbPoint (expandEntry (-(w : ℤ)) ++ s) = 1 / (w + 1 / sbPoint s) := by
  rw [expandEntry_neg_natCast, sbPoint_replicate_false_append]

/-- The marked vector [6, -2, 1, -1] of 1087, the word 111111000100 with runs 6, 3, 1,
    2: the point is 6 + 1/(3 + 1/(1 + 1/3)) = 94/15. -/
example : sbPoint (decodeVector [6, -2, 1, -1]) = 94 / 15 := by
  decide +kernel

end AcceleratedCollatz
