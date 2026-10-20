-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TMarkerPoint

/-!
  The point of a number by its binary digits read from the highest one. A list of digits,
  lowest first, is read by `digitPoint` with the maps of `markerPoint` (a digit 1:
  y ↦ y + 1, a digit 0: y ↦ 1/(y + 1), the first digit applied last), so that
  `markerPoint` is `digitPoint` of the digits lowest first (`markerPoint_ofBits`) and
  `hiPoint` is `digitPoint` of the digits highest first. The digits of an odd x are runs
  of t_1, ..., t_k digits 1 (lowest run first, zeros kept as runs of length 0) separated
  by single digits 0 (`runsWord`); their point is the continued fraction
  [s_1; s_2 + 1, ..., s_(k-1) + 1, s_k + 2] of the run lengths in reading order
  (`cfRuns`, `digitPoint_runsWord`). Reversing the digits reverses the runs
  (`runsWord_reverse`), so x lowest first gives [t_1; t_2 + 1, ..., t_k + 2]
  (`markerPoint_runs`) and highest first [t_k; t_(k-1) + 1, ..., t_1 + 2] (`hiPoint_runs`):
  the readings of the trees of Yu-Ting and of Hanna, Czyz and Self (K. Ryde, Trees of
  Rationals), each with 1 taken off its first quotient.
-/

namespace AcceleratedCollatz

/-- The point of a list of digits, lowest first: 1 for no digits; a digit 1 in front maps
    y to y + 1, a digit 0 in front maps y to 1/(y + 1). -/
def digitPoint : List Bool → ℚ
  | [] => 1
  | true :: ds => digitPoint ds + 1
  | false :: ds => 1 / (digitPoint ds + 1)

theorem digitPoint_true_cons (ds : List Bool) : digitPoint (true :: ds) = digitPoint ds + 1 :=
  rfl

theorem digitPoint_false_cons (ds : List Bool) :
    digitPoint (false :: ds) = 1 / (digitPoint ds + 1) :=
  rfl

/-- t digits 1 in front add t. -/
theorem digitPoint_replicate_true_append (t : ℕ) (ds : List Bool) :
    digitPoint (List.replicate t true ++ ds) = t + digitPoint ds := by
  induction t with
  | zero =>
    rw [List.replicate_zero, List.nil_append, Nat.cast_zero, zero_add]
  | succ t ih =>
    rw [List.replicate_succ, List.cons_append, digitPoint_true_cons, ih]
    push_cast
    ring

/-! ### Digits and numbers -/

/-- The number of a list of digits, lowest first. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | true :: ds => 2 * ofBits ds + 1
  | false :: ds => 2 * ofBits ds

/-- The digits of a number, lowest first, without digits 0 on top. -/
def toBits (n : ℕ) : List Bool :=
  if h : n = 0 then [] else decide (n % 2 = 1) :: toBits (n / 2)
decreasing_by
  omega

/-- The highest digit of a list is a 1. -/
def TopTrue : List Bool → Prop
  | [] => False
  | [b] => b = true
  | _ :: d :: ds => TopTrue (d :: ds)

theorem topTrue_cons {ds : List Bool} (b : Bool) (h : TopTrue ds) : TopTrue (b :: ds) := by
  match ds, h with
  | [], h => exact h.elim
  | _ :: _, h => exact h

theorem topTrue_append (l : List Bool) {ds : List Bool} (h : TopTrue ds) :
    TopTrue (l ++ ds) := by
  induction l with
  | nil =>
    exact h
  | cons b l ih =>
    exact topTrue_cons b ih

theorem topTrue_replicate : ∀ t : ℕ, TopTrue (List.replicate (t + 1) true)
  | 0 => rfl
  | t + 1 => topTrue_replicate t

theorem ofBits_pos : ∀ ds : List Bool, TopTrue ds → 0 < ofBits ds
  | [], h => h.elim
  | [b], h => by
    change b = true at h
    subst h
    change 0 < 2 * 0 + 1
    omega
  | true :: d :: ds, _ => by
    change 0 < 2 * ofBits (d :: ds) + 1
    omega
  | false :: d :: ds, h => by
    have := ofBits_pos (d :: ds) h
    change 0 < 2 * ofBits (d :: ds)
    omega

/-- `markerPoint` reads the digits lowest first. -/
theorem markerPoint_ofBits : ∀ ds : List Bool, TopTrue ds →
    markerPoint (ofBits ds) = digitPoint ds
  | [], h => h.elim
  | [b], h => by
    change b = true at h
    subst h
    have e := markerPoint_bit_one 0
    rw [markerPoint_zero] at e
    change markerPoint (2 * 0 + 1) = 1 + 1
    exact e
  | true :: d :: ds, h => by
    change markerPoint (2 * ofBits (d :: ds) + 1) = digitPoint (d :: ds) + 1
    rw [markerPoint_bit_one, markerPoint_ofBits (d :: ds) h]
  | false :: d :: ds, h => by
    have hpos := ofBits_pos (d :: ds) h
    change markerPoint (2 * ofBits (d :: ds)) = 1 / (digitPoint (d :: ds) + 1)
    rw [markerPoint_bit_zero hpos, markerPoint_ofBits (d :: ds) h]

theorem toBits_zero : toBits 0 = [] := by
  rw [toBits]
  rfl

theorem toBits_bit_one (n : ℕ) : toBits (2 * n + 1) = true :: toBits n := by
  have h1 : (2 * n + 1) % 2 = 1 := by
    omega
  have h2 : (2 * n + 1) / 2 = n := by
    omega
  rw [toBits, dite_eq_right (Nat.succ_ne_zero _), h1, h2]
  rfl

theorem toBits_bit_zero {n : ℕ} (hn : 1 ≤ n) : toBits (2 * n) = false :: toBits n := by
  have h0 : 2 * n ≠ 0 := by
    omega
  have h1 : (2 * n) % 2 = 0 := by
    omega
  have h2 : 2 * n / 2 = n := by
    omega
  rw [toBits, dite_eq_right h0, h1, h2]
  rfl

/-- The digits of the number of a list with a 1 on top are that list. -/
theorem toBits_ofBits : ∀ ds : List Bool, TopTrue ds → toBits (ofBits ds) = ds
  | [], h => h.elim
  | [b], h => by
    change b = true at h
    subst h
    change toBits (2 * 0 + 1) = [true]
    rw [toBits_bit_one, toBits_zero]
  | true :: d :: ds, h => by
    change toBits (2 * ofBits (d :: ds) + 1) = true :: d :: ds
    rw [toBits_bit_one, toBits_ofBits (d :: ds) h]
  | false :: d :: ds, h => by
    have hpos := ofBits_pos (d :: ds) h
    change toBits (2 * ofBits (d :: ds)) = false :: d :: ds
    rw [toBits_bit_zero hpos, toBits_ofBits (d :: ds) h]

/-- The point of a number by its binary digits read from the highest one. -/
def hiPoint (n : ℕ) : ℚ :=
  digitPoint (toBits n).reverse

/-! ### Runs of digits 1 -/

/-- Runs of t_1, t_2, ... digits 1, lowest first, separated by single digits 0. -/
def runsWord : List ℕ → List Bool
  | [] => []
  | [t] => List.replicate t true
  | t :: u :: ts => List.replicate t true ++ false :: runsWord (u :: ts)

theorem runsWord_cons_cons (t u : ℕ) (ts : List ℕ) :
    runsWord (t :: u :: ts) = List.replicate t true ++ false :: runsWord (u :: ts) :=
  rfl

/-- The continued fraction [s_1; s_2 + 1, ..., s_(k-1) + 1, s_k + 2] of run lengths
    s_1, ..., s_k in reading order (1 for no runs). -/
def cfRuns : List ℕ → ℚ
  | [] => 1
  | [t] => t + 1
  | t :: u :: ts => t + 1 / (cfRuns (u :: ts) + 1)

/-- The point of the runs is their continued fraction. -/
theorem digitPoint_runsWord : ∀ ts : List ℕ, digitPoint (runsWord ts) = cfRuns ts
  | [] => rfl
  | [t] => by
    have h := digitPoint_replicate_true_append t []
    rw [List.append_nil] at h
    change digitPoint (List.replicate t true) = t + 1
    rw [h]
    rfl
  | t :: u :: ts => by
    rw [runsWord_cons_cons, digitPoint_replicate_true_append, digitPoint_false_cons,
      digitPoint_runsWord (u :: ts)]
    rfl

/-- A run appended on top. -/
theorem runsWord_append_single : ∀ (ts : List ℕ), ts ≠ [] → ∀ t : ℕ,
    runsWord (ts ++ [t]) = runsWord ts ++ false :: List.replicate t true
  | [], h, _ => absurd rfl h
  | [_], _, _ => rfl
  | s :: u :: l, _, t => by
    have ih : runsWord (u :: (l ++ [t])) = runsWord (u :: l) ++ false :: List.replicate t true :=
      runsWord_append_single (u :: l) (List.cons_ne_nil u l) t
    change runsWord (s :: u :: (l ++ [t])) =
      runsWord (s :: u :: l) ++ false :: List.replicate t true
    rw [runsWord_cons_cons, runsWord_cons_cons, ih, List.append_assoc, List.cons_append]

/-- Reversing the digits reverses the runs. -/
theorem runsWord_reverse : ∀ ts : List ℕ, (runsWord ts).reverse = runsWord ts.reverse
  | [] => rfl
  | [t] => by
    change (List.replicate t true).reverse = List.replicate t true
    rw [List.reverse_replicate]
  | t :: u :: ts => by
    have e1 : (t :: u :: ts).reverse = (u :: ts).reverse ++ [t] := List.reverse_cons
    have hne : (u :: ts).reverse ≠ [] := by
      simp
    have e2 := runsWord_append_single _ hne t
    have e3 : (List.replicate t true ++ false :: runsWord (u :: ts)).reverse =
        (runsWord (u :: ts)).reverse ++ false :: List.replicate t true := by
      simp
    rw [runsWord_cons_cons, e3, runsWord_reverse (u :: ts), e1, e2]

/-- Runs with a last run of at least one digit 1 have a 1 on top. -/
theorem topTrue_runsWord (ts : List ℕ) {t : ℕ} (ht : 1 ≤ t) :
    TopTrue (runsWord (ts ++ [t])) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  by_cases hne : ts = []
  · subst hne
    exact topTrue_replicate s
  · rw [runsWord_append_single ts hne]
    exact topTrue_append _ (topTrue_cons false (topTrue_replicate s))

/-! ### The two readings -/

/-- Read from the lowest digit: [t_1; t_2 + 1, ..., t_k + 2] (the tree of Yu-Ting). -/
theorem markerPoint_runs (ts : List ℕ) {t : ℕ} (ht : 1 ≤ t) :
    markerPoint (ofBits (runsWord (ts ++ [t]))) = cfRuns (ts ++ [t]) := by
  rw [markerPoint_ofBits _ (topTrue_runsWord ts ht), digitPoint_runsWord]

/-- Read from the highest digit: [t_k; t_(k-1) + 1, ..., t_1 + 2] (the tree of Hanna, Czyz
    and Self). -/
theorem hiPoint_runs (ts : List ℕ) {t : ℕ} (ht : 1 ≤ t) :
    hiPoint (ofBits (runsWord (ts ++ [t]))) = cfRuns (t :: ts.reverse) := by
  have e : (ts ++ [t]).reverse = t :: ts.reverse := by
    simp
  rw [hiPoint, toBits_ofBits _ (topTrue_runsWord ts ht), runsWord_reverse, e,
    digitPoint_runsWord]

/-- The runs and the decomposition of `markerPoint_ht`: the number of t, u, ... is
    h 2^(t + 1) + 2^t - 1 with h the number of u, .... -/
theorem ofBits_runsWord_cons_cons (t u : ℕ) (ts : List ℕ) :
    ofBits (runsWord (t :: u :: ts)) + 1 = 2 ^ t * (2 * ofBits (runsWord (u :: ts)) + 1) := by
  rw [runsWord_cons_cons]
  generalize runsWord (u :: ts) = ds
  induction t with
  | zero =>
    rw [List.replicate_zero, List.nil_append, pow_zero, one_mul]
    rfl
  | succ t ih =>
    rw [List.replicate_succ, List.cons_append]
    change 2 * ofBits (List.replicate t true ++ false :: ds) + 1 + 1 = _
    rw [pow_succ, show 2 ^ t * 2 * (2 * ofBits ds + 1) = 2 * (2 ^ t * (2 * ofBits ds + 1)) by
      ring, ← ih]
    omega

/-- 1087 = 10000111111 in binary, runs 6, 0, 0, 0, 1: from the lowest digit 73/11, from the
    highest 43/26. -/
example : markerPoint 1087 = 73 / 11 ∧ hiPoint 1087 = 43 / 26 := by
  have e : ofBits (runsWord ([6, 0, 0, 0] ++ [1])) = 1087 := by
    decide
  have h1 := markerPoint_runs [6, 0, 0, 0] (t := 1) le_rfl
  have h2 := hiPoint_runs [6, 0, 0, 0] (t := 1) le_rfl
  rw [e] at h1 h2
  rw [h1, h2]
  norm_num [cfRuns]

end AcceleratedCollatz
