-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.AdmissibleLength
import Mathlib.Data.Prod.Lex

/-!
  Integer sweep of Thomas and Williams, Sweeping up Zeta (2018), for two letters:
  integer weight a1 per odd step and a2 per halving (`lvlZ`), steps sorted by
  endpoint level (`sweepZ`). `SweepBijective` states their Thm 6.3: the sweep is a
  bijection on the words of each content (`contentSet`).
-/

namespace AcceleratedCollatz

/-- Integer level of w after m steps: weight a1 per odd step, a2 per halving. -/
def lvlZ (a1 a2 : ℤ) (w : List Bool) (m : ℕ) : ℤ :=
  ((w.take m).map (fun b => if b then a1 else a2)).sum

/-- Sort key of step i in the sweep of Thomas and Williams: negative endpoint levels
    first, then endpoint level, then index, all descending. -/
def twKey (a1 a2 : ℤ) (w : List Bool) (i : ℕ) : Lex (Bool × Lex (ℤ × ℕ)) :=
  toLex (decide (lvlZ a1 a2 w (i + 1) < 0), toLex (lvlZ a1 a2 w (i + 1), i))

/-- Step indices of w in the order of `twKey`, largest first. -/
def sweepIdxZ (a1 a2 : ℤ) (w : List Bool) : List ℕ :=
  (List.range w.length).mergeSort (fun i k => decide (twKey a1 a2 w k ≤ twKey a1 a2 w i))

/-- Integer sweep: the steps of w in the order of `sweepIdxZ`. -/
def sweepZ (a1 a2 : ℤ) (w : List Bool) : List Bool :=
  (sweepIdxZ a1 a2 w).map (fun i => w.getD i false)

/-- Dyck words: e1 odd steps, e2 halvings, no integer level below 0. -/
def dyckSet (a1 a2 : ℤ) (e1 e2 : ℕ) : Set (List Bool) :=
  {w | w.count true = e1 ∧ w.count false = e2 ∧ ∀ m ≤ w.length, 0 ≤ lvlZ a1 a2 w m}

/-- Words with e1 odd steps and e2 halvings. -/
def contentSet (e1 e2 : ℕ) : Set (List Bool) :=
  {w | w.count true = e1 ∧ w.count false = e2}

/-- A Dyck word is a word of its content. -/
theorem dyckSet_subset_contentSet (a1 a2 : ℤ) (e1 e2 : ℕ) :
    dyckSet a1 a2 e1 e2 ⊆ contentSet e1 e2 :=
  fun _ h => ⟨h.1, h.2.1⟩

/-- Thomas and Williams, Sweeping up Zeta (2018), Thm 6.3, for two letters. -/
def SweepBijective : Prop :=
  ∀ (a1 a2 : ℤ) (e1 e2 : ℕ),
    Set.BijOn (sweepZ a1 a2) (contentSet e1 e2) (contentSet e1 e2)

theorem sum_map_weights (a1 a2 : ℤ) (l : List Bool) :
    (l.map (fun b => if b then a1 else a2)).sum =
      a1 * order l + a2 * ((l.length : ℤ) - order l) := by
  induction l with
  | nil => simp [order]
  | cons b t ih =>
    cases b with
    | true =>
      have hord : order (true :: t) = order t + 1 := by
        unfold order
        simp
      rw [List.map_cons, List.sum_cons, ih, hord, List.length_cons]
      simp only [↓reduceIte]
      push_cast
      ring
    | false =>
      have hord : order (false :: t) = order t := by
        unfold order
        simp
      rw [List.map_cons, List.sum_cons, ih, hord, List.length_cons]
      push_cast
      ring

theorem lvlZ_weights (c d : ℤ) {s : List Bool} {m : ℕ} (hm : m ≤ s.length) :
    lvlZ (c - d) (-d) s m = c * order (s.take m) - d * m := by
  unfold lvlZ
  rw [sum_map_weights]
  have hlen : (s.take m).length = m := by
    simp [hm]
  rw [hlen]
  ring

theorem sweepIdxZ_perm (a1 a2 : ℤ) (w : List Bool) :
    (sweepIdxZ a1 a2 w).Perm (List.range w.length) :=
  List.mergeSort_perm _ _

theorem sweepIdxZ_nodup (a1 a2 : ℤ) (w : List Bool) : (sweepIdxZ a1 a2 w).Nodup :=
  (sweepIdxZ_perm a1 a2 w).nodup_iff.mpr List.nodup_range

theorem sweepIdxZ_pairwise (a1 a2 : ℤ) (w : List Bool) :
    (sweepIdxZ a1 a2 w).Pairwise (fun i k => twKey a1 a2 w k ≤ twKey a1 a2 w i) := by
  have h := List.pairwise_mergeSort
    (le := fun i k => decide (twKey a1 a2 w k ≤ twKey a1 a2 w i))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hbc hab)
    (fun a b => by
      rcases le_total (twKey a1 a2 w b) (twKey a1 a2 w a) with h | h
      · simp [h]
      · simp [h])
    (List.range w.length)
  exact h.imp (fun hab => by simpa using hab)

theorem lvlZ_append_false (a1 a2 : ℤ) {w : List Bool} {m : ℕ} (hm : m ≤ w.length) :
    lvlZ a1 a2 (w ++ [false]) m = lvlZ a1 a2 w m := by
  unfold lvlZ
  rw [List.take_append_of_le_length hm]

theorem lvlZ_zero (a1 a2 : ℤ) (w : List Bool) : lvlZ a1 a2 w 0 = 0 := by
  simp [lvlZ]

theorem count_true_add_count_false (l : List Bool) :
    l.count true + l.count false = l.length := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | true =>
      simp only [List.count_cons, List.length_cons]
      simp
      omega
    | false =>
      simp only [List.count_cons, List.length_cons]
      simp
      omega

end AcceleratedCollatz
