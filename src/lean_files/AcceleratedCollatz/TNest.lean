-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TParity

/-!
  First drops of a sequence a : ℕ → ℕ. `IsFirstDrop a i j`: j is the first index
  after i with a j < a i. First drops are unique (`isFirstDrop_unique`) and the
  half-open intervals [i, j) they bound are nested or disjoint
  (`isFirstDrop_laminar`); every start inside [i, j) drops no later than j
  (`exists_isFirstDrop_inside`). Instance: the T-trajectory `tTraj x`, with
  drop time `IsTDrop` (convention drop(1) = 1, trajectory (1, 2, 1)).
-/

namespace AcceleratedCollatz

/-- j is the first index after i with a j < a i. -/
def IsFirstDrop (a : ℕ → ℕ) (i j : ℕ) : Prop :=
  i < j ∧ a j < a i ∧ ∀ k, i < k → k < j → a i ≤ a k

theorem isFirstDrop_unique {a : ℕ → ℕ} {i j j' : ℕ}
    (h : IsFirstDrop a i j) (h' : IsFirstDrop a i j') : j = j' := by
  obtain ⟨hij, hj, hmin⟩ := h
  obtain ⟨hij', hj', hmin'⟩ := h'
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd (hmin' j hij hlt) (not_le.mpr hj)
  · exact heq
  · exact absurd (hmin j' hij' hgt) (not_le.mpr hj')

/-- Any drop below a i after i gives a first drop no later than it. -/
theorem exists_isFirstDrop_le {a : ℕ → ℕ} {i j : ℕ} (hij : i < j) (hj : a j < a i) :
    ∃ j', IsFirstDrop a i j' ∧ j' ≤ j := by
  classical
  have hex : ∃ m, i < m ∧ a m < a i := ⟨j, hij, hj⟩
  refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩,
    Nat.find_min' hex ⟨hij, hj⟩⟩
  intro k hik hk
  by_contra hlt
  exact Nat.find_min hex hk ⟨hik, not_le.mp hlt⟩

/-- A start inside [i, j) drops no later than j. -/
theorem isFirstDrop_nested {a : ℕ → ℕ} {i j i' j' : ℕ}
    (h : IsFirstDrop a i j) (h' : IsFirstDrop a i' j') (hii' : i < i') (hi'j : i' < j) :
    j' ≤ j := by
  obtain ⟨_, hj, hmin⟩ := h
  have hle : a i ≤ a i' := hmin i' hii' hi'j
  obtain ⟨j'', h'', hj''⟩ := exists_isFirstDrop_le hi'j (lt_of_lt_of_le hj hle)
  rw [isFirstDrop_unique h' h'']
  exact hj''

/-- First-drop intervals [i, j) and [i', j') with i < i' are nested or disjoint. -/
theorem isFirstDrop_laminar {a : ℕ → ℕ} {i j i' j' : ℕ}
    (h : IsFirstDrop a i j) (h' : IsFirstDrop a i' j') (hii' : i < i') :
    j' ≤ j ∨ j ≤ i' := by
  rcases lt_or_ge i' j with hi'j | hji'
  · exact Or.inl (isFirstDrop_nested h h' hii' hi'j)
  · exact Or.inr hji'

/-- Every start inside [i, j) has a first drop, no later than j. -/
theorem exists_isFirstDrop_inside {a : ℕ → ℕ} {i j i' : ℕ}
    (h : IsFirstDrop a i j) (hii' : i ≤ i') (hi'j : i' < j) :
    ∃ j', IsFirstDrop a i' j' ∧ j' ≤ j := by
  obtain ⟨_, hj, hmin⟩ := h
  have hle : a i ≤ a i' := by
    rcases hii'.lt_or_eq with hlt | rfl
    · exact hmin i' hlt hi'j
    · exact le_rfl
  exact exists_isFirstDrop_le hi'j (lt_of_lt_of_le hj hle)

/-- The T-trajectory of x. -/
abbrev tTraj (x : ℕ) : ℕ → ℕ := fun k => tStep^[k] x

/-- Drop time j of x under T. Convention drop(1) = 1: the trajectory of 1 is
    (1, 2, 1), drop time 2. -/
def IsTDrop (x j : ℕ) : Prop :=
  if x = 1 then j = 2 else IsFirstDrop (tTraj x) 0 j

theorem tTraj_one : tTraj 1 1 = 2 ∧ tTraj 1 2 = 1 := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

theorem isTDrop_one : IsTDrop 1 2 := by
  simp [IsTDrop]

end AcceleratedCollatz
