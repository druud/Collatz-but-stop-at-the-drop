-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSternBrocotTree
import AcceleratedCollatz.TVectorLex
import Mathlib.Tactic.LinearCombination

/-!
  The interval of a node: between the fraction below and the fraction above it, compared
  by cross products. Below a node the fractions are nonnegative combinations of its two
  fractions (`sbNodeFrom_comb`), so every point of a word that continues w lies strictly
  inside the interval of w (`sbNode_inside`). Two words that part at a first place, the
  one with the 0 there first: the interval of the first ends where the interval of the
  second starts or before it (`sbNode_split_le`), and the two touch exactly when after
  that place the first word has only 1s and the second only 0s (`sbNode_split_eq_iff`).
  So the intervals of admissible words, of any Orders, are disjoint and sorted like the
  words (`admissible_interval_le`), and two of them touch exactly for v0 and v10...0
  (`admissible_touch_iff`).
-/

namespace AcceleratedCollatz

theorem sbNodeFrom_append (s : SBNode) (w u : List Bool) :
    sbNodeFrom s (w ++ u) = sbNodeFrom (sbNodeFrom s w) u := by
  induction w generalizing s with
  | nil =>
    rfl
  | cons b w ih =>
    rw [List.cons_append, sbNodeFrom_cons, sbNodeFrom_cons, ih]

theorem sbNodeFrom_append_single (s : SBNode) (u : List Bool) (b : Bool) :
    sbNodeFrom s (u ++ [b]) = sbMove b (sbNodeFrom s u) := by
  rw [sbNodeFrom_append]
  rfl

theorem sbNode_append (w u : List Bool) : sbNode (w ++ u) = sbNodeFrom (sbNode w) u :=
  sbNodeFrom_append sbRoot w u

/-- Below a node s the fraction below is α lo + β hi and the fraction above γ lo + δ hi,
    with α, δ ≥ 1; β = 0 exactly when every move was to the left, γ = 0 exactly when
    every move was to the right. -/
theorem sbNodeFrom_comb (s : SBNode) (u : List Bool) :
    ∃ α β γ δ : ℕ, 1 ≤ α ∧ 1 ≤ δ ∧ (β = 0 ↔ ∀ b ∈ u, b = false) ∧
      (γ = 0 ↔ ∀ b ∈ u, b = true) ∧
      (sbNodeFrom s u).loNum = α * s.loNum + β * s.hiNum ∧
      (sbNodeFrom s u).loDen = α * s.loDen + β * s.hiDen ∧
      (sbNodeFrom s u).hiNum = γ * s.loNum + δ * s.hiNum ∧
      (sbNodeFrom s u).hiDen = γ * s.loDen + δ * s.hiDen := by
  induction u using List.reverseRecOn with
  | nil =>
    refine ⟨1, 0, 0, 1, le_rfl, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp [sbNodeFrom]
    · simp [sbNodeFrom]
    · simp [sbNodeFrom]
    · simp [sbNodeFrom]
  | append_singleton u b ih =>
    obtain ⟨α, β, γ, δ, hα, hδ, hβ, hγ, h1, h2, h3, h4⟩ := ih
    rw [sbNodeFrom_append_single]
    cases b
    · refine ⟨α, β, α + γ, β + δ, hα, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hβ]
        simp
      · constructor
        · intro h
          omega
        · intro h
          have := h false (by simp)
          simp at this
      · simp only [sbMove, Bool.false_eq_true, ↓reduceIte]
        exact h1
      · simp only [sbMove, Bool.false_eq_true, ↓reduceIte]
        exact h2
      · simp only [sbMove, Bool.false_eq_true, ↓reduceIte]
        rw [h1, h3]
        ring
      · simp only [sbMove, Bool.false_eq_true, ↓reduceIte]
        rw [h2, h4]
        ring
    · refine ⟨α + γ, β + δ, γ, δ, by omega, hδ, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · constructor
        · intro h
          omega
        · intro h
          have := h true (by simp)
          simp at this
      · rw [hγ]
        simp
      · simp only [sbMove, ↓reduceIte]
        rw [h1, h3]
        ring
      · simp only [sbMove, ↓reduceIte]
        rw [h2, h4]
        ring
      · simp only [sbMove, ↓reduceIte]
        exact h3
      · simp only [sbMove, ↓reduceIte]
        exact h4

/-- The point of a word that continues w lies strictly inside the interval of w. -/
theorem sbNode_inside (w u : List Bool) :
    (sbNode w).loNum * ((sbNode (w ++ u)).loDen + (sbNode (w ++ u)).hiDen) <
        ((sbNode (w ++ u)).loNum + (sbNode (w ++ u)).hiNum) * (sbNode w).loDen ∧
      ((sbNode (w ++ u)).loNum + (sbNode (w ++ u)).hiNum) * (sbNode w).hiDen <
        (sbNode w).hiNum * ((sbNode (w ++ u)).loDen + (sbNode (w ++ u)).hiDen) := by
  have hdet := sbNode_det w
  rw [sbNode_append]
  obtain ⟨α, β, γ, δ, hα, hδ, _, _, h1, h2, h3, h4⟩ := sbNodeFrom_comb (sbNode w) u
  rw [h1, h2, h3, h4]
  have hd : ((sbNode w).hiNum : ℤ) * (sbNode w).loDen -
      (sbNode w).loNum * (sbNode w).hiDen = 1 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hdet
    push_cast at this
    linarith
  constructor
  · have e : ((α * (sbNode w).loNum + β * (sbNode w).hiNum + (γ * (sbNode w).loNum +
        δ * (sbNode w).hiNum) : ℕ) : ℤ) * (sbNode w).loDen -
        (sbNode w).loNum * ((α * (sbNode w).loDen + β * (sbNode w).hiDen +
        (γ * (sbNode w).loDen + δ * (sbNode w).hiDen) : ℕ) : ℤ) = β + δ := by
      push_cast
      linear_combination ((β : ℤ) + δ) * hd
    have : (0 : ℤ) < β + δ := by
      omega
    have h' : ((sbNode w).loNum * (α * (sbNode w).loDen + β * (sbNode w).hiDen +
        (γ * (sbNode w).loDen + δ * (sbNode w).hiDen)) : ℤ) <
        ((α * (sbNode w).loNum + β * (sbNode w).hiNum + (γ * (sbNode w).loNum +
        δ * (sbNode w).hiNum)) * (sbNode w).loDen : ℤ) := by
      push_cast at e ⊢
      linarith
    exact_mod_cast h'
  · have e : ((sbNode w).hiNum : ℤ) * ((α * (sbNode w).loDen + β * (sbNode w).hiDen +
        (γ * (sbNode w).loDen + δ * (sbNode w).hiDen) : ℕ) : ℤ) -
        ((α * (sbNode w).loNum + β * (sbNode w).hiNum + (γ * (sbNode w).loNum +
        δ * (sbNode w).hiNum) : ℕ) : ℤ) * (sbNode w).hiDen = α + γ := by
      push_cast
      linear_combination ((α : ℤ) + γ) * hd
    have : (0 : ℤ) < α + γ := by
      omega
    have h' : ((α * (sbNode w).loNum + β * (sbNode w).hiNum + (γ * (sbNode w).loNum +
        δ * (sbNode w).hiNum)) * (sbNode w).hiDen : ℤ) <
        ((sbNode w).hiNum * (α * (sbNode w).loDen + β * (sbNode w).hiDen +
        (γ * (sbNode w).loDen + δ * (sbNode w).hiDen)) : ℤ) := by
      push_cast at e ⊢
      linarith
    exact_mod_cast h'

/-- Two words that part after v, the first with a 0, the second with a 1: the end of the
    first interval and the start of the second, in cross products, differ by
    γ α' + γ β' + δ β', where γ = 0 exactly when the first word has only 1s after the
    place and β' = 0 exactly when the second has only 0s after it. -/
theorem sbNode_split_cross (v x y : List Bool) :
    ∃ c : ℕ, (c = 0 ↔ (∀ b ∈ x, b = true) ∧ ∀ b ∈ y, b = false) ∧
      (sbNode (v ++ true :: y)).loNum * (sbNode (v ++ false :: x)).hiDen =
        (sbNode (v ++ false :: x)).hiNum * (sbNode (v ++ true :: y)).loDen + c := by
  have hdet := sbNode_det v
  have hd : ((sbNode v).hiNum : ℤ) * (sbNode v).loDen -
      (sbNode v).loNum * (sbNode v).hiDen = 1 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hdet
    push_cast at this
    linarith
  have es : v ++ false :: x = v ++ [false] ++ x := by
    simp
  have et : v ++ true :: y = v ++ [true] ++ y := by
    simp
  rw [es, et, sbNode_append (v ++ [false]), sbNode_append (v ++ [true]), sbNode_append v [false],
    sbNode_append v [true]]
  obtain ⟨α, β, γ, δ, hα, hδ, _, hγ, _, _, h3, h4⟩ :=
    sbNodeFrom_comb (sbNodeFrom (sbNode v) [false]) x
  obtain ⟨α', β', γ', δ', hα', hδ', hβ', _, h1', h2', _, _⟩ :=
    sbNodeFrom_comb (sbNodeFrom (sbNode v) [true]) y
  refine ⟨γ * α' + γ * β' + δ * β', ?_, ?_⟩
  · rw [← hγ, ← hβ']
    constructor
    · intro h
      have hga : γ * α' = 0 := by
        omega
      have hdb : δ * β' = 0 := by
        omega
      rcases Nat.mul_eq_zero.mp hga with h0 | h0
      · rcases Nat.mul_eq_zero.mp hdb with h1 | h1
        · omega
        · exact ⟨h0, h1⟩
      · omega
    · rintro ⟨h0, h1⟩
      rw [h0, h1]
      ring
  · rw [h3, h4, h1', h2']
    simp only [sbNodeFrom, sbMove, Bool.false_eq_true, ↓reduceIte]
    have key : (((α' * ((sbNode v).loNum + (sbNode v).hiNum) + β' * (sbNode v).hiNum) *
        (γ * (sbNode v).loDen + δ * ((sbNode v).loDen + (sbNode v).hiDen)) : ℕ) : ℤ) =
        (((γ * (sbNode v).loNum + δ * ((sbNode v).loNum + (sbNode v).hiNum)) *
        (α' * ((sbNode v).loDen + (sbNode v).hiDen) + β' * (sbNode v).hiDen) +
        (γ * α' + γ * β' + δ * β')) : ℕ) := by
      push_cast
      linear_combination ((γ : ℤ) * α' + γ * β' + δ * β') * hd
    exact_mod_cast key

/-- Two words that part after v, the first with a 0, the second with a 1: the interval of
    the first ends where the interval of the second starts or before it. -/
theorem sbNode_split_le (v x y : List Bool) :
    (sbNode (v ++ false :: x)).hiNum * (sbNode (v ++ true :: y)).loDen ≤
      (sbNode (v ++ true :: y)).loNum * (sbNode (v ++ false :: x)).hiDen := by
  obtain ⟨c, _, h⟩ := sbNode_split_cross v x y
  omega

/-- The two intervals touch exactly when the first word has only 1s and the second only
    0s after the place where they part. -/
theorem sbNode_split_eq_iff (v x y : List Bool) :
    (sbNode (v ++ false :: x)).hiNum * (sbNode (v ++ true :: y)).loDen =
        (sbNode (v ++ true :: y)).loNum * (sbNode (v ++ false :: x)).hiDen ↔
      (∀ b ∈ x, b = true) ∧ ∀ b ∈ y, b = false := by
  obtain ⟨c, hc, h⟩ := sbNode_split_cross v x y
  rw [← hc]
  omega

/-- Admissible words, of any Orders, have disjoint intervals, sorted like the words. -/
theorem admissible_interval_le {s t : List Bool} (hs : Admissible s) (ht : Admissible t)
    (hst : s < t) :
    (sbNode s).hiNum * (sbNode t).loDen ≤ (sbNode t).loNum * (sbNode s).hiDen := by
  have hne : s ≠ t := ne_of_lt hst
  rcases prefix_or_split s t with h | h | ⟨u, v, w, rfl, rfl⟩ | ⟨u, v, w, rfl, rfl⟩
  · exact absurd h (admissible_not_prefix s t hs ht hne)
  · exact absurd h (admissible_not_prefix t s ht hs (Ne.symm hne))
  · exact sbNode_split_le u v w
  · exact absurd hst (lt_asymm (split_lt u w v))

/-- The intervals of two admissible words s < t touch exactly when s = v0 and
    t = v10...0. -/
theorem admissible_touch_iff {s t : List Bool} (hs : Admissible s) (ht : Admissible t)
    (hst : s < t) :
    (sbNode s).hiNum * (sbNode t).loDen = (sbNode t).loNum * (sbNode s).hiDen ↔
      ∃ v m, s = v ++ [false] ∧ t = v ++ true :: List.replicate m false := by
  constructor
  · intro htouch
    have hne : s ≠ t := ne_of_lt hst
    rcases prefix_or_split s t with h | h | ⟨u, v, w, rfl, rfl⟩ | ⟨u, v, w, rfl, rfl⟩
    · exact absurd h (admissible_not_prefix s t hs ht hne)
    · exact absurd h (admissible_not_prefix t s ht hs (Ne.symm hne))
    · obtain ⟨hv, hw⟩ := (sbNode_split_eq_iff u v w).mp htouch
      have hv0 : v = [] := by
        rcases List.eq_nil_or_concat v with h0 | ⟨L, b, hL⟩
        · exact h0
        · exfalso
          have hb : b = true := hv b (by simp [hL])
          have hlast := admissible_last_false _ hs (by simp)
          rw [hL, List.concat_eq_append] at hlast
          simp [hb] at hlast
      refine ⟨u, w.length, by rw [hv0], ?_⟩
      exact congrArg (fun z => u ++ true :: z) (List.eq_replicate_iff.mpr ⟨rfl, hw⟩)
    · exact absurd hst (lt_asymm (split_lt u w v))
  · rintro ⟨v, m, rfl, rfl⟩
    refine (sbNode_split_eq_iff v [] (List.replicate m false)).mpr ⟨?_, ?_⟩
    · intro b hb
      simp at hb
    · intro b hb
      exact List.eq_of_mem_replicate hb

end AcceleratedCollatz
