-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainEquiv
import AcceleratedCollatz.TRank

/-!
  Computable chain decomposition. `chainParse u` cuts u greedily into shortest
  prefixes of level < 1; on blocks ++ tail it returns the blocks
  (`chainParse_append`, `chainParse_flatten`). `chainOf s`: the chain blocks of s,
  the inverse of `chainWord` (`chainOf_chainWord`, `chainWord_chainOf`), equal to
  `chainEquiv` (`chainEquiv_eq_chainOf`). `codeOf s`: the (d, c) list of s, c the
  0-based `rank` of the block in its Order; equal to `codeEquiv`
  (`codeEquiv_eq_codeOf`).
-/

namespace AcceleratedCollatz

theorem seqProduct_nil : seqProduct [] = 1 := by
  simp [seqProduct]

/-- Greedy parse: repeatedly the shortest prefix of level < 1. -/
def chainParse (u : List Bool) : List (List Bool) :=
  if h : ∃ j, j < u.length + 1 ∧ seqProduct (u.take j) < 1 then
    u.take (Nat.find h) :: chainParse (u.drop (Nat.find h))
  else []
termination_by u.length
decreasing_by
  have hspec := Nat.find_spec h
  have hpos : Nat.find h ≠ 0 := by
    intro h0
    rw [h0, List.take_zero, seqProduct_nil] at hspec
    exact absurd hspec.2 (lt_irrefl 1)
  rw [List.length_drop]
  omega

/-- Chain blocks of s: the parse of s without its leading 1, without the tail 0. -/
def chainOf (s : List Bool) : List (List Bool) :=
  (chainParse s.tail).filter (fun b => decide (1 ≤ order b))

/-- (d, c) list of s: Order and 0-based rank of every chain block. -/
def codeOf (s : List Bool) : List (ℕ × ℕ) :=
  (chainOf s).map (fun b => (order b, rank (order b) b))

set_option linter.hashCommand false in
#guard chainOf [true, true, false, true, true, false, false] =
  [[true, false], [true, true, false, false]]

set_option linter.hashCommand false in
#guard codeOf [true, true, true, false, true, true, true, false, false, false] = [(5, 1)]

theorem chainParse_nil : chainParse [] = [] := by
  have hno : ¬ ∃ j, j < ([] : List Bool).length + 1 ∧
      seqProduct (([] : List Bool).take j) < 1 := by
    rintro ⟨j, -, hlt⟩
    rw [List.take_nil, seqProduct_nil] at hlt
    exact lt_irrefl 1 hlt
  rw [chainParse]
  simp only [hno, ↓reduceDIte]

/-- An admissible prefix is the first block. -/
theorem chainParse_append (b r : List Bool) (hb : Admissible b) :
    chainParse (b ++ r) = b :: chainParse r := by
  have hex : ∃ j, j < (b ++ r).length + 1 ∧ seqProduct ((b ++ r).take j) < 1 := by
    refine ⟨b.length, ?_, ?_⟩
    · rw [List.length_append]
      omega
    · rw [List.take_left]
      exact hb.lt_one
  have hfind : Nat.find hex = b.length := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.length_append]
      omega
    · rw [List.take_left]
      exact hb.lt_one
    · intro m hm hcon
      have htake : (b ++ r).take m = b.take m := List.take_append_of_le_length (by omega)
      rw [htake] at hcon
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rw [List.take_zero, seqProduct_nil] at hcon
        exact lt_irrefl 1 hcon.2
      · exact lt_asymm (hb.prefix_gt m hpos hm) hcon.2
  rw [chainParse]
  simp only [hex, ↓reduceDIte]
  rw [hfind, List.take_left, List.drop_left]

/-- On admissible blocks followed by r: the blocks, then the parse of r. -/
theorem chainParse_flatten (bs : List (List Bool)) (r : List Bool)
    (h : ∀ b ∈ bs, Admissible b) : chainParse (bs.flatten ++ r) = bs ++ chainParse r := by
  induction bs with
  | nil =>
    rfl
  | cons b t ih =>
    rw [List.flatten_cons, List.append_assoc, chainParse_append _ _ (h b List.mem_cons_self),
      ih (fun c hc => h c (List.mem_cons_of_mem b hc))]
    rfl

theorem chainParse_singleton_false : chainParse [false] = [[false]] := by
  have h := chainParse_append [false] [] admissible_singleton_false
  rw [List.append_nil, chainParse_nil] at h
  exact h

/-- `chainOf` inverts `chainWord`. -/
theorem chainOf_chainWord (bs : List (List Bool)) (h : ∀ b ∈ bs, IsChainBlock b) :
    chainOf (chainWord bs) = bs := by
  have hkeep : bs.filter (fun b => decide (1 ≤ order b)) = bs := by
    rw [List.filter_eq_self]
    intro b hb
    exact decide_eq_true (h b hb).order_pos
  unfold chainOf chainWord
  rw [List.tail_cons, chainParse_flatten bs _ (fun b hb => (h b hb).adm), List.filter_append,
    hkeep]
  have hdrop : List.filter (fun b => decide (1 ≤ order b)) [[false]] = [] := by
    decide
  rcases chainTail_cases bs with ⟨-, ht⟩ | ⟨-, ht⟩
  · rw [ht, chainParse_singleton_false, hdrop, List.append_nil]
  · rw [ht, chainParse_nil, List.filter_nil, List.append_nil]

/-- The chain blocks of an admissible PV of Order n + 1, and their chain word. -/
theorem chainWord_chainOf {n : ℕ} {s : List Bool} (hs : s ∈ admSet (n + 1)) :
    chainOf s ∈ chainBlocks n ∧ chainWord (chainOf s) = s := by
  obtain ⟨bs, hbs, rfl⟩ := chainWord_surjOn n (Finset.mem_coe.mpr hs)
  rw [chainOf_chainWord bs hbs.1]
  exact ⟨hbs, rfl⟩

/-- `chainOf` computes `chainEquiv`. -/
theorem chainEquiv_eq_chainOf (n : ℕ) (s : (admSet (n + 1) : Set (List Bool))) :
    (chainEquiv n s : List (List Bool)) = chainOf s := by
  have h := chainOf_chainWord (chainEquiv n s) (chainEquiv n s).2.1
  rw [chainWord_chainEquiv] at h
  exact h.symm

/-- `codeOf` computes `codeEquiv`. -/
theorem codeEquiv_eq_codeOf (n : ℕ) (s : (admSet (n + 1) : Set (List Bool))) :
    (codeEquiv n s).1.map (fun x => (x.1, (x.2 : ℕ))) = codeOf s := by
  unfold codeOf
  rw [← chainEquiv_eq_chainOf n s]
  change ((chainEquiv n s).1.pmap blockCode _).map _ = _
  rw [List.map_pmap]
  have hfun : ∀ (a : List Bool) (h : a ∈ admSet (order a)),
      ((blockCode a h).fst, ((blockCode a h).snd : ℕ)) = (order a, rank (order a) a) :=
    fun a h => Prod.ext rfl (admIndex_symm_eq_rank (order a) a h)
  have hcongr := List.pmap_congr_left (chainEquiv n s).1
    (f := fun a h => ((blockCode a h).fst, ((blockCode a h).snd : ℕ)))
    (g := fun a (_ : a ∈ admSet (order a)) => (order a, rank (order a) a))
    (H₁ := fun b hb => mem_admSet_order_of_chainBlock ((chainEquiv n s).2.1 b hb))
    (H₂ := fun b hb => mem_admSet_order_of_chainBlock ((chainEquiv n s).2.1 b hb))
    (fun a _ h₁ _ => hfun a h₁)
  exact hcongr.trans (List.pmap_eq_map _)

end AcceleratedCollatz
