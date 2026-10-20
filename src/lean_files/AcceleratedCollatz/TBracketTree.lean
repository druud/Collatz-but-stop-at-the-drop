-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketChain

/-!
  Bracket words as plane trees. A bracket tree is the list
  0 :: (W1 ++ ... ++ Wk) with 1 added to the last entry, for bracket trees
  W1 .. Wk whose lengths are valid Orders (`ValidOrders`); k = 0 gives [1]. An
  entry is a node, the Wi are the subtrees of its children, the added 1 its own
  close. The bracket words of the admissible words of Order n + 1 are exactly the
  bracket trees of length n + 1 (`image_bracketWord_admSet`).
-/

namespace AcceleratedCollatz

/-- Bracket trees: a root entry, subtrees with valid lengths, the root's close. -/
inductive IsBracketTree : List ℕ → Prop
  | node (ws : List (List ℕ)) (h : ∀ w ∈ ws, IsBracketTree w)
      (hv : ValidOrders (ws.map List.length)) : IsBracketTree (addLast 1 (0 :: ws.flatten))

theorem length_addLast (p : ℕ) : ∀ l : List ℕ, (addLast p l).length = l.length
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    change (addLast p (b :: l)).length + 1 = _
    rw [length_addLast p (b :: l)]
    rfl

/-- A bracket word has one entry per odd position. -/
theorem length_bracketWord (s : List Bool) : (bracketWord s).length = order s := by
  rw [← card_oddSet]
  simp [bracketWord, oddPos, oddSet, Finset.card, Finset.filter_val, Finset.range_val,
    Multiset.range]

theorem map_length_map_bracketWord (bs : List (List Bool)) :
    (bs.map bracketWord).map List.length = bs.map order := by
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  exact length_bracketWord b

/-- The bracket word of an admissible word of Order ≥ 1 is a bracket tree. -/
theorem isBracketTree_bracketWord (n : ℕ) :
    ∀ s : List Bool, Admissible s → order s = n + 1 → IsBracketTree (bracketWord s) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hA hord
    have hs : s ∈ (admSet (n + 1) : Set (List Bool)) :=
      Finset.mem_coe.mpr ((mem_admSet _ s).mpr ⟨hA, hord⟩)
    obtain ⟨bs, hbs, rfl⟩ := chainWord_surjOn n hs
    rw [bracketWord_chain hbs]
    apply IsBracketTree.node
    · intro w hw
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
      have hcb := hbs.1 b hb
      have hle : order b ≤ n := by
        rw [← hbs.2.2]
        exact List.le_sum_of_mem (List.mem_map_of_mem hb)
      have hpos := hcb.order_pos
      exact ih (order b - 1) (by omega) b hcb.adm (by omega)
    · rw [map_length_map_bracketWord]
      exact hbs.2.1

/-- Every bracket tree is the bracket word of an admissible word of Order ≥ 1. -/
theorem exists_bracketWord_of_isBracketTree {c : List ℕ} (h : IsBracketTree c) :
    ∃ s, IsChainBlock s ∧ bracketWord s = c := by
  induction h with
  | node ws _ hv ih =>
    have hex : ∀ us : List (List ℕ), (∀ w ∈ us, ∃ s, IsChainBlock s ∧ bracketWord s = w) →
        ∃ bs : List (List Bool), (∀ b ∈ bs, IsChainBlock b) ∧ bs.map bracketWord = us := by
      intro us
      induction us with
      | nil =>
        intro _
        exact ⟨[], fun b hb => absurd hb List.not_mem_nil, rfl⟩
      | cons w us ihus =>
        intro hall
        obtain ⟨b, hb, hbw⟩ := hall w List.mem_cons_self
        obtain ⟨bs, hbs, hmap⟩ := ihus (fun x hx => hall x (List.mem_cons_of_mem w hx))
        refine ⟨b :: bs, fun x hx => ?_, by rw [List.map_cons, hbw, hmap]⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hb
        · exact hbs x hx'
    obtain ⟨bs, hbs, hmap⟩ := hex ws ih
    have hvalid : ValidOrders (bs.map order) := by
      rw [← map_length_map_bracketWord, hmap]
      exact hv
    have hmem : bs ∈ chainBlocks (bs.map order).sum := ⟨hbs, hvalid, rfl⟩
    have hadm := (mem_admSet _ _).mp (chainWord_mem hmem)
    refine ⟨chainWord bs, ⟨hadm.1, by omega⟩, ?_⟩
    rw [bracketWord_chain hmem, hmap]

/-- The bracket words of Order n + 1 are the bracket trees of length n + 1. -/
theorem image_bracketWord_admSet (n : ℕ) :
    bracketWord '' (admSet (n + 1) : Set (List Bool)) =
      {c | IsBracketTree c ∧ c.length = n + 1} := by
  ext c
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hA, hord⟩ := (mem_admSet _ s).mp (Finset.mem_coe.mp hs)
    exact ⟨isBracketTree_bracketWord n s hA hord, by rw [length_bracketWord, hord]⟩
  · rintro ⟨hc, hlen⟩
    obtain ⟨s, hs, rfl⟩ := exists_bracketWord_of_isBracketTree hc
    rw [length_bracketWord] at hlen
    exact ⟨s, Finset.mem_coe.mpr ((mem_admSet _ s).mpr ⟨hs.adm, hlen⟩), rfl⟩

-- The bracket words of Order 4.
set_option linter.hashCommand false in
#guard (admSet 4).image bracketWord = {[0, 0, 0, 4], [0, 0, 1, 3], [0, 1, 0, 3]}

end AcceleratedCollatz
