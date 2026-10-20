-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketParse

/-!
  Decoding bracket trees. `decodeNode f l` reads one node from the front of the
  list l, as `parseNode` does, and returns its word instead of its size: an entry
  c + 1 is the word 10, an entry 0 opens a node whose children are read by
  `decodeKids`, and the node's word is the chain word of its children's words
  (`chainWord`). `bracketDecode c` is the word of the node read from c. On bracket
  trees it inverts `bracketWord` (`bracketWord_bracketDecode`,
  `bracketDecode_bracketWord`, `invOn_bracketDecode`).
-/

namespace AcceleratedCollatz

mutual
/-- One node at the front of the list, with fuel: its word, the closes left for
    its ancestors, the rest. -/
def decodeNode : ℕ → List ℕ → List Bool × ℕ × List ℕ
  | 0, _ => ([], 0, [])
  | _ + 1, [] => ([], 0, [])
  | _ + 1, (c + 1) :: rest => ([true, false], c, rest)
  | f + 1, 0 :: rest => decodeKids f [] rest
/-- The further children of a node after children with words bs, with fuel: the
    word of the node, the closes left for its ancestors, the rest. -/
def decodeKids : ℕ → List (List Bool) → List ℕ → List Bool × ℕ × List ℕ
  | 0, _, _ => ([], 0, [])
  | f + 1, bs, l =>
    match decodeNode f l with
    | (b, 0, rest) => decodeKids f (bs ++ [b]) rest
    | (b, p + 1, rest) => (chainWord (bs ++ [b]), p, rest)
end

/-- Word of the node read from c. -/
def bracketDecode (c : List ℕ) : List Bool := (decodeNode (2 * c.length) c).1

theorem chainWord_nil : chainWord [] = [true, false] := by
  decide

/-- The chain word of chain blocks whose bracket words have valid lengths is a
    chain block; its bracket word is the node over these bracket words. -/
theorem bracketWord_chainWord_node {bs : List (List Bool)} (hbs : ∀ b ∈ bs, IsChainBlock b)
    (hv : ValidOrders ((bs.map bracketWord).map List.length)) :
    IsChainBlock (chainWord bs) ∧
      bracketWord (chainWord bs) = addLast 1 (0 :: (bs.map bracketWord).flatten) := by
  rw [map_length_map_bracketWord] at hv
  have hmem : bs ∈ chainBlocks (bs.map order).sum := ⟨hbs, hv, rfl⟩
  have hadm := (mem_admSet _ _).mp (chainWord_mem hmem)
  exact ⟨⟨hadm.1, by omega⟩, bracketWord_chain hmem⟩

/-- What the decoder reads from a bracket tree w with p added to its last entry,
    given fuel 2 |w| - 1: a chain block with bracket word w. -/
def DecodesTo (w : List ℕ) (s : List Bool) : Prop :=
  IsChainBlock s ∧ bracketWord s = w ∧ ∀ f p rest, 2 * w.length ≤ f + 1 →
    decodeNode f (addLast p w ++ rest) = (s, p, rest)

/-- The decoder reads a nonempty list of bracket trees as the further children of
    a node. -/
theorem decodeKids_complete : ∀ ws : List (List ℕ),
    (∀ w ∈ ws, IsBracketTree w) → (∀ w ∈ ws, ∃ s, DecodesTo w s) → ws ≠ [] →
    ∃ bs' : List (List Bool), (∀ b ∈ bs', IsChainBlock b) ∧ bs'.map bracketWord = ws ∧
      ∀ bs f p rest, 2 * (ws.map List.length).sum ≤ f →
        decodeKids f bs (addLast (p + 1) ws.flatten ++ rest) =
          (chainWord (bs ++ bs'), p, rest) := by
  intro ws
  induction ws with
  | nil =>
    intro _ _ h
    exact absurd rfl h
  | cons w ws ihws =>
    intro htree ih _
    obtain ⟨b, hb, hbw, hdec⟩ := ih w List.mem_cons_self
    have hwpos : 1 ≤ w.length :=
      List.length_pos_iff.mpr (ne_nil_of_isBracketTree (htree w List.mem_cons_self))
    rcases ws with _ | ⟨w2, ws'⟩
    · refine ⟨[b], ?_, by rw [List.map_singleton, hbw], ?_⟩
      · intro x hx
        rw [List.mem_singleton] at hx
        rw [hx]
        exact hb
      · intro bs f p rest hf
        rw [List.map_singleton, List.sum_singleton] at hf
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [List.flatten_singleton, decodeKids, hdec f' (p + 1) rest (by omega)]
    · have hne2 : w2 :: ws' ≠ [] := List.cons_ne_nil _ _
      have htree2 : ∀ x ∈ w2 :: ws', IsBracketTree x :=
        fun x hx => htree x (List.mem_cons_of_mem w hx)
      have hfl := flatten_ne_nil_of_trees hne2 htree2
      obtain ⟨bs2, hbs2, hmap2, hdec2⟩ :=
        ihws htree2 (fun x hx => ih x (List.mem_cons_of_mem w hx)) hne2
      refine ⟨b :: bs2, ?_, by rw [List.map_cons, hbw, hmap2], ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hb
        · exact hbs2 x hx'
      · intro bs f p rest hf
        rw [List.map_cons, List.sum_cons] at hf
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        have hp := hdec f' 0 (addLast (p + 1) (w2 :: ws').flatten ++ rest) (by omega)
        rw [addLast_zero] at hp
        rw [List.flatten_cons, addLast_append (p + 1) w hfl, List.append_assoc, decodeKids, hp]
        change decodeKids f' (bs ++ [b]) _ = _
        rw [hdec2 (bs ++ [b]) f' p rest (by omega), List.append_assoc, List.singleton_append]

/-- The decoder reads a bracket tree as a chain block with that bracket word. -/
theorem decodeNode_complete {w : List ℕ} (h : IsBracketTree w) : ∃ s, DecodesTo w s := by
  induction h with
  | node ws htree hv ih =>
    rcases ws with _ | ⟨w1, ws'⟩
    · have hnode := bracketWord_chainWord_node (bs := [])
        (fun b hb => absurd hb List.not_mem_nil) hv
      rw [chainWord_nil] at hnode
      refine ⟨[true, false], hnode.1, hnode.2, ?_⟩
      intro f p rest hf
      rw [length_node, List.map_nil, List.sum_nil] at hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      change decodeNode (f' + 1) ((1 + p) :: rest) = _
      rw [Nat.add_comm 1 p, decodeNode]
    · have hne : w1 :: ws' ≠ [] := List.cons_ne_nil _ _
      have hfl := flatten_ne_nil_of_trees hne htree
      obtain ⟨bs, hbs, hmap, hdec⟩ := decodeKids_complete (w1 :: ws') htree ih hne
      rw [← hmap] at hv
      have hnode := bracketWord_chainWord_node hbs hv
      rw [hmap] at hnode
      refine ⟨chainWord bs, hnode.1, hnode.2, ?_⟩
      intro f p rest hf
      rw [length_node] at hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [addLast_cons 1 0 hfl, addLast_cons p 0 (addLast_ne_nil 1 hfl), addLast_addLast,
        Nat.add_comm 1 p, List.cons_append, decodeNode, hdec [] f' p rest (by omega),
        List.nil_append]

/-- The decoded word of a bracket tree is a chain block: admissible, of Order ≥ 1. -/
theorem isChainBlock_bracketDecode {c : List ℕ} (h : IsBracketTree c) :
    IsChainBlock (bracketDecode c) := by
  obtain ⟨s, hs, _, hdec⟩ := decodeNode_complete h
  have hp := hdec (2 * c.length) 0 [] (by omega)
  rw [addLast_zero, List.append_nil] at hp
  unfold bracketDecode
  rw [hp]
  exact hs

/-- The bracket word of the decoded word of a bracket tree is the tree. -/
theorem bracketWord_bracketDecode {c : List ℕ} (h : IsBracketTree c) :
    bracketWord (bracketDecode c) = c := by
  obtain ⟨s, _, hw, hdec⟩ := decodeNode_complete h
  have hp := hdec (2 * c.length) 0 [] (by omega)
  rw [addLast_zero, List.append_nil] at hp
  unfold bracketDecode
  rw [hp]
  exact hw

/-- Decoding the bracket word of an admissible word of Order ≥ 1 gives the word. -/
theorem bracketDecode_bracketWord {s : List Bool} (hA : Admissible s) (hord : 1 ≤ order s) :
    bracketDecode (bracketWord s) = s := by
  have htree := isBracketTree_bracketWord (order s - 1) s hA (by omega)
  exact bracketWord_injective (isChainBlock_bracketDecode htree).adm hA
    (bracketWord_bracketDecode htree)

/-- `bracketDecode` and `bracketWord` are inverse to each other between the
    admissible words of Order n + 1 and the bracket trees of length n + 1. -/
theorem invOn_bracketDecode (n : ℕ) :
    Set.InvOn bracketDecode bracketWord (admSet (n + 1) : Set (List Bool))
      {c | IsBracketTree c ∧ c.length = n + 1} := by
  constructor
  · intro s hs
    obtain ⟨hA, hord⟩ := (mem_admSet _ s).mp (Finset.mem_coe.mp hs)
    exact bracketDecode_bracketWord hA (by omega)
  · intro c hc
    exact bracketWord_bracketDecode hc.1

/-- The decoded word of a bracket tree of length n + 1 has Order n + 1. -/
theorem bracketDecode_mem_admSet {n : ℕ} {c : List ℕ} (h : IsBracketTree c)
    (hlen : c.length = n + 1) : bracketDecode c ∈ admSet (n + 1) := by
  rw [mem_admSet]
  refine ⟨(isChainBlock_bracketDecode h).adm, ?_⟩
  rw [← length_bracketWord, bracketWord_bracketDecode h, hlen]

-- The words of Order 4.
set_option linter.hashCommand false in
#guard [[0, 0, 0, 4], [0, 0, 1, 3], [0, 1, 0, 3]].map bracketDecode =
  [[true, true, true, true, false, false, false],
   [true, true, true, false, true, false, false],
   [true, true, false, true, true, false, false]]

-- Decoding inverts `bracketWord` on the admissible words of Order 7.
set_option linter.hashCommand false in
#guard decide (∀ s ∈ admSet 7, bracketDecode (bracketWord s) = s)

end AcceleratedCollatz
