-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketTree

/-!
  Bracket trees by parsing. `parseNode f l` reads one node from the front of the
  list l: an entry c + 1 is a leaf that closes itself and leaves c closes for its
  ancestors; an entry 0 opens a node whose children are read by `parseKids`, one
  after another while the Orders read so far satisfy `LevelUp`; the child that
  leaves closes is the last one. Both return the size of the node, the closes left
  for the ancestors and the rest of the list; f is fuel, 2 |l| suffices.
  `isBracketTree c` accepts c iff it parses as one node with no closes and no rest
  left; it decides `IsBracketTree` (`isBracketTree_iff`).
-/

namespace AcceleratedCollatz

theorem addLast_zero : ∀ l : List ℕ, addLast 0 l = l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    change a :: addLast 0 (b :: l) = _
    rw [addLast_zero (b :: l)]

theorem addLast_append (p : ℕ) (u : List ℕ) {v : List ℕ} (hv : v ≠ []) :
    addLast p (u ++ v) = u ++ addLast p v := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    rw [List.cons_append, addLast_cons p a (List.append_ne_nil_of_right_ne_nil u hv), ih,
      List.cons_append]

theorem addLast_addLast (p q : ℕ) (l : List ℕ) :
    addLast p (addLast q l) = addLast (q + p) l := by
  rcases List.eq_nil_or_concat l with rfl | ⟨init, a, rfl⟩
  · rfl
  · rw [List.concat_eq_append, addLast_concat, addLast_concat, addLast_concat, Nat.add_assoc]

theorem addLast_ne_nil (p : ℕ) {l : List ℕ} (hl : l ≠ []) : addLast p l ≠ [] := by
  intro h
  have hlen := length_addLast p l
  rw [h, List.length_nil] at hlen
  exact hl (List.length_eq_zero_iff.mp hlen.symm)

theorem ne_nil_of_isBracketTree {w : List ℕ} (h : IsBracketTree w) : w ≠ [] := by
  cases h with
  | node ws _ _ => exact addLast_ne_nil 1 (List.cons_ne_nil _ _)

/-- Size of a node: 1 plus the sizes of its children. -/
theorem length_node (ws : List (List ℕ)) :
    (addLast 1 (0 :: ws.flatten)).length = 1 + (ws.map List.length).sum := by
  rw [length_addLast, List.length_cons, List.length_flatten]
  omega

theorem flatten_ne_nil_of_trees {ws : List (List ℕ)} (hne : ws ≠ [])
    (h : ∀ w ∈ ws, IsBracketTree w) : ws.flatten ≠ [] := by
  obtain ⟨w, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.flatten_cons]
  exact List.append_ne_nil_of_left_ne_nil (ne_nil_of_isBracketTree (h w List.mem_cons_self)) _

mutual
/-- One node at the front of the list, with fuel: its size, the closes left for
    its ancestors, the rest. -/
def parseNode : ℕ → List ℕ → Option (ℕ × ℕ × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, (c + 1) :: rest => some (1, c, rest)
  | f + 1, 0 :: rest => parseKids f [] rest
/-- The further children of a node after children of sizes os, with fuel: the size
    of the node, the closes left for its ancestors, the rest. -/
def parseKids : ℕ → List ℕ → List ℕ → Option (ℕ × ℕ × List ℕ)
  | 0, _, _ => none
  | f + 1, os, l =>
    if LevelUp os then
      match parseNode f l with
      | some (o, 0, rest) => parseKids f (os ++ [o]) rest
      | some (o, p + 1, rest) => some (1 + os.sum + o, p, rest)
      | none => none
    else none
end

/-- Bracket-tree test: c parses as one node, no closes and no rest left. -/
def isBracketTree (c : List ℕ) : Bool :=
  decide (parseNode (2 * c.length) c = some (c.length, 0, []))

/-- What the parser accepts: a bracket tree with p added to its last entry, and for
    the children a nonempty list of bracket trees with p + 1 added at the end. -/
theorem parse_sound : ∀ f : ℕ,
    (∀ l o p rest, parseNode f l = some (o, p, rest) →
      ∃ w, IsBracketTree w ∧ w.length = o ∧ l = addLast p w ++ rest) ∧
    (∀ os l o p rest, parseKids f os l = some (o, p, rest) →
      ∃ ws, ws ≠ [] ∧ (∀ w ∈ ws, IsBracketTree w) ∧ LevelUp os ∧
        (∀ i, 1 ≤ i → i < ws.length → LevelUp (os ++ (ws.map List.length).take i)) ∧
        o = 1 + os.sum + (ws.map List.length).sum ∧
        l = addLast (p + 1) ws.flatten ++ rest) := by
  intro f
  induction f with
  | zero =>
    constructor
    · intro l o p rest h
      simp [parseNode] at h
    · intro os l o p rest h
      simp [parseKids] at h
  | succ f ih =>
    obtain ⟨ihN, ihK⟩ := ih
    constructor
    · intro l o p rest h
      rcases l with _ | ⟨c, l'⟩
      · simp [parseNode] at h
      rcases c with _ | c
      · rw [parseNode] at h
        obtain ⟨ws, hne, htree, _, hval, ho, hl⟩ := ihK [] l' o p rest h
        have hfl := flatten_ne_nil_of_trees hne htree
        refine ⟨addLast 1 (0 :: ws.flatten), IsBracketTree.node ws htree ?_, ?_, ?_⟩
        · intro i hi hil
          rw [List.length_map] at hil
          have hi' := hval i hi hil
          rw [List.nil_append] at hi'
          exact hi'
        · rw [length_node, ho, List.sum_nil]
          omega
        · rw [hl, addLast_cons 1 0 hfl, addLast_cons p 0 (addLast_ne_nil 1 hfl),
            addLast_addLast, Nat.add_comm 1 p]
          rfl
      · rw [parseNode] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have ht : IsBracketTree [1] :=
          IsBracketTree.node [] (fun w hw => absurd hw List.not_mem_nil)
            (fun i _ hil => absurd hil (Nat.not_lt_zero i))
        refine ⟨[1], ht, rfl, ?_⟩
        change (c + 1) :: l' = [1 + c] ++ l'
        rw [Nat.add_comm 1 c]
        rfl
    · intro os l o p rest h
      rw [parseKids] at h
      by_cases hL : LevelUp os
      · simp only [hL, ↓reduceIte] at h
        cases hpn : parseNode f l with
        | none =>
          rw [hpn] at h
          simp at h
        | some r =>
          obtain ⟨o1, p1, rest1⟩ := r
          rw [hpn] at h
          obtain ⟨w1, hw1, hlen1, hl1⟩ := ihN l o1 p1 rest1 hpn
          cases p1 with
          | zero =>
            obtain ⟨ws, hne, htree, hLup, hval, ho, hl⟩ := ihK (os ++ [o1]) rest1 o p rest h
            refine ⟨w1 :: ws, List.cons_ne_nil _ _, ?_, hL, ?_, ?_, ?_⟩
            · intro w hw
              rcases List.mem_cons.mp hw with rfl | hw'
              · exact hw1
              · exact htree w hw'
            · intro i hi hil
              obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
              rw [List.length_cons] at hil
              rw [List.map_cons, List.take_succ_cons, hlen1]
              rcases Nat.eq_zero_or_pos i' with rfl | hpos
              · rw [List.take_zero]
                exact hLup
              · have hi' := hval i' hpos (by omega)
                rw [List.append_assoc, List.singleton_append] at hi'
                exact hi'
            · rw [ho, List.map_cons, List.sum_cons, List.sum_append, List.sum_singleton, hlen1]
              omega
            · rw [hl1, addLast_zero, hl, List.flatten_cons,
                addLast_append (p + 1) w1 (flatten_ne_nil_of_trees hne htree), List.append_assoc]
          | succ p1 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨[w1], List.cons_ne_nil _ _, ?_, hL, ?_, ?_, ?_⟩
            · intro w hw
              rw [List.mem_singleton] at hw
              rw [hw]
              exact hw1
            · intro i hi hil
              rw [List.length_singleton] at hil
              omega
            · rw [List.map_singleton, List.sum_singleton, hlen1]
            · rw [hl1, List.flatten_singleton]
      · simp only [hL, ↓reduceIte] at h
        simp at h

/-- The parser reads a nonempty list of bracket trees with valid Orders as the
    further children of a node. -/
theorem parseKids_complete : ∀ ws : List (List ℕ),
    (∀ w ∈ ws, IsBracketTree w) →
    (∀ w ∈ ws, ∀ f p rest, 2 * w.length ≤ f + 1 →
      parseNode f (addLast p w ++ rest) = some (w.length, p, rest)) →
    ws ≠ [] → ∀ os f p rest, LevelUp os →
    (∀ i, 1 ≤ i → i < ws.length → LevelUp (os ++ (ws.map List.length).take i)) →
    2 * (ws.map List.length).sum ≤ f →
    parseKids f os (addLast (p + 1) ws.flatten ++ rest) =
      some (1 + os.sum + (ws.map List.length).sum, p, rest) := by
  intro ws
  induction ws with
  | nil =>
    intro _ _ h
    exact absurd rfl h
  | cons w ws ihws =>
    intro htree ih _ os f p rest hL hval hf
    have hwpos : 1 ≤ w.length :=
      List.length_pos_iff.mpr (ne_nil_of_isBracketTree (htree w List.mem_cons_self))
    rw [List.map_cons, List.sum_cons] at hf ⊢
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [parseKids]
    simp only [hL, ↓reduceIte]
    rcases ws with _ | ⟨w2, ws'⟩
    · have hp := ih w List.mem_cons_self f' (p + 1) rest (by omega)
      rw [List.flatten_singleton, hp, List.map_nil, List.sum_nil]
      rfl
    · have hne2 : w2 :: ws' ≠ [] := List.cons_ne_nil _ _
      have htree2 : ∀ x ∈ w2 :: ws', IsBracketTree x :=
        fun x hx => htree x (List.mem_cons_of_mem w hx)
      have hfl := flatten_ne_nil_of_trees hne2 htree2
      have hp := ih w List.mem_cons_self f' 0 (addLast (p + 1) (w2 :: ws').flatten ++ rest)
        (by omega)
      rw [addLast_zero] at hp
      have hup : LevelUp (os ++ [w.length]) := hval 1 le_rfl (by simp)
      have hval2 : ∀ i, 1 ≤ i → i < (w2 :: ws').length →
          LevelUp ((os ++ [w.length]) ++ ((w2 :: ws').map List.length).take i) := by
        intro i hi hil
        have h1 := hval (i + 1) (by omega) (by simpa using hil)
        rw [List.map_cons, List.take_succ_cons] at h1
        rw [List.append_assoc, List.singleton_append]
        exact h1
      have hrec := ihws htree2 (fun x hx => ih x (List.mem_cons_of_mem w hx)) hne2
        (os ++ [w.length]) f' p rest hup hval2 (by omega)
      have hsum : 1 + (os ++ [w.length]).sum + ((w2 :: ws').map List.length).sum =
          1 + os.sum + (w.length + ((w2 :: ws').map List.length).sum) := by
        rw [List.sum_append, List.sum_singleton]
        omega
      rw [List.flatten_cons, addLast_append (p + 1) w hfl, List.append_assoc, hp]
      change parseKids f' (os ++ [w.length]) _ = _
      rw [hrec, hsum]

/-- The parser reads a bracket tree with p added to its last entry, given fuel
    2 |w| - 1. -/
theorem parseNode_complete {w : List ℕ} (h : IsBracketTree w) :
    ∀ f p rest, 2 * w.length ≤ f + 1 →
      parseNode f (addLast p w ++ rest) = some (w.length, p, rest) := by
  induction h with
  | node ws htree hv ih =>
    intro f p rest hf
    rw [length_node] at hf ⊢
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rcases ws with _ | ⟨w1, ws'⟩
    · change parseNode (f' + 1) ((1 + p) :: rest) = _
      rw [Nat.add_comm 1 p, parseNode]
      rfl
    · have hne : w1 :: ws' ≠ [] := List.cons_ne_nil _ _
      have hfl := flatten_ne_nil_of_trees hne htree
      have hval : ∀ i, 1 ≤ i → i < (w1 :: ws').length →
          LevelUp ([] ++ ((w1 :: ws').map List.length).take i) := by
        intro i hi hil
        rw [List.nil_append]
        apply hv i hi
        rw [List.length_map]
        exact hil
      have hk := parseKids_complete (w1 :: ws') htree ih hne [] f' p rest (by decide) hval
        (by omega)
      rw [addLast_cons 1 0 hfl, addLast_cons p 0 (addLast_ne_nil 1 hfl), addLast_addLast,
        Nat.add_comm 1 p, List.cons_append, parseNode, hk, List.sum_nil, Nat.add_zero]

/-- `isBracketTree` decides `IsBracketTree`. -/
theorem isBracketTree_iff (c : List ℕ) : isBracketTree c = true ↔ IsBracketTree c := by
  unfold isBracketTree
  rw [decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨w, hw, _, hc⟩ := (parse_sound _).1 c _ _ _ h
    rw [addLast_zero, List.append_nil] at hc
    rw [hc]
    exact hw
  · intro h
    have hp := parseNode_complete h (2 * c.length) 0 [] (by omega)
    rw [addLast_zero, List.append_nil] at hp
    exact hp

instance : DecidablePred IsBracketTree :=
  fun c => decidable_of_iff _ (isBracketTree_iff c)

-- Two valid children of Order 1; a third child of Order 1 is not valid.
set_option linter.hashCommand false in
#guard isBracketTree [0, 1, 2] && !isBracketTree [0, 1, 1, 2]

-- The bracket words of Order 6 parse.
set_option linter.hashCommand false in
#guard decide (∀ c ∈ (admSet 6).image bracketWord, isBracketTree c)

end AcceleratedCollatz
