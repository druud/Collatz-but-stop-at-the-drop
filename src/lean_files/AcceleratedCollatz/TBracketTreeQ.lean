-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainEquivQ
import Mathlib.Data.Set.Card

/-!
  Trees of the q-family (odd q ≥ 3), with the Order-0 children marked. A tree is a leaf
  (an Order-0 block, the word [0]) or a node with a list of children (`ChainTreeQ`); its
  word is read in preorder: a leaf gives [0], a node gives 1 followed by the words of its
  children (`ChainTreeQ.word`). A node is an odd step with its brackets, its children are
  the blocks of the word its brackets span, so the Order of the word is the number of
  nodes. A tree is valid when at every node the Orders of the children keep the level
  above 1 before the last child and bring it below 1 after it (`ValidTreeQ`): only the
  Orders enter. The words of the valid trees are exactly the admissible words
  (`admissibleQ_word`, `exists_validTreeQ_word`), each of one tree
  (`word_inj_of_validTreeQ`), so the valid trees of Order n are counted by `admSetQ q n`
  (`word_bijOn_validTreesQ`, `ncard_validTreesQ`). For q = 3 a leaf can only be the last
  child of a node.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- A tree: a leaf (an Order-0 block) or a node with a list of children. -/
inductive ChainTreeQ where
  | leaf : ChainTreeQ
  | node : List ChainTreeQ → ChainTreeQ

/-- The word of a tree, read in preorder: [0] for a leaf, 1 and the children for a node. -/
def ChainTreeQ.word : ChainTreeQ → List Bool
  | .leaf => [false]
  | .node ts => true :: (ts.map ChainTreeQ.word).flatten

/-- A valid tree: at every node the Orders of the children keep the level above 1 before
    the last child and bring it below 1 after it. -/
inductive ValidTreeQ (q : ℕ) : ChainTreeQ → Prop
  | leaf : ValidTreeQ q .leaf
  | node (ts : List ChainTreeQ) (hts : ∀ t ∈ ts, ValidTreeQ q t)
      (hup : LevelUpQ q ((ts.map ChainTreeQ.word).map order).dropLast)
      (hend : ¬LevelUpQ q ((ts.map ChainTreeQ.word).map order)) :
      ValidTreeQ q (.node ts)

theorem ChainTreeQ.word_leaf : ChainTreeQ.leaf.word = [false] := by
  simp [ChainTreeQ.word]

theorem ChainTreeQ.word_node (ts : List ChainTreeQ) :
    (ChainTreeQ.node ts).word = true :: (ts.map ChainTreeQ.word).flatten := by
  simp [ChainTreeQ.word]

/-- The word of a valid tree is admissible. -/
theorem admissibleQ_word (hodd : Odd q) (hq : 3 ≤ q) {t : ChainTreeQ} (h : ValidTreeQ q t) :
    AdmissibleQ q t.word := by
  induction h with
  | leaf =>
    rw [ChainTreeQ.word_leaf]
    exact admissibleQ_singleton_false q
  | node ts _ hup hend ih =>
    rw [ChainTreeQ.word_node]
    have hadm : ∀ b ∈ ts.map ChainTreeQ.word, AdmissibleQ q b := by
      intro b hb
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
      exact ih t ht
    exact (admissibleQ_iff_chainQ hodd hq _ hadm).mpr ⟨hup, hend⟩

/-- An admissible word of Order 0 is [0]. -/
theorem eq_singleton_false_of_order_zero {s : List Bool} (hA : AdmissibleQ q s)
    (h0 : order s = 0) : s = [false] := by
  cases s with
  | nil =>
    exact absurd hA (not_admissibleQ_nil q)
  | cons b u =>
    have hb : b = false := by
      cases b
      · rfl
      · simp [order] at h0
    subst hb
    cases u with
    | nil =>
      rfl
    | cons c v =>
      exfalso
      have h := hA.prefix_gt 1 le_rfl (by simp)
      norm_num [seqProductQ, factorQ] at h

/-- Lists of words, each the word of a valid tree, are the words of a list of valid
    trees. -/
theorem exists_trees_of_forall {bs : List (List Bool)}
    (h : ∀ b ∈ bs, ∃ t, ValidTreeQ q t ∧ t.word = b) :
    ∃ ts : List ChainTreeQ, (∀ t ∈ ts, ValidTreeQ q t) ∧ ts.map ChainTreeQ.word = bs := by
  induction bs with
  | nil =>
    exact ⟨[], by simp, rfl⟩
  | cons b bs ih =>
    obtain ⟨t, ht, rfl⟩ := h b List.mem_cons_self
    obtain ⟨ts, hts, hmap⟩ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    refine ⟨t :: ts, ?_, by rw [List.map_cons, hmap]⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact ht
    · exact hts u hu'

/-- Every admissible word is the word of a valid tree. -/
theorem exists_validTreeQ_word (hodd : Odd q) (hq : 3 ≤ q) :
    ∀ (n : ℕ) (s : List Bool), s.length = n → AdmissibleQ q s →
      ∃ t, ValidTreeQ q t ∧ t.word = s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hA
    rcases Nat.eq_zero_or_pos (order s) with h0 | hpos
    · exact ⟨.leaf, .leaf, by rw [ChainTreeQ.word_leaf, eq_singleton_false_of_order_zero hA h0]⟩
    · obtain ⟨bs, hsplit, hup, hend⟩ :=
        (admissibleQ_iff_exists_chainQ hodd hq s).mp ⟨hA, hpos⟩
      have hkids : ∀ b ∈ bs, ∃ t, ValidTreeQ q t ∧ t.word = b := by
        intro b hb
        have hlt : b.length < n := by
          rw [← hn, hsplit.eq, List.length_cons]
          have := (List.sublist_flatten_of_mem hb).length_le
          omega
        exact ih b.length hlt b rfl (hsplit.adm b hb)
      obtain ⟨ts, hts, hmap⟩ := exists_trees_of_forall hkids
      have hup' : LevelUpQ q ((ts.map ChainTreeQ.word).map order).dropLast := by
        rw [hmap]
        exact hup
      have hend' : ¬LevelUpQ q ((ts.map ChainTreeQ.word).map order) := by
        rw [hmap]
        exact hend
      refine ⟨.node ts, .node ts hts hup' hend', ?_⟩
      rw [ChainTreeQ.word_node, hmap, hsplit.eq]

/-- Pointwise injectivity lifts to lists. -/
theorem map_inj_of_forall {α β : Type} {f : α → β} :
    ∀ (xs ys : List α), (∀ x ∈ xs, ∀ y ∈ ys, f x = f y → x = y) → xs.map f = ys.map f →
      xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by
    simp at h
  | _ :: _, [], _, h => by
    simp at h
  | x :: xs, y :: ys, hinj, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    rw [hinj x List.mem_cons_self y List.mem_cons_self h.1,
      map_inj_of_forall xs ys
        (fun x' hx' y' hy' => hinj x' (List.mem_cons_of_mem _ hx') y' (List.mem_cons_of_mem _ hy'))
        h.2]

/-- A valid tree is determined by its word. -/
theorem word_inj_of_validTreeQ (hodd : Odd q) (hq : 3 ≤ q) {t : ChainTreeQ}
    (h : ValidTreeQ q t) : ∀ t', ValidTreeQ q t' → t.word = t'.word → t = t' := by
  induction h with
  | leaf =>
    intro t' _ hw
    cases t' with
    | leaf =>
      rfl
    | node ts' =>
      rw [ChainTreeQ.word_leaf, ChainTreeQ.word_node] at hw
      simp at hw
  | node ts hts _ _ ih =>
    intro t' ht' hw
    cases t' with
    | leaf =>
      rw [ChainTreeQ.word_leaf, ChainTreeQ.word_node] at hw
      simp at hw
    | node ts' =>
      cases ht' with
      | node _ hts' _ _ =>
        rw [ChainTreeQ.word_node, ChainTreeQ.word_node, List.cons.injEq] at hw
        have hadm : ∀ b ∈ ts.map ChainTreeQ.word, AdmissibleQ q b := by
          intro b hb
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
          exact admissibleQ_word hodd hq (hts u hu)
        have hadm' : ∀ b ∈ ts'.map ChainTreeQ.word, AdmissibleQ q b := by
          intro b hb
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
          exact admissibleQ_word hodd hq (hts' u hu)
        have hmap := flatten_inj_of_admissibleQ _ _ hadm hadm' hw.2
        rw [map_inj_of_forall ts ts' (fun x hx y hy hxy => ih x hx y (hts' y hy) hxy) hmap]

/-- The valid trees of Order n: their word has Order n (one 1 per node). -/
def validTreesQ (q n : ℕ) : Set ChainTreeQ :=
  {t | ValidTreeQ q t ∧ order t.word = n}

/-- The word maps the valid trees of Order n one to one onto the admissible words of
    Order n. -/
theorem word_bijOn_validTreesQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    Set.BijOn ChainTreeQ.word (validTreesQ q n) (admSetQ q n : Set (List Bool)) := by
  refine ⟨fun t ht => ?_, fun t ht t' ht' hw => word_inj_of_validTreeQ hodd hq ht.1 t' ht'.1 hw,
    fun s hs => ?_⟩
  · rw [Finset.mem_coe, mem_admSetQ (by omega)]
    exact ⟨admissibleQ_word hodd hq ht.1, ht.2⟩
  · rw [Finset.mem_coe, mem_admSetQ (by omega)] at hs
    obtain ⟨t, ht, rfl⟩ := exists_validTreeQ_word hodd hq _ s rfl hs.1
    exact ⟨t, ⟨ht, hs.2⟩, rfl⟩

/-- The valid trees of Order n are as many as the admissible words of Order n. -/
theorem ncard_validTreesQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (validTreesQ q n).ncard = (admSetQ q n).card := by
  rw [← Set.ncard_coe_finset]
  exact (word_bijOn_validTreesQ hodd hq n).ncard_eq

-- q = 5: the word 11000 = 1 | 100 | 0 is the tree node [node [leaf, leaf], leaf].
set_option linter.hashCommand false in
#guard (ChainTreeQ.node [.node [.leaf, .leaf], .leaf]).word = [true, true, false, false, false]

end AcceleratedCollatz
