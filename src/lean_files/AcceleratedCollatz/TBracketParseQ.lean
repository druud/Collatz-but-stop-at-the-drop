-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketTreeQ

/-!
  Trees of the q-family (odd q ≥ 3) by parsing their words. `parseNodeQ q f l` reads one
  tree from the front of the list l: a 0 is a leaf; a 1 opens a node whose children are
  read by `parseKidsQ`, one after another while the Orders read so far keep the level
  above 1; the child that brings it below 1 is the last one. Both return the tree and the
  rest of the list; f is fuel, 2 |l| suffices. `parseTreeQ q s` is the tree that reads all
  of s, and it is a valid tree of word s exactly when one exists (`parseTreeQ_eq_some_iff`):
  the parser decides admissibility (`isTreeWordQ_iff`). `ChainTreeQ.validQ` checks a given
  tree node by node and decides `ValidTreeQ` (`validQ_iff`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- The Orders of the words of a list of trees. -/
def ChainTreeQ.orders (ts : List ChainTreeQ) : List ℕ :=
  (ts.map ChainTreeQ.word).map order

theorem ChainTreeQ.orders_append (ts us : List ChainTreeQ) :
    ChainTreeQ.orders (ts ++ us) = ChainTreeQ.orders ts ++ ChainTreeQ.orders us := by
  simp [ChainTreeQ.orders]

theorem ChainTreeQ.length_word_pos : ∀ t : ChainTreeQ, 0 < t.word.length
  | .leaf => by
    simp [ChainTreeQ.word]
  | .node ts => by
    simp [ChainTreeQ.word]

theorem ChainTreeQ.length_word_node (ts : List ChainTreeQ) :
    (ChainTreeQ.node ts).word.length = 1 + ((ts.map ChainTreeQ.word).map List.length).sum := by
  rw [ChainTreeQ.word_node, List.length_cons, List.length_flatten]
  omega

mutual
/-- One tree at the front of the list, with fuel: the tree and the rest. -/
def parseNodeQ (q : ℕ) : ℕ → List Bool → Option (ChainTreeQ × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some (.leaf, rest)
  | f + 1, true :: rest => parseKidsQ q f [] rest
/-- The further children of a node after the children ts, with fuel: the node and the
    rest. -/
def parseKidsQ (q : ℕ) : ℕ → List ChainTreeQ → List Bool → Option (ChainTreeQ × List Bool)
  | 0, _, _ => none
  | f + 1, ts, l =>
    match parseNodeQ q f l with
    | some (t, rest) =>
      if LevelUpQ q (ChainTreeQ.orders (ts ++ [t])) then parseKidsQ q f (ts ++ [t]) rest
      else some (.node (ts ++ [t]), rest)
    | none => none
end

/-- What the parser returns is a valid tree whose word was read from the front. -/
theorem parseQ_sound (hq : 3 ≤ q) : ∀ f : ℕ,
    (∀ l t rest, parseNodeQ q f l = some (t, rest) → ValidTreeQ q t ∧ l = t.word ++ rest) ∧
    (∀ ts l t rest, (∀ u ∈ ts, ValidTreeQ q u) → LevelUpQ q (ChainTreeQ.orders ts) →
      parseKidsQ q f ts l = some (t, rest) →
        ValidTreeQ q t ∧ true :: ((ts.map ChainTreeQ.word).flatten ++ l) = t.word ++ rest) := by
  intro f
  induction f with
  | zero =>
    constructor
    · intro l t rest h
      simp [parseNodeQ] at h
    · intro ts l t rest _ _ h
      simp [parseKidsQ] at h
  | succ f ih =>
    obtain ⟨ihN, ihK⟩ := ih
    constructor
    · intro l t rest h
      rcases l with _ | ⟨b, l'⟩
      · simp [parseNodeQ] at h
      cases b with
      | false =>
        rw [parseNodeQ] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨.leaf, ?_⟩
        rw [ChainTreeQ.word_leaf, List.singleton_append]
      | true =>
        rw [parseNodeQ] at h
        have hnil : ∀ u ∈ ([] : List ChainTreeQ), ValidTreeQ q u := by
          intro u hu
          exact absurd hu List.not_mem_nil
        obtain ⟨hv, hw⟩ := ihK [] l' t rest hnil (levelUpQ_nil hq) h
        refine ⟨hv, ?_⟩
        rw [← hw, List.map_nil, List.flatten_nil, List.nil_append]
    · intro ts l t rest hts hL h
      rw [parseKidsQ] at h
      cases hpn : parseNodeQ q f l with
      | none =>
        rw [hpn] at h
        simp at h
      | some r =>
        obtain ⟨t1, rest1⟩ := r
        rw [hpn] at h
        obtain ⟨hv1, hl1⟩ := ihN l t1 rest1 hpn
        have hts1 : ∀ u ∈ ts ++ [t1], ValidTreeQ q u := by
          intro u hu
          rcases List.mem_append.mp hu with hu' | hu'
          · exact hts u hu'
          · rw [List.mem_singleton] at hu'
            rw [hu']
            exact hv1
        have hflat : true :: ((ts.map ChainTreeQ.word).flatten ++ l) =
            true :: (((ts ++ [t1]).map ChainTreeQ.word).flatten ++ rest1) := by
          rw [hl1, List.map_append, List.flatten_append, List.map_singleton,
            List.flatten_singleton, List.append_assoc]
        by_cases hL1 : LevelUpQ q (ChainTreeQ.orders (ts ++ [t1]))
        · simp only [hL1, ↓reduceIte] at h
          obtain ⟨hv, hw⟩ := ihK (ts ++ [t1]) rest1 t rest hts1 hL1 h
          exact ⟨hv, by rw [hflat, hw]⟩
        · simp only [hL1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hup : LevelUpQ q
              (((ts ++ [t1]).map ChainTreeQ.word).map order).dropLast := by
            change LevelUpQ q (ChainTreeQ.orders (ts ++ [t1])).dropLast
            rw [ChainTreeQ.orders_append]
            change LevelUpQ q (ChainTreeQ.orders ts ++ [order t1.word]).dropLast
            rw [List.dropLast_concat]
            exact hL
          refine ⟨.node (ts ++ [t1]) hts1 hup hL1, ?_⟩
          rw [hflat, ChainTreeQ.word_node, List.cons_append]

/-- The parser reads a nonempty list of valid trees as the further children of a node,
    when the level stays above 1 before the last one and falls below 1 after it. -/
theorem parseKidsQ_complete (hq : 3 ≤ q) : ∀ us : List ChainTreeQ,
    (∀ u ∈ us, ∀ f rest, 2 * u.word.length ≤ f + 1 →
      parseNodeQ q f (u.word ++ rest) = some (u, rest)) →
    us ≠ [] → ∀ ts f rest, LevelUpQ q (ChainTreeQ.orders (ts ++ us)).dropLast →
    ¬LevelUpQ q (ChainTreeQ.orders (ts ++ us)) →
    2 * ((us.map ChainTreeQ.word).map List.length).sum ≤ f →
    parseKidsQ q f ts ((us.map ChainTreeQ.word).flatten ++ rest) =
      some (.node (ts ++ us), rest) := by
  intro us
  induction us with
  | nil =>
    intro _ h
    exact absurd rfl h
  | cons u us ihus =>
    intro ih _ ts f rest hup hend hf
    have hupos := ChainTreeQ.length_word_pos u
    rw [List.map_cons, List.map_cons, List.sum_cons] at hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hp := ih u List.mem_cons_self f' ((us.map ChainTreeQ.word).flatten ++ rest)
      (by omega)
    rw [List.map_cons, List.flatten_cons, List.append_assoc, parseKidsQ, hp]
    rcases us with _ | ⟨u2, us'⟩
    · have hend' : ¬LevelUpQ q (ChainTreeQ.orders (ts ++ [u])) := hend
      simp only [hend', ↓reduceIte, List.map_nil, List.flatten_nil, List.nil_append]
    · have hne2 : u2 :: us' ≠ [] := List.cons_ne_nil _ _
      have hsplit : ts ++ u :: u2 :: us' = (ts ++ [u]) ++ u2 :: us' := by
        rw [List.append_assoc, List.singleton_append]
      have hords2 : ChainTreeQ.orders (u2 :: us') ≠ [] := by
        simp [ChainTreeQ.orders]
      have hup1 : LevelUpQ q (ChainTreeQ.orders (ts ++ [u])) := by
        rw [hsplit, ChainTreeQ.orders_append, List.dropLast_append_of_ne_nil hords2] at hup
        exact levelUpQ_of_append hq _ _ hup
      rw [hsplit] at hup hend
      have hf2 : 2 * (((u2 :: us').map ChainTreeQ.word).map List.length).sum ≤ f' := by
        rw [List.map_cons, List.map_cons, List.sum_cons] at hf ⊢
        omega
      have hrec := ihus (fun x hx => ih x (List.mem_cons_of_mem u hx)) hne2 (ts ++ [u]) f' rest
        hup hend hf2
      simp only [hup1, ↓reduceIte]
      rw [hrec, hsplit]

/-- The parser reads a valid tree from the front of a list, given fuel 2 |word| - 1. -/
theorem parseNodeQ_complete (hq : 3 ≤ q) {t : ChainTreeQ} (h : ValidTreeQ q t) :
    ∀ f rest, 2 * t.word.length ≤ f + 1 → parseNodeQ q f (t.word ++ rest) = some (t, rest) := by
  induction h with
  | leaf =>
    intro f rest hf
    rw [ChainTreeQ.word_leaf] at hf ⊢
    rw [List.length_singleton] at hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rfl
  | node ts _ hup hend ih =>
    intro f rest hf
    rw [ChainTreeQ.length_word_node] at hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hne : ts ≠ [] := by
      rintro rfl
      exact hend (levelUpQ_nil hq)
    have hk := parseKidsQ_complete hq ts ih hne [] f' rest hup hend (by omega)
    rw [ChainTreeQ.word_node, List.cons_append, parseNodeQ, hk, List.nil_append]

/-- The tree that reads all of s, if any. -/
def parseTreeQ (q : ℕ) (s : List Bool) : Option ChainTreeQ :=
  match parseNodeQ q (2 * s.length) s with
  | some (t, []) => some t
  | _ => none

/-- `parseTreeQ` finds the valid tree of word s, and only that. -/
theorem parseTreeQ_eq_some_iff (hq : 3 ≤ q) (s : List Bool) (t : ChainTreeQ) :
    parseTreeQ q s = some t ↔ ValidTreeQ q t ∧ t.word = s := by
  constructor
  · intro h
    unfold parseTreeQ at h
    cases hp : parseNodeQ q (2 * s.length) s with
    | none =>
      rw [hp] at h
      simp at h
    | some r =>
      obtain ⟨t', rest⟩ := r
      rw [hp] at h
      cases rest with
      | nil =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hv, hs⟩ := (parseQ_sound hq _).1 s t' [] hp
        rw [List.append_nil] at hs
        exact ⟨hv, hs.symm⟩
      | cons b rest' =>
        simp at h
  · rintro ⟨hv, rfl⟩
    have hp := parseNodeQ_complete hq hv (2 * t.word.length) [] (by omega)
    rw [List.append_nil] at hp
    unfold parseTreeQ
    rw [hp]

/-- Word test: s is the word of a valid tree. -/
def isTreeWordQ (q : ℕ) (s : List Bool) : Bool :=
  (parseTreeQ q s).isSome

/-- The parser decides admissibility. -/
theorem isTreeWordQ_iff (hodd : Odd q) (hq : 3 ≤ q) (s : List Bool) :
    isTreeWordQ q s = true ↔ AdmissibleQ q s := by
  unfold isTreeWordQ
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hv, rfl⟩ := (parseTreeQ_eq_some_iff hq s t).mp ht
    exact admissibleQ_word hodd hq hv
  · intro hA
    obtain ⟨t, hv, hw⟩ := exists_validTreeQ_word hodd hq _ s rfl hA
    rw [(parseTreeQ_eq_some_iff hq s t).mpr ⟨hv, hw⟩]
    rfl

/-- Validity check of a given tree, node by node. -/
def ChainTreeQ.validQ (q : ℕ) : ChainTreeQ → Bool
  | .leaf => true
  | .node ts =>
    ts.attach.all (fun ⟨t, _⟩ => t.validQ q) &&
      decide (LevelUpQ q (ChainTreeQ.orders ts).dropLast) &&
      !decide (LevelUpQ q (ChainTreeQ.orders ts))

/-- `ChainTreeQ.validQ` decides `ValidTreeQ`. -/
theorem ChainTreeQ.validQ_iff : ∀ t : ChainTreeQ, t.validQ q = true ↔ ValidTreeQ q t
  | .leaf => by
    simp only [ChainTreeQ.validQ, true_iff]
    exact .leaf
  | .node ts => by
    have ih : ∀ t ∈ ts, t.validQ q = true ↔ ValidTreeQ q t := fun t _ => ChainTreeQ.validQ_iff t
    rw [ChainTreeQ.validQ]
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_attach, true_implies,
      Subtype.forall, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · rintro ⟨⟨hall, hup⟩, hend⟩
      exact .node ts (fun t ht => (ih t ht).mp (hall t ht)) hup hend
    · intro h
      cases h with
      | node _ hts hup hend =>
        exact ⟨⟨fun t ht => (ih t ht).mpr (hts t ht), hup⟩, hend⟩

instance : DecidablePred (ValidTreeQ q) :=
  fun t => decidable_of_iff _ (ChainTreeQ.validQ_iff t)

-- q = 5: 11000 is the tree node [node [leaf, leaf], leaf]; 1100 has no tree.
set_option linter.hashCommand false in
#guard (match parseTreeQ 5 [true, true, false, false, false] with
  | some (.node [.node [.leaf, .leaf], .leaf]) => true
  | _ => false) && (parseTreeQ 5 [true, true, false, false]).isNone

-- q = 5: the parser accepts exactly the admissible words of Orders 1 to 4.
set_option linter.hashCommand false in
#guard (List.range 4).all fun n =>
  ((allBits (p2Q 5 (n + 1))).filter (isTreeWordQ 5)).length = (admSetQ 5 (n + 1)).card

end AcceleratedCollatz
