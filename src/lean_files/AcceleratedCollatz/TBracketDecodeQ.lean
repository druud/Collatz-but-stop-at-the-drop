-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketChainQ
import AcceleratedCollatz.TBracketParse
import AcceleratedCollatz.TBracketParseQ

/-!
  Trees of the q-family (odd q ≥ 3) from their bracket words, by Orders only. After children
  of Orders os, bracket m of a node is open when 2^(m + 1 + P) ≤ q^(1 + O), O the sum of os
  and P the sum of their p2Q (`openQ`); a child closes the brackets it leaves shut. The
  encoder `encQ` writes one entry per node: the closes of the brackets of every node in the
  column of its 1, the closes of a child added to the last entry written before it
  (`encKidsQ`). The decoder `decNodeQ` reads a tree with a counter r of the closes left in
  the current column: r > 0 is a leaf, r = 0 reads the next entry as a node; `decKidsQ`
  adds children while the level stays above 1, subtracting their closes from r. A leaf
  child closes at least one bracket (`one_le_closeQ_leaf`), and the decoder inverts the
  encoder on every valid tree with a node at the root (`decodeQ_encQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Brackets of a node still open after children of Orders os. -/
def openQ (q : ℕ) (os : List ℕ) : ℕ :=
  ((Finset.range (bracketsQ q)).filter
    (fun m => 2 ^ (m + 1 + (os.map (p2Q q)).sum) ≤ q ^ (1 + os.sum))).card

/-- Brackets of a node closed by its next child, of Order o, after children of Orders os. -/
def closeQ (q : ℕ) (os : List ℕ) (o : ℕ) : ℕ := openQ q os - openQ q (os ++ [o])

mutual
/-- Bracket word of a tree from the Orders of its nodes. -/
def encQ (q : ℕ) : ChainTreeQ → List ℕ
  | .leaf => []
  | .node ts => (encKidsQ q [] ts).1 :: (encKidsQ q [] ts).2
/-- Children after children of Orders os: the closes in the current column before the
    first node child, and the entries of the node children. -/
def encKidsQ (q : ℕ) (os : List ℕ) : List ChainTreeQ → ℕ × List ℕ
  | [] => (0, [])
  | .leaf :: us =>
    (closeQ q os 0 + (encKidsQ q (os ++ [0]) us).1, (encKidsQ q (os ++ [0]) us).2)
  | .node vs :: us =>
    (0, addLast (closeQ q os (order (ChainTreeQ.node vs).word) +
        (encKidsQ q (os ++ [order (ChainTreeQ.node vs).word]) us).1) (encQ q (.node vs)) ++
      (encKidsQ q (os ++ [order (ChainTreeQ.node vs).word]) us).2)
end

mutual
/-- One tree from the front of the entries, r closes left in the current column, with
    fuel: the tree, the closes left after it, the rest. -/
def decNodeQ (q : ℕ) : ℕ → ℕ → List ℕ → Option (ChainTreeQ × ℕ × List ℕ)
  | 0, _, _ => none
  | _ + 1, r + 1, l => some (.leaf, r + 1, l)
  | _ + 1, 0, [] => none
  | f + 1, 0, c :: l => decKidsQ q f [] c l
/-- The further children of a node after the children ts, with fuel: the node, the
    closes left after it, the rest. -/
def decKidsQ (q : ℕ) : ℕ → List ChainTreeQ → ℕ → List ℕ → Option (ChainTreeQ × ℕ × List ℕ)
  | 0, _, _, _ => none
  | f + 1, ts, r, l =>
    match decNodeQ q f r l with
    | some (t, r1, l1) =>
      if closeQ q (ChainTreeQ.orders ts) (order t.word) ≤ r1 then
        if LevelUpQ q (ChainTreeQ.orders (ts ++ [t])) then
          decKidsQ q f (ts ++ [t]) (r1 - closeQ q (ChainTreeQ.orders ts) (order t.word)) l1
        else some (.node (ts ++ [t]), r1 - closeQ q (ChainTreeQ.orders ts) (order t.word), l1)
      else none
    | none => none
end

/-- The tree of a bracket word, if the entries read as one. -/
def decodeQ (q : ℕ) (c : List ℕ) : Option ChainTreeQ :=
  match decNodeQ q (2 * p2Q q c.length) 0 c with
  | some (t, 0, []) => some t
  | _ => none

theorem ChainTreeQ.orders_cons (t : ChainTreeQ) (ts : List ChainTreeQ) :
    ChainTreeQ.orders (t :: ts) = order t.word :: ChainTreeQ.orders ts := by
  simp [ChainTreeQ.orders]

theorem ChainTreeQ.orders_concat (ts : List ChainTreeQ) (t : ChainTreeQ) :
    ChainTreeQ.orders (ts ++ [t]) = ChainTreeQ.orders ts ++ [order t.word] := by
  rw [ChainTreeQ.orders_append]
  simp [ChainTreeQ.orders]

theorem order_word_leaf : order ChainTreeQ.leaf.word = 0 := by
  simp [ChainTreeQ.word, order]

theorem encQ_node_ne_nil (ts : List ChainTreeQ) : encQ q (.node ts) ≠ [] := by
  simp [encQ]

/-- Halving a level that lies in [2^(1+P), 2^(e+1+P)) shuts one of e thresholds. -/
theorem card_filter_succ_lt {e P X : ℕ} (hlow : 2 ^ (1 + P) < X) (hcap : X < 2 ^ (e + 1 + P)) :
    ((Finset.range e).filter (fun m => 2 ^ (m + 1 + (P + 1)) ≤ X)).card <
      ((Finset.range e).filter (fun m => 2 ^ (m + 1 + P) ≤ X)).card := by
  have hex : ∃ j, X < 2 ^ (j + 2 + P) := ⟨e, by
    have : 2 ^ (e + 1 + P) ≤ 2 ^ (e + 2 + P) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega⟩
  have hjspec : X < 2 ^ (Nat.find hex + 2 + P) := Nat.find_spec hex
  have hjle : 2 ^ (Nat.find hex + 1 + P) ≤ X := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]
      exact hlow.le
    · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [not_lt] at hmin
      have he : Nat.find hex - 1 + 2 + P = Nat.find hex + 1 + P := by
        omega
      rw [he] at hmin
      exact hmin
  have hje : Nat.find hex < e := by
    by_contra hcon
    have : 2 ^ (e + 1 + P) ≤ 2 ^ (Nat.find hex + 1 + P) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨Nat.find hex, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hje, hjle⟩
    · rw [Finset.mem_filter, not_and, not_le]
      intro _
      have he : Nat.find hex + 1 + (P + 1) = Nat.find hex + 2 + P := by
        omega
      rw [he]
      exact hjspec
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hm.2⟩

/-- After children with the level above 1, a leaf closes a bracket. -/
theorem one_le_closeQ_leaf (hq : 3 ≤ q) {os : List ℕ} (hup : LevelUpQ q os) :
    1 ≤ closeQ q os 0 := by
  unfold closeQ openQ
  have hP' : ((os ++ [0]).map (p2Q q)).sum = (os.map (p2Q q)).sum + 1 := by
    rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have h0 : p2Q q 0 = 1 := by
      simp [p2Q]
    rw [h0]
  have hO' : (os ++ [0]).sum = os.sum := by
    simp
  rw [hP', hO']
  have hcap : q ^ (1 + os.sum) < 2 ^ (bracketsQ q + 1 + (os.map (p2Q q)).sum) := by
    have hq1 : q < 2 ^ (bracketsQ q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
    have hs := q_pow_sum_le hq os
    rw [pow_add, pow_one, pow_add 2 (bracketsQ q + 1)]
    exact Nat.mul_lt_mul_of_lt_of_le hq1 hs (by positivity)
  have := card_filter_succ_lt hup hcap
  omega

/-- A carry x on the last entry of (a + b) :: L moves to b :: L with a taken off the head. -/
theorem addLast_sub_head {x a b r : ℕ} {L M : List ℕ}
    (h : addLast x ((a + b) :: L) = r :: M) : addLast x (b :: L) = (r - a) :: M ∧ a ≤ r := by
  rcases L with _ | ⟨c, L'⟩
  · simp only [addLast, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [addLast]
    constructor
    · congr 1
      omega
    · omega
  · rw [addLast_cons x _ (List.cons_ne_nil c L'), List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [addLast_cons x _ (List.cons_ne_nil c L')]
    constructor
    · congr 1
      omega
    · omega

/-- The decoder reads a leaf when closes are left in the column. -/
theorem decNodeQ_leaf {f r : ℕ} (hf : 1 ≤ f) (hr : 1 ≤ r) (l : List ℕ) :
    decNodeQ q f r l = some (.leaf, r, l) := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rfl

/-- The decoder reads the remaining children of a node from their entries, the carry x on
    the last entry left over at the end. -/
theorem decKidsQ_complete (hq : 3 ≤ q) : ∀ us : List ChainTreeQ,
    (∀ u ∈ us, u ≠ .leaf → ∀ f x rest, 2 * u.word.length ≤ f + 1 →
      decNodeQ q f 0 (addLast x (encQ q u) ++ rest) = some (u, x, rest)) →
    us ≠ [] → ∀ ts f r x (M rest : List ℕ), LevelUpQ q (ChainTreeQ.orders ts) →
    LevelUpQ q (ChainTreeQ.orders (ts ++ us)).dropLast →
    ¬LevelUpQ q (ChainTreeQ.orders (ts ++ us)) →
    r :: M = addLast x ((encKidsQ q (ChainTreeQ.orders ts) us).1 ::
      (encKidsQ q (ChainTreeQ.orders ts) us).2) →
    2 * ((us.map ChainTreeQ.word).map List.length).sum ≤ f →
    decKidsQ q f ts r (M ++ rest) = some (.node (ts ++ us), x, rest) := by
  intro us
  induction us with
  | nil =>
    intro _ h
    exact absurd rfl h
  | cons u us ihus =>
    intro ih _ ts f r x M rest hL hup hend hrM hf
    have hupos := ChainTreeQ.length_word_pos u
    rw [List.map_cons, List.map_cons, List.sum_cons] at hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hsplit : ts ++ u :: us = (ts ++ [u]) ++ us := by
      rw [List.append_assoc, List.singleton_append]
    have hf2 : 2 * ((us.map ChainTreeQ.word).map List.length).sum ≤ f' := by
      omega
    have ihus' := ihus (fun x hx => ih x (List.mem_cons_of_mem u hx))
    -- the level after ts ++ [u] when more children follow
    have hupu : us ≠ [] → LevelUpQ q (ChainTreeQ.orders (ts ++ [u])) := by
      intro hne
      have hords : ChainTreeQ.orders us ≠ [] := by
        intro h0
        apply hne
        simpa [ChainTreeQ.orders] using h0
      rw [hsplit, ChainTreeQ.orders_append, List.dropLast_append_of_ne_nil hords] at hup
      exact levelUpQ_of_append hq _ _ hup
    rw [hsplit] at hup hend ⊢
    cases u with
    | leaf =>
      rw [encKidsQ] at hrM
      obtain ⟨hrM', hcr⟩ := addLast_sub_head hrM.symm
      have hc1 := one_le_closeQ_leaf hq hL
      rw [decKidsQ, decNodeQ_leaf (by omega) (by omega)]
      simp only [order_word_leaf, hcr, ↓reduceIte]
      rcases us with _ | ⟨u2, us'⟩
      · rw [List.append_nil] at hend ⊢
        simp only [hend, ↓reduceIte]
        simp only [encKidsQ, addLast, List.cons.injEq] at hrM'
        obtain ⟨hr, rfl⟩ := hrM'
        rw [List.nil_append, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq]
        exact ⟨rfl, by omega, rfl⟩
      · have hup1 := hupu (List.cons_ne_nil _ _)
        simp only [hup1, ↓reduceIte]
        have hrM2 : (r - closeQ q (ChainTreeQ.orders ts) 0) :: M =
            addLast x ((encKidsQ q (ChainTreeQ.orders (ts ++ [.leaf])) (u2 :: us')).1 ::
              (encKidsQ q (ChainTreeQ.orders (ts ++ [.leaf])) (u2 :: us')).2) := by
          rw [ChainTreeQ.orders_concat, order_word_leaf]
          exact hrM'.symm
        have h0 := ihus' (List.cons_ne_nil _ _) (ts ++ [.leaf]) f'
          (r - closeQ q (ChainTreeQ.orders ts) 0) x M rest
        have h1 := h0 hup1 hup
        have h2 := h1 hend hrM2
        exact h2 hf2
    | node vs =>
      have hne := encQ_node_ne_nil (q := q) vs
      have hpos := ChainTreeQ.length_word_pos (ChainTreeQ.node vs)
      have hfN : 2 * (ChainTreeQ.node vs).word.length ≤ f' + 1 := by
        omega
      have hnl : ChainTreeQ.node vs ≠ .leaf := nofun
      rw [encKidsQ, ← ChainTreeQ.orders_concat] at hrM
      generalize hc : closeQ q (ChainTreeQ.orders ts) (order (ChainTreeQ.node vs).word) = c
        at hrM
      generalize hp : encKidsQ q (ChainTreeQ.orders (ts ++ [.node vs])) us = p at hrM
      obtain ⟨y, L⟩ := p
      dsimp only at hrM
      rw [addLast_cons x 0 (List.append_ne_nil_of_left_ne_nil (addLast_ne_nil _ hne) _),
        List.cons.injEq] at hrM
      obtain ⟨rfl, rfl⟩ := hrM
      rcases List.eq_nil_or_concat L with rfl | ⟨L0, a, rfl⟩
      · rw [List.append_nil, addLast_addLast]
        have hIH := ih (.node vs) List.mem_cons_self hnl f' (c + y + x) rest hfN
        rw [decKidsQ, hIH]
        dsimp only
        rw [hc]
        have hk : c ≤ c + y + x := by
          omega
        simp only [hk, ↓reduceIte]
        rcases us with _ | ⟨u2, us'⟩
        · simp only [encKidsQ, Prod.mk.injEq] at hp
          obtain ⟨rfl, -⟩ := hp
          rw [List.append_nil] at hend ⊢
          simp only [hend, ↓reduceIte]
          rw [Nat.add_zero, Nat.add_sub_cancel_left]
        · have hup1 := hupu (List.cons_ne_nil _ _)
          simp only [hup1, ↓reduceIte]
          have hrM2 : (c + y + x - c) :: [] =
              addLast x ((encKidsQ q (ChainTreeQ.orders (ts ++ [.node vs])) (u2 :: us')).1 ::
                (encKidsQ q (ChainTreeQ.orders (ts ++ [.node vs])) (u2 :: us')).2) := by
            rw [hp]
            simp only [addLast, List.cons.injEq, and_true]
            omega
          have h0 := ihus' (List.cons_ne_nil _ _) (ts ++ [.node vs]) f' (c + y + x - c) x []
            rest
          have h1 := h0 hup1 hup
          have h2 := h1 hend hrM2
          have hrec := h2 hf2
          rw [List.nil_append] at hrec
          exact hrec
      · rw [List.concat_eq_append] at hp ⊢
        have hLne : L0 ++ [a] ≠ [] := by
          simp
        rw [addLast_append x _ hLne, List.append_assoc]
        have hIH := ih (.node vs) List.mem_cons_self hnl f' (c + y)
          (addLast x (L0 ++ [a]) ++ rest) hfN
        rw [decKidsQ, hIH]
        dsimp only
        rw [hc]
        have hk : c ≤ c + y := by
          omega
        simp only [hk, ↓reduceIte]
        rcases us with _ | ⟨u2, us'⟩
        · simp [encKidsQ] at hp
        · have hup1 := hupu (List.cons_ne_nil _ _)
          simp only [hup1, ↓reduceIte]
          have hrM2 : (c + y - c) :: addLast x (L0 ++ [a]) =
              addLast x ((encKidsQ q (ChainTreeQ.orders (ts ++ [.node vs])) (u2 :: us')).1 ::
                (encKidsQ q (ChainTreeQ.orders (ts ++ [.node vs])) (u2 :: us')).2) := by
            rw [hp, addLast_cons x y hLne, Nat.add_sub_cancel_left]
          have h0 := ihus' (List.cons_ne_nil _ _) (ts ++ [.node vs]) f' (c + y - c) x
            (addLast x (L0 ++ [a])) rest
          have h1 := h0 hup1 hup
          have h2 := h1 hend hrM2
          exact h2 hf2

/-- The decoder reads a valid node from its entries with a carry x on the last one, given
    fuel 2 |word| - 1. -/
theorem decNodeQ_complete (hq : 3 ≤ q) {t : ChainTreeQ} (h : ValidTreeQ q t) :
    t ≠ .leaf → ∀ f x rest, 2 * t.word.length ≤ f + 1 →
      decNodeQ q f 0 (addLast x (encQ q t) ++ rest) = some (t, x, rest) := by
  induction h with
  | leaf =>
    intro h
    exact absurd rfl h
  | node ts _ hup hend ih =>
    intro _ f x rest hf
    have hne : ts ≠ [] := by
      rintro rfl
      exact hend (levelUpQ_nil hq)
    rw [ChainTreeQ.length_word_node] at hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨r, M, hrM⟩ : ∃ r M, addLast x ((encKidsQ q [] ts).1 :: (encKidsQ q [] ts).2) =
        r :: M := by
      rcases (encKidsQ q [] ts).2 with _ | ⟨b, L⟩
      · exact ⟨_, [], rfl⟩
      · exact ⟨_, _, addLast_cons x _ (List.cons_ne_nil b L)⟩
    have hords : ChainTreeQ.orders [] = [] := rfl
    have hup' : LevelUpQ q (ChainTreeQ.orders ([] ++ ts)).dropLast := by
      rw [List.nil_append]
      exact hup
    have hend' : ¬LevelUpQ q (ChainTreeQ.orders ([] ++ ts)) := by
      rw [List.nil_append]
      exact hend
    have hk := decKidsQ_complete hq ts ih hne [] f' r x M rest (levelUpQ_nil hq) hup' hend'
      (by rw [hords, hrM]) (by omega)
    rw [List.nil_append] at hk
    rw [encQ, hrM, List.cons_append, decNodeQ, hk]

mutual
/-- One entry per node. -/
theorem length_encQ : ∀ t : ChainTreeQ, (encQ q t).length = order t.word
  | .leaf => by
    simp [encQ, ChainTreeQ.word, order]
  | .node ts => by
    rw [encQ, List.length_cons, length_encKidsQ [] ts, ChainTreeQ.word_node, order_cons_flatten,
      List.map_map]
    omega
/-- One entry per node of the node children. -/
theorem length_encKidsQ : ∀ (os : List ℕ) (us : List ChainTreeQ),
    (encKidsQ q os us).2.length = ((us.map ChainTreeQ.word).map order).sum
  | _, [] => by
    simp [encKidsQ]
  | os, .leaf :: us => by
    rw [encKidsQ, length_encKidsQ _ us]
    simp [ChainTreeQ.word, order]
  | os, .node vs :: us => by
    rw [encKidsQ, List.length_append, length_addLast, length_encQ (.node vs),
      length_encKidsQ _ us]
    simp
end

/-- The decoder inverts the encoder on every valid tree with a node at the root. -/
theorem decodeQ_encQ (hodd : Odd q) (hq : 3 ≤ q) {t : ChainTreeQ} (h : ValidTreeQ q t)
    (hn : t ≠ .leaf) : decodeQ q (encQ q t) = some t := by
  have hlen : t.word.length = p2Q q (encQ q t).length := by
    rw [length_encQ]
    exact admissibleQ_length (by omega) (admissibleQ_word hodd hq h)
  have hd := decNodeQ_complete hq h hn (2 * p2Q q (encQ q t).length) 0 [] (by omega)
  rw [addLast_zero, List.append_nil] at hd
  unfold decodeQ
  rw [hd]
  rfl

/-! ### The encoder per column -/

/-- Bracket m of a node is open after children of Orders os. -/
abbrev OpenAtQ (q : ℕ) (os : List ℕ) (m : ℕ) : Prop :=
  2 ^ (m + 1 + (os.map (p2Q q)).sum) ≤ q ^ (1 + os.sum)

/-- Column of the close of bracket m among further children of Orders os after children of
    Orders pre, counted in odd steps: the Orders of the children before its close. -/
def colQ (q : ℕ) (pre : List ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | o :: os, m => (if OpenAtQ q pre m then o else 0) + colQ q (pre ++ [o]) os m

/-- Brackets of a node open after children of Orders pre that close among further children
    of Orders os in column n. -/
def leadAtQ (q : ℕ) (pre os : List ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (bracketsQ q)).filter
    (fun m => OpenAtQ q pre m ∧ ¬OpenAtQ q (pre ++ os) m ∧ colQ q pre os m = n)).card

/-- Closes of the brackets of a node per column, one entry per odd step. -/
def leadQ (q : ℕ) (pre os : List ℕ) : List ℕ :=
  (List.range (1 + os.sum)).map (leadAtQ q pre os)

theorem openAtQ_of_append (hq : 3 ≤ q) {pre os : List ℕ} {m : ℕ}
    (h : OpenAtQ q (pre ++ os) m) : OpenAtQ q pre m := by
  have e1 : 2 ^ (m + 1 + ((pre ++ os).map (p2Q q)).sum) =
      2 ^ (m + 1 + (pre.map (p2Q q)).sum) * 2 ^ (os.map (p2Q q)).sum := by
    rw [List.map_append, List.sum_append, ← pow_add]
    congr 1
    omega
  have e2 : q ^ (1 + (pre ++ os).sum) = q ^ (1 + pre.sum) * q ^ os.sum := by
    rw [List.sum_append, ← pow_add]
    congr 1
    omega
  have h' : 2 ^ (m + 1 + (pre.map (p2Q q)).sum) * 2 ^ (os.map (p2Q q)).sum ≤
      q ^ (1 + pre.sum) * q ^ os.sum := by
    rw [← e1, ← e2]
    exact h
  have hs := q_pow_sum_le hq os
  by_contra hcon
  have hlt : q ^ (1 + pre.sum) < 2 ^ (m + 1 + (pre.map (p2Q q)).sum) := Nat.lt_of_not_le hcon
  have := Nat.mul_lt_mul_of_lt_of_le hlt hs (by positivity)
  omega

theorem not_openAtQ_append (hq : 3 ≤ q) {pre : List ℕ} {m : ℕ} (h : ¬OpenAtQ q pre m)
    (os : List ℕ) : ¬OpenAtQ q (pre ++ os) m :=
  fun h' => h (openAtQ_of_append hq h')

/-- A bracket closed before the children os has column 0 among them. -/
theorem colQ_of_not_openAtQ (hq : 3 ≤ q) :
    ∀ (os pre : List ℕ) {m : ℕ}, ¬OpenAtQ q pre m → colQ q pre os m = 0
  | [], _, _, _ => rfl
  | o :: os, pre, m, h => by
    rw [colQ, colQ_of_not_openAtQ hq os (pre ++ [o]) (not_openAtQ_append hq h [o])]
    simp only [h, ↓reduceIte]

theorem closeQ_eq_card (hq : 3 ≤ q) (pre : List ℕ) (o : ℕ) :
    closeQ q pre o = ((Finset.range (bracketsQ q)).filter
      (fun m => OpenAtQ q pre m ∧ ¬OpenAtQ q (pre ++ [o]) m)).card := by
  unfold closeQ openQ
  have hsub : (Finset.range (bracketsQ q)).filter (fun m => OpenAtQ q (pre ++ [o]) m) ⊆
      (Finset.range (bracketsQ q)).filter (fun m => OpenAtQ q pre m) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, openAtQ_of_append hq hm.2⟩
  have hc := Finset.card_sdiff_of_subset hsub
  rw [← hc]
  congr 1
  ext m
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
  tauto

theorem leadAtQ_cons_lt {pre os : List ℕ} {o n : ℕ} (hn : n < o) :
    leadAtQ q pre (o :: os) n = 0 := by
  unfold leadAtQ
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ ⟨hop, _, hcol⟩
  rw [colQ] at hcol
  simp only [hop, ↓reduceIte] at hcol
  omega

theorem leadAtQ_cons_self (hq : 3 ≤ q) (pre os : List ℕ) (o : ℕ) :
    leadAtQ q pre (o :: os) o = closeQ q pre o + leadAtQ q (pre ++ [o]) os 0 := by
  rw [closeQ_eq_card hq]
  unfold leadAtQ
  rw [← Finset.card_union_of_disjoint]
  · apply congrArg Finset.card
    ext m
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    have hassoc : pre ++ o :: os = (pre ++ [o]) ++ os := by
      simp
    rw [hassoc, colQ]
    constructor
    · rintro ⟨hm, hop, hend, hcol⟩
      simp only [hop, ↓reduceIte] at hcol
      by_cases ho : OpenAtQ q (pre ++ [o]) m
      · exact Or.inr ⟨hm, ho, hend, by omega⟩
      · exact Or.inl ⟨hm, hop, ho⟩
    · rintro (⟨hm, hop, ho⟩ | ⟨hm, ho, hend, hcol⟩)
      · refine ⟨hm, hop, not_openAtQ_append hq ho os, ?_⟩
        rw [colQ_of_not_openAtQ hq os _ ho]
        simp only [hop, ↓reduceIte, Nat.add_zero]
      · have hop := openAtQ_of_append hq ho
        refine ⟨hm, hop, hend, ?_⟩
        rw [hcol]
        simp only [hop, ↓reduceIte, Nat.add_zero]
  · rw [Finset.disjoint_filter]
    intro m _ ⟨_, ho⟩ ⟨ho', _⟩
    exact ho ho'

theorem leadAtQ_cons_gt (hq : 3 ≤ q) (pre os : List ℕ) (o k : ℕ) :
    leadAtQ q pre (o :: os) (o + k + 1) = leadAtQ q (pre ++ [o]) os (k + 1) := by
  unfold leadAtQ
  apply congrArg Finset.card
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  have hassoc : pre ++ o :: os = (pre ++ [o]) ++ os := by
    simp
  rw [hassoc, colQ]
  constructor
  · rintro ⟨hm, hop, hend, hcol⟩
    simp only [hop, ↓reduceIte] at hcol
    by_cases ho : OpenAtQ q (pre ++ [o]) m
    · exact ⟨hm, ho, hend, by omega⟩
    · rw [colQ_of_not_openAtQ hq os _ ho] at hcol
      omega
  · rintro ⟨hm, ho, hend, hcol⟩
    have hop := openAtQ_of_append hq ho
    refine ⟨hm, hop, hend, ?_⟩
    rw [hcol]
    simp only [hop, ↓reduceIte]
    omega

/-- The column closes after one more child of Order o: zero in its first o columns, its own
    closes added at column o. -/
theorem leadQ_cons (hq : 3 ≤ q) (pre os : List ℕ) (o : ℕ) :
    leadQ q pre (o :: os) = List.replicate o 0 ++
      (closeQ q pre o + leadAtQ q (pre ++ [o]) os 0) ::
        (List.range os.sum).map (fun k => leadAtQ q (pre ++ [o]) os (k + 1)) := by
  unfold leadQ
  have hr : 1 + (o :: os).sum = o + (os.sum + 1) := by
    rw [List.sum_cons]
    omega
  rw [hr, List.range_add, List.map_append, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  congr 1
  · rw [List.eq_replicate_iff, List.length_map, List.length_range]
    refine ⟨rfl, ?_⟩
    intro b hb
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hb
    exact leadAtQ_cons_lt (List.mem_range.mp hn)
  · congr 1
    · rw [Nat.add_zero, leadAtQ_cons_self hq]
    · apply List.map_congr_left
      intro k _
      change leadAtQ q pre (o :: os) (o + (k + 1)) = _
      rw [← Nat.add_assoc, leadAtQ_cons_gt hq]

theorem leadQ_eq_cons (q : ℕ) (pre os : List ℕ) :
    leadQ q pre os = leadAtQ q pre os 0 ::
      (List.range os.sum).map (fun k => leadAtQ q pre os (k + 1)) := by
  unfold leadQ
  rw [Nat.add_comm, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- Entries E, carrying b on the last one, against zeros and b. -/
theorem zipWith_replicate_addLast : ∀ (E : List ℕ), E ≠ [] → ∀ (a b : ℕ) (F T : List ℕ),
    List.zipWith (· + ·) (a :: (E ++ F)) (List.replicate E.length 0 ++ b :: T) =
      a :: (addLast b E ++ List.zipWith (· + ·) F T)
  | [], h, _, _, _, _ => absurd rfl h
  | [e], _, a, b, F, T => by
    simp [addLast]
  | e :: e' :: E, _, a, b, F, T => by
    have ih := zipWith_replicate_addLast (e' :: E) (List.cons_ne_nil _ _) e b F T
    simp only [List.length_cons, List.replicate_succ, List.cons_append, List.zipWith_cons_cons,
      Nat.add_zero] at ih ⊢
    rw [ih, addLast_cons b e (List.cons_ne_nil e' E), List.cons_append]

/-- The encoder of the children: zero and their entries, plus the closes of the node per
    column. -/
theorem encKidsQ_eq_leadQ (hq : 3 ≤ q) : ∀ (us : List ChainTreeQ) (pre : List ℕ),
    (encKidsQ q pre us).1 :: (encKidsQ q pre us).2 =
      List.zipWith (· + ·) (0 :: (us.map (encQ q)).flatten) (leadQ q pre (ChainTreeQ.orders us))
  | [], pre => by
    rw [leadQ_eq_cons]
    simp only [encKidsQ, List.map_nil, List.flatten_nil, ChainTreeQ.orders, List.sum_nil,
      List.range_zero, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons.injEq, and_true]
    unfold leadAtQ
    rw [List.append_nil]
    have h0 : ((Finset.range (bracketsQ q)).filter
        (fun m => OpenAtQ q pre m ∧ ¬OpenAtQ q pre m ∧ colQ q pre [] m = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _ h
      exact h.2.1 h.1
    omega
  | .leaf :: us, pre => by
    have ih := encKidsQ_eq_leadQ hq us (pre ++ [0])
    rw [leadQ_eq_cons] at ih
    rw [ChainTreeQ.orders_cons, order_word_leaf, leadQ_cons hq, encKidsQ, List.replicate_zero,
      List.nil_append, List.map_cons, List.flatten_cons]
    simp only [encQ, List.nil_append, List.zipWith_cons_cons, List.cons.injEq] at ih ⊢
    exact ⟨by omega, ih.2⟩
  | .node vs :: us, pre => by
    have ih := encKidsQ_eq_leadQ hq us (pre ++ [order (ChainTreeQ.node vs).word])
    rw [leadQ_eq_cons] at ih
    have hlen := length_encQ (q := q) (.node vs)
    have hrep : List.replicate (order (ChainTreeQ.node vs).word) 0 =
        List.replicate (encQ q (.node vs)).length 0 := by
      rw [hlen]
    rw [ChainTreeQ.orders_cons, leadQ_cons hq, encKidsQ, List.map_cons, List.flatten_cons, hrep,
      zipWith_replicate_addLast _ (encQ_node_ne_nil vs)]
    simp only [List.zipWith_cons_cons, List.cons.injEq] at ih
    rw [Nat.zero_add] at ih
    rw [ih.1, ih.2]

/-- The encoder of a node: zero and the entries of its children, plus the closes of its own
    brackets per column. -/
theorem encQ_node_eq (hq : 3 ≤ q) (ts : List ChainTreeQ) :
    encQ q (.node ts) =
      List.zipWith (· + ·) (0 :: (ts.map (encQ q)).flatten) (leadQ q [] (ChainTreeQ.orders ts)) :=
  encKidsQ_eq_leadQ hq ts []

end AcceleratedCollatz
