-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainEquiv
import AcceleratedCollatz.TPrefixCount

/-!
  Rank and unrank of admissible PVs within their Order, by the prefix counts of
  TPrefixCount. `unrank n k` walks the word: at each letter it compares k with the
  number of words that go on with 0. `rank n s` adds these numbers at the ones of
  s. Both read the table `rows`. `unrank n k` is the PV of Order n with exactly k
  smaller ones (`unrank_mem`, `card_lt_unrank`), so it is `admIndex n k`
  (`admIndex_eq_unrank`); `rank` is the inverse (`admIndex_symm_eq_rank`).
  Indices start at 0.
-/

namespace AcceleratedCollatz

/-- The index of x in the sorted enumeration of S is the number of smaller elements. -/
theorem orderIsoOfFin_symm_eq_card (S : Finset (List Bool)) (x : List Bool) (hx : x ∈ S) :
    ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩ : ℕ) = (S.filter (· < x)).card := by
  have himg : S.filter (· < x) = (Finset.Iio ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩)).image
      (fun j => ((S.orderIsoOfFin rfl) j : List Bool)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hy, hlt⟩
      refine ⟨(S.orderIsoOfFin rfl).symm ⟨y, hy⟩, ?_, ?_⟩
      · exact (S.orderIsoOfFin rfl).symm.lt_iff_lt.mpr hlt
      · rw [OrderIso.apply_symm_apply]
    · rintro ⟨j, hj, rfl⟩
      refine ⟨((S.orderIsoOfFin rfl) j).2, ?_⟩
      have h := (S.orderIsoOfFin rfl).lt_iff_lt.mpr hj
      rw [OrderIso.apply_symm_apply] at h
      exact h
  have hinj : Function.Injective (fun j => ((S.orderIsoOfFin rfl) j : List Bool)) :=
    fun a b h => EquivLike.injective (S.orderIsoOfFin rfl) (Subtype.ext h)
  rw [himg, Finset.card_image_of_injective _ hinj, Fin.card_Iio]

theorem append_lt_append_iff (p x y : List Bool) : p ++ x < p ++ y ↔ x < y := by
  induction p with
  | nil =>
    rfl
  | cons a p ih =>
    rw [List.cons_append, List.cons_append, List.cons_lt_cons_iff, ih]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact absurd h (lt_irrefl a)
      · exact h
    · exact fun h => Or.inr ⟨rfl, h⟩

/-- Admissible PVs of Order n that begin with p and are smaller than p ++ u. -/
def lowerSet (n : ℕ) (p u : List Bool) : Finset (List Bool) :=
  (admSet n).filter (fun t => p <+: t ∧ t < p ++ u)

theorem mem_lowerSet (n : ℕ) (p u t : List Bool) :
    t ∈ lowerSet n p u ↔ t ∈ admSet n ∧ p <+: t ∧ t < p ++ u := by
  simp only [lowerSet, Finset.mem_filter]

theorem lowerSet_nil_left (n : ℕ) (u : List Bool) :
    lowerSet n [] u = (admSet n).filter (· < u) := by
  ext t
  simp [lowerSet]

theorem card_lowerSet_nil (n : ℕ) (p : List Bool) : (lowerSet n p []).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨_, ⟨t', rfl⟩, hlt⟩ := (mem_lowerSet n p [] t).mp ht
  rw [append_lt_append_iff] at hlt
  exact List.not_lt_nil t' hlt

/-- An admissible PV of Order n with the proper prefix p has a next letter. -/
theorem exists_cons_of_prefix {n : ℕ} {p t : List Bool} (hlen : p.length < p2_of n)
    (ht : t ∈ admSet n) (hpre : p <+: t) : ∃ c t', t = p ++ c :: t' := by
  obtain ⟨t', rfl⟩ := hpre
  have hA := (mem_admSet n _).mp ht
  have hl := admissible_length _ hA.1
  rw [hA.2, List.length_append] at hl
  cases t' with
  | nil =>
    rw [List.length_nil] at hl
    omega
  | cons c t'' =>
    exact ⟨c, t'', rfl⟩

theorem append_single_append (p u : List Bool) (b : Bool) : p ++ [b] ++ u = p ++ b :: u := by
  rw [List.append_assoc, List.singleton_append]

/-- Next letter 0: the smaller words all go on with 0. -/
theorem lowerSet_false {n : ℕ} {p : List Bool} (u : List Bool) (hlen : p.length < p2_of n) :
    lowerSet n p (false :: u) = lowerSet n (p ++ [false]) u := by
  ext t
  rw [mem_lowerSet, mem_lowerSet, append_single_append]
  constructor
  · rintro ⟨ht, hpre, hlt⟩
    obtain ⟨c, t', rfl⟩ := exists_cons_of_prefix hlen ht hpre
    have hc := hlt
    rw [append_lt_append_iff, List.cons_lt_cons_iff] at hc
    cases c with
    | true =>
      rcases hc with h | ⟨h, _⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    | false =>
      exact ⟨ht, ⟨t', append_single_append p t' false⟩, hlt⟩
  · rintro ⟨ht, hpre, hlt⟩
    exact ⟨ht, (List.prefix_append p [false]).trans hpre, hlt⟩

/-- Next letter 1: the smaller words go on with 0, or with 1 and are smaller later. -/
theorem card_lowerSet_true {n : ℕ} {p : List Bool} (u : List Bool) (hlen : p.length < p2_of n) :
    (lowerSet n p (true :: u)).card =
      (extSet n (p ++ [false])).card + (lowerSet n (p ++ [true]) u).card := by
  have hu : lowerSet n p (true :: u) = extSet n (p ++ [false]) ∪ lowerSet n (p ++ [true]) u := by
    ext t
    rw [Finset.mem_union, mem_lowerSet, mem_lowerSet, mem_extSet, append_single_append,
      ← mem_admSet]
    constructor
    · rintro ⟨ht, hpre, hlt⟩
      obtain ⟨c, t', rfl⟩ := exists_cons_of_prefix hlen ht hpre
      cases c with
      | false =>
        exact Or.inl ⟨ht, t', append_single_append p t' false⟩
      | true =>
        exact Or.inr ⟨ht, ⟨t', append_single_append p t' true⟩, hlt⟩
    · rintro (⟨ht, t', rfl⟩ | ⟨ht, hpre, hlt⟩)
      · refine ⟨ht, (List.prefix_append p [false]).trans (List.prefix_append _ t'), ?_⟩
        rw [append_single_append, append_lt_append_iff, List.cons_lt_cons_iff]
        exact Or.inl (by decide)
      · exact ⟨ht, (List.prefix_append p [true]).trans hpre, hlt⟩
  have hd : Disjoint (extSet n (p ++ [false])) (lowerSet n (p ++ [true]) u) := by
    rw [Finset.disjoint_left]
    intro t h1 h2
    obtain ⟨_, t1, rfl⟩ := (mem_extSet n _ t).mp h1
    obtain ⟨_, ⟨t2, h⟩, _⟩ := (mem_lowerSet n _ u _).mp h2
    rw [append_single_append, append_single_append, List.append_cancel_left_eq,
      List.cons.injEq] at h
    exact absurd h.1 (by decide)
  rw [hu, Finset.card_union_of_disjoint hd]

theorem order_append_false (p : List Bool) : order (p ++ [false]) = order p := by
  rw [order_append_single]
  rfl

theorem order_append_true (p : List Bool) : order (p ++ [true]) = order p + 1 := by
  rw [order_append_single]
  rfl

/-- Number of words below p ++ u among those beginning with p, where p has j ones. -/
def rankFrom (n : ℕ) : ℕ → List Bool → ℕ
  | _, [] => 0
  | j, false :: u => rankFrom n j u
  | j, true :: u => childCnt n u.length j + rankFrom n (j + 1) u

/-- The rest of the word with index k among those beginning with a prefix with r
    letters to come and j ones. -/
def unrankFrom (n : ℕ) : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | r + 1, j, k =>
    if k < childCnt n r j then false :: unrankFrom n r j k
    else true :: unrankFrom n r (j + 1) (k - childCnt n r j)

/-- `rankFrom` counts the smaller words with the same prefix. -/
theorem card_lowerSet {n : ℕ} : ∀ (u p : List Bool), GoodPrefix n p → p ++ u ∈ admSet n →
    (lowerSet n p u).card = rankFrom n (order p) u
  | [], p, _, _ => card_lowerSet_nil n p
  | b :: u, p, hG, hs => by
    have hA := (mem_admSet n _).mp hs
    have hl := admissible_length _ hA.1
    rw [hA.2, List.length_append, List.length_cons] at hl
    have hs' : p ++ [b] ++ u ∈ admSet n := by
      rw [append_single_append]
      exact hs
    have hG' : GoodPrefix n (p ++ [b]) :=
      goodPrefix_of_mem_extSet ((mem_extSet n _ _).mpr ⟨hA, u, append_single_append p u b⟩)
    cases b with
    | false =>
      rw [lowerSet_false u (by omega), card_lowerSet u (p ++ [false]) hG' hs',
        order_append_false, rankFrom]
    | true =>
      rw [card_lowerSet_true u (by omega),
        card_extSet_child false hG (by omega) (card_extSet u.length),
        card_lowerSet u (p ++ [true]) hG' hs', order_append_false, order_append_true,
        rankFrom]

/-- `unrankFrom` completes a good prefix to the word with k smaller ones. -/
theorem unrankFrom_spec {n : ℕ} : ∀ (r : ℕ) (p : List Bool) (k : ℕ), GoodPrefix n p →
    p.length + r = p2_of n → k < (extSet n p).card →
    p ++ unrankFrom n r (order p) k ∈ admSet n ∧
      (lowerSet n p (unrankFrom n r (order p) k)).card = k
  | 0, p, k, _, hlen, hk => by
    rw [card_extSet_full (by omega)] at hk
    rw [unrankFrom, List.append_nil, card_lowerSet_nil]
    by_cases hp : p ∈ admSet n
    · rw [ite_eq_left hp] at hk
      exact ⟨hp, by omega⟩
    · rw [ite_eq_right hp] at hk
      omega
  | r + 1, p, k, hG, hlen, hk => by
    have h0 := card_extSet_child false hG (r := r) (by omega) (card_extSet r)
    have h1 := card_extSet_child true hG (r := r) (by omega) (card_extSet r)
    rw [order_append_false] at h0
    rw [order_append_true] at h1
    rw [card_extSet_split (by omega), h0, h1] at hk
    rw [unrankFrom]
    by_cases hlt : k < childCnt n r (order p)
    · rw [ite_eq_left hlt]
      have hne : (extSet n (p ++ [false])).Nonempty := by
        rw [← Finset.card_pos, h0]
        omega
      obtain ⟨s, hs⟩ := hne
      have hG' := goodPrefix_of_mem_extSet hs
      have hl' : (p ++ [false]).length + r = p2_of n := by
        rw [List.length_append, List.length_singleton]
        omega
      have hk0 : k < (extSet n (p ++ [false])).card := by
        rw [h0]
        exact hlt
      have ih := unrankFrom_spec r (p ++ [false]) k hG' hl' hk0
      rw [order_append_false, append_single_append] at ih
      refine ⟨ih.1, ?_⟩
      rw [lowerSet_false _ (by omega)]
      exact ih.2
    · rw [ite_eq_right hlt]
      have hk1 : k - childCnt n r (order p) < (extSet n (p ++ [true])).card := by
        rw [h1]
        omega
      obtain ⟨s, hs⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hk1)
      have hG' := goodPrefix_of_mem_extSet hs
      have hl' : (p ++ [true]).length + r = p2_of n := by
        rw [List.length_append, List.length_singleton]
        omega
      have ih := unrankFrom_spec r (p ++ [true]) _ hG' hl' hk1
      rw [order_append_true, append_single_append] at ih
      refine ⟨ih.1, ?_⟩
      rw [card_lowerSet_true _ (by omega), h0, ih.2]
      omega

/-- `childCnt`, read from row r of the table. -/
def rowChild (n r j : ℕ) (rw : List ℕ) : ℕ :=
  if r = 0 ∨ 2 ^ (p2_of n - r) < 3 ^ j then rw.getD j 0 else 0

theorem rowChild_row (n r j : ℕ) : rowChild n r j (row n r) = childCnt n r j := by
  rw [rowChild, childCnt, getD_row]

/-- `unrankFrom`, reading the rows of the table from the top. -/
def unrankRows (n : ℕ) : List (List ℕ) → ℕ → ℕ → List Bool
  | [], _, _ => []
  | rw :: rest, j, k =>
    if k < rowChild n rest.length j rw then false :: unrankRows n rest j k
    else true :: unrankRows n rest (j + 1) (k - rowChild n rest.length j rw)

/-- `rankFrom`, reading the rows of the table from the top. -/
def rankRows (n : ℕ) : List (List ℕ) → ℕ → List Bool → ℕ
  | _ :: rest, j, false :: u => rankRows n rest j u
  | rw :: rest, j, true :: u => rowChild n u.length j rw + rankRows n rest (j + 1) u
  | _, _, _ => 0

theorem unrankRows_rows (n : ℕ) : ∀ r j k,
    unrankRows n (rows n r) j k = unrankFrom n (r + 1) j k
  | 0, j, k => by
    change unrankRows n [row n 0] j k = _
    simp only [unrankRows, unrankFrom, List.length_nil, rowChild_row]
  | r + 1, j, k => by
    rw [unrankFrom, rows_succ, unrankRows, length_rows, rowChild_row, unrankRows_rows n r,
      unrankRows_rows n r]

theorem rankRows_rows (n : ℕ) : ∀ (r j : ℕ) (u : List Bool), u.length = r + 1 →
    rankRows n (rows n r) j u = rankFrom n j u
  | 0, j, u, hu => by
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hu
    change rankRows n [row n 0] j [b] = _
    cases b with
    | false =>
      simp only [rankRows, rankFrom]
    | true =>
      simp only [rankRows, rankFrom, List.length_nil, rowChild_row]
  | r + 1, j, [], hu => by
    rw [List.length_nil] at hu
    omega
  | r + 1, j, b :: u, hu => by
    rw [List.length_cons, Nat.add_right_cancel_iff] at hu
    rw [rows_succ]
    cases b with
    | false =>
      rw [rankRows, rankFrom, rankRows_rows n r j u hu]
    | true =>
      rw [rankRows, rankFrom, rankRows_rows n r (j + 1) u hu, hu, rowChild_row]

/-- The admissible PV of Order n with index k in lexicographic order (from 0). -/
def unrank (n k : ℕ) : List Bool := unrankRows n (rows n (p2_of n - 1)) 0 k

/-- The index of s among the admissible PVs of Order n in lexicographic order
    (from 0). -/
def rank (n : ℕ) (s : List Bool) : ℕ := rankRows n (rows n (p2_of n - 1)) 0 s

theorem unrank_eq_unrankFrom (n k : ℕ) : unrank n k = unrankFrom n (p2_of n) 0 k := by
  have hp : p2_of n = p2_of n - 1 + 1 := by
    unfold p2_of
    omega
  rw [unrank, unrankRows_rows, ← hp]

theorem rank_eq_rankFrom {n : ℕ} {s : List Bool} (hs : s ∈ admSet n) :
    rank n s = rankFrom n 0 s := by
  have hA := (mem_admSet n s).mp hs
  have hl := admissible_length s hA.1
  rw [hA.2] at hl
  have hp : p2_of n = p2_of n - 1 + 1 := by
    unfold p2_of
    omega
  rw [rank, rankRows_rows n _ 0 s (by omega)]

/-- `unrank n k` is an admissible PV of Order n. -/
theorem unrank_mem {n k : ℕ} (hk : k < (admSet n).card) : unrank n k ∈ admSet n := by
  rw [← extSet_nil] at hk
  have h := (unrankFrom_spec (p2_of n) [] k (goodPrefix_nil n) (by simp) hk).1
  rw [List.nil_append] at h
  rw [unrank_eq_unrankFrom]
  exact h

/-- Exactly k admissible PVs of Order n are smaller than `unrank n k`. -/
theorem card_lt_unrank {n k : ℕ} (hk : k < (admSet n).card) :
    ((admSet n).filter (· < unrank n k)).card = k := by
  rw [← extSet_nil] at hk
  have h := (unrankFrom_spec (p2_of n) [] k (goodPrefix_nil n) (by simp) hk).2
  rw [lowerSet_nil_left] at h
  rw [unrank_eq_unrankFrom]
  exact h

/-- `rank n s` is the number of admissible PVs of Order n smaller than s. -/
theorem rank_eq_card {n : ℕ} {s : List Bool} (hs : s ∈ admSet n) :
    rank n s = ((admSet n).filter (· < s)).card := by
  rw [rank_eq_rankFrom hs, ← lowerSet_nil_left]
  exact (card_lowerSet s [] (goodPrefix_nil n) hs).symm

/-- `unrank` computes the sorted enumeration `admIndex`. -/
theorem admIndex_eq_unrank (n : ℕ) (i : Fin (admSet n).card) :
    (admIndex n i : List Bool) = unrank n i := by
  have hmem := unrank_mem i.2
  have hidx : (admIndex n).symm ⟨unrank n i, hmem⟩ = i := by
    apply Fin.ext
    unfold admIndex
    rw [orderIsoOfFin_symm_eq_card, card_lt_unrank i.2]
  have h := congrArg (admIndex n) hidx
  rw [OrderIso.apply_symm_apply] at h
  exact (congrArg Subtype.val h).symm

/-- `rank` computes the inverse of `admIndex`. -/
theorem admIndex_symm_eq_rank (n : ℕ) (s : List Bool) (hs : s ∈ admSet n) :
    ((admIndex n).symm ⟨s, hs⟩ : ℕ) = rank n s := by
  unfold admIndex
  rw [orderIsoOfFin_symm_eq_card, rank_eq_card hs]

theorem rank_unrank {n k : ℕ} (hk : k < (admSet n).card) : rank n (unrank n k) = k := by
  rw [rank_eq_card (unrank_mem hk), card_lt_unrank hk]

theorem unrank_rank {n : ℕ} {s : List Bool} (hs : s ∈ admSet n) : unrank n (rank n s) = s := by
  have h := admIndex_eq_unrank n ((admIndex n).symm ⟨s, hs⟩)
  rw [OrderIso.apply_symm_apply, admIndex_symm_eq_rank] at h
  exact h.symm

-- The seven PVs of Order 5 in order.
set_option linter.hashCommand false in
#guard (List.range 7).map (unrank 5) =
  [[true, true, false, true, true, false, true, false],
   [true, true, false, true, true, true, false, false],
   [true, true, true, false, true, false, true, false],
   [true, true, true, false, true, true, false, false],
   [true, true, true, true, false, false, true, false],
   [true, true, true, true, false, true, false, false],
   [true, true, true, true, true, false, false, false]]

-- Order 60, index ⌊2 a(60) / 3⌋ - 1: the word, and its index back.
set_option linter.hashCommand false in
#guard String.ofList ((unrank 60 883625357808182753690875).map fun b => if b then '1' else '0') =
  "111111010001111111110110101001110101111011011011" ++
  "001011101011000101111101101011111100001100010100"

set_option linter.hashCommand false in
#guard rank 60 (unrank 60 883625357808182753690875) = 883625357808182753690875

end AcceleratedCollatz
