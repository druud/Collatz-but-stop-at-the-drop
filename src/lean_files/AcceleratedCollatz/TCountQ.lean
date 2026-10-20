-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainEquivQ

/-!
  Counting recursion for the admissible words of the q-family (odd q ≥ 3). With
  `admSetQ q n` the admissible words of Order n and `blockSetQ q os` the block lists
  with Orders os:
  |admSetQ q (n+1)| = Σ over the Order lists os of ∏ |admSetQ q o_i|
  (`card_admSetQ_succ`), where os runs through `validCompsQ q n`: the lists of natural
  numbers, 0 allowed, with sum n that keep the level above 1 before the last entry and
  bring it below 1 after it (`mem_validCompsQ`). Such a list has fewer than
  p2Q q (n + 1) entries (`length_lt_of_levelUpQ_dropLast`), so there are finitely many.
  The block lists over them are `chainBlocksQ q n` (`mem_sigma_blockSetQ`), which
  `chainWordQ` maps one to one onto `admSetQ q (n + 1)`. An Order-0 block is the word
  [0] and counts with the factor |admSetQ q 0| = 1.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Lists of k natural numbers, 0 allowed, with sum n. -/
def weakComps : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | k + 1, n => (List.range (n + 1)).flatMap (fun j => (weakComps k (n - j)).map (List.cons j))

/-- Membership in `weakComps k n`. -/
theorem mem_weakComps : ∀ (k n : ℕ) (os : List ℕ),
    os ∈ weakComps k n ↔ os.length = k ∧ os.sum = n
  | 0, 0, os => by
    simp only [weakComps, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h, _⟩
      exact List.length_eq_zero_iff.mp h
  | 0, n + 1, os => by
    simp only [weakComps, List.not_mem_nil, false_iff]
    rintro ⟨h, hs⟩
    rw [List.length_eq_zero_iff.mp h] at hs
    simp at hs
  | k + 1, n, os => by
    simp only [weakComps, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨j, hj, t, ht, rfl⟩
      rw [mem_weakComps k (n - j) t] at ht
      refine ⟨by rw [List.length_cons, ht.1], ?_⟩
      rw [List.sum_cons, ht.2]
      omega
    · rintro ⟨hlen, hsum⟩
      cases os with
      | nil =>
        simp at hlen
      | cons o t =>
        rw [List.sum_cons] at hsum
        rw [List.length_cons] at hlen
        refine ⟨o, by omega, t, ?_, rfl⟩
        rw [mem_weakComps k (n - o) t]
        exact ⟨by omega, by omega⟩

/-- A list has at most as many entries as the sum of p2Q of its entries. -/
theorem length_le_sum_p2Q (q : ℕ) (os : List ℕ) : os.length ≤ (os.map (p2Q q)).sum := by
  induction os with
  | nil =>
    simp
  | cons o t ih =>
    have h := one_le_p2Q q o
    rw [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- The sum of a list without its last entry is at most the sum of the list. -/
theorem sum_dropLast_le (os : List ℕ) : os.dropLast.sum ≤ os.sum := by
  have h : os.sum = os.dropLast.sum + (os.drop (os.length - 1)).sum := by
    rw [← List.sum_append, List.dropLast_eq_take, List.take_append_drop]
  omega

/-- Orders that keep the level above 1 before the last one: fewer than p2Q(sum + 1)
    of them. -/
theorem length_lt_of_levelUpQ_dropLast (hq : 3 ≤ q) {os : List ℕ}
    (h : LevelUpQ q os.dropLast) : os.length < p2Q q (os.sum + 1) := by
  unfold LevelUpQ at h
  have hsum := sum_dropLast_le os
  have hpow : q ^ (1 + os.dropLast.sum) ≤ q ^ (os.sum + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hspec := p2Q_spec hq (os.sum + 1)
  have hlt : 2 ^ (1 + (os.dropLast.map (p2Q q)).sum) < 2 ^ p2Q q (os.sum + 1) :=
    lt_of_lt_of_le h (le_trans hpow hspec.le)
  have hexp := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have hlen := length_le_sum_p2Q q os.dropLast
  rw [List.length_dropLast] at hlen
  omega

/-- Order lists of the chains of Order n + 1: sum n, the level above 1 before the last
    entry and below 1 after it. -/
def validCompsQ (q n : ℕ) : Finset (List ℕ) :=
  ((List.range (p2Q q (n + 1))).flatMap (fun k => weakComps k n)).toFinset.filter
    (fun os => LevelUpQ q os.dropLast ∧ ¬LevelUpQ q os)

/-- Membership in `validCompsQ q n`. -/
theorem mem_validCompsQ (hq : 3 ≤ q) (n : ℕ) (os : List ℕ) :
    os ∈ validCompsQ q n ↔ os.sum = n ∧ LevelUpQ q os.dropLast ∧ ¬LevelUpQ q os := by
  simp only [validCompsQ, Finset.mem_filter, List.mem_toFinset, List.mem_flatMap,
    List.mem_range, mem_weakComps]
  constructor
  · rintro ⟨⟨k, _, _, hsum⟩, h⟩
    exact ⟨hsum, h⟩
  · rintro ⟨hsum, hup, hend⟩
    refine ⟨⟨os.length, ?_, rfl, hsum⟩, hup, hend⟩
    rw [← hsum]
    exact length_lt_of_levelUpQ_dropLast hq hup

/-- Block lists with Orders os, every block admissible. -/
def blockSetQ (q : ℕ) : List ℕ → Finset (List (List Bool))
  | [] => {[]}
  | o :: os => (admSetQ q o ×ˢ blockSetQ q os).image (fun p => p.1 :: p.2)

/-- Membership in `blockSetQ q os`. -/
theorem mem_blockSetQ (hq : 3 ≤ q) : ∀ (os : List ℕ) (bs : List (List Bool)),
    bs ∈ blockSetQ q os ↔ bs.map order = os ∧ ∀ b ∈ bs, AdmissibleQ q b
  | [], bs => by
    cases bs with
    | nil =>
      simp [blockSetQ]
    | cons b t =>
      simp [blockSetQ]
  | o :: os, bs => by
    simp only [blockSetQ, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨b, t, ⟨hb, ht⟩, rfl⟩
      rw [mem_admSetQ (by omega)] at hb
      rw [mem_blockSetQ hq os t] at ht
      refine ⟨by rw [List.map_cons, hb.2, ht.1], ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hb.1
      · exact ht.2 c hc'
    · rintro ⟨hmap, hadm⟩
      cases bs with
      | nil =>
        simp at hmap
      | cons b t =>
        rw [List.map_cons, List.cons.injEq] at hmap
        refine ⟨b, t, ⟨?_, ?_⟩, rfl⟩
        · rw [mem_admSetQ (by omega)]
          exact ⟨hadm b List.mem_cons_self, hmap.1⟩
        · rw [mem_blockSetQ hq os t]
          exact ⟨hmap.2, fun c hc => hadm c (List.mem_cons_of_mem b hc)⟩

/-- Number of block lists with Orders os: the product of the counts of the Orders. -/
theorem card_blockSetQ (q : ℕ) : ∀ os : List ℕ,
    (blockSetQ q os).card = (os.map (fun o => (admSetQ q o).card)).prod
  | [] => by
    simp [blockSetQ]
  | o :: os => by
    rw [blockSetQ, Finset.card_image_of_injective, Finset.card_product, card_blockSetQ q os,
      List.map_cons, List.prod_cons]
    intro p r h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2

/-- The block lists over `validCompsQ q n` are `chainBlocksQ q n`. -/
theorem mem_sigma_blockSetQ (hq : 3 ≤ q) (n : ℕ) (os : List ℕ) (bs : List (List Bool)) :
    (⟨os, bs⟩ : Σ _ : List ℕ, List (List Bool)) ∈ (validCompsQ q n).sigma (blockSetQ q) ↔
      bs ∈ chainBlocksQ q n ∧ bs.map order = os := by
  simp only [Finset.mem_sigma, mem_validCompsQ hq, mem_blockSetQ hq]
  constructor
  · rintro ⟨⟨hsum, hup, hend⟩, rfl, hadm⟩
    exact ⟨⟨hadm, hup, hend, hsum⟩, rfl⟩
  · rintro ⟨⟨hadm, hup, hend, hsum⟩, rfl⟩
    exact ⟨⟨hsum, hup, hend⟩, rfl, hadm⟩

/-- The count by chains: |admSetQ q (n+1)| = Σ over the Order lists os in
    `validCompsQ q n` of ∏ |admSetQ q o_i|. -/
theorem card_admSetQ_succ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (admSetQ q (n + 1)).card =
      ∑ os ∈ validCompsQ q n, (os.map (fun o => (admSetQ q o).card)).prod := by
  have himg : ((validCompsQ q n).sigma (blockSetQ q)).image (fun p => chainWordQ p.2) =
      admSetQ q (n + 1) := by
    ext s
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨os, bs⟩, hp, rfl⟩
      exact chainWordQ_mem hodd hq ((mem_sigma_blockSetQ hq n os bs).mp hp).1
    · intro hs
      obtain ⟨bs, hbs, rfl⟩ := chainWordQ_surjOn hodd hq n (Finset.mem_coe.mpr hs)
      exact ⟨⟨bs.map order, bs⟩, (mem_sigma_blockSetQ hq n _ bs).mpr ⟨hbs, rfl⟩, rfl⟩
  have hinj : Set.InjOn (fun p : Σ _ : List ℕ, List (List Bool) => chainWordQ p.2)
      ((validCompsQ q n).sigma (blockSetQ q)) := by
    rintro ⟨os, bs⟩ hp ⟨os', bs'⟩ hr h
    rw [Finset.mem_coe, mem_sigma_blockSetQ hq] at hp hr
    have hbb : bs = bs' := chainWordQ_injOn q n hp.1 hr.1 h
    subst hbb
    rw [← hp.2, ← hr.2]
  rw [← himg, Finset.card_image_of_injOn hinj, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro os _
  exact card_blockSetQ q os

-- q = 5: the counts of Orders 1 to 4, directly and by chains.
set_option linter.hashCommand false in
#guard (List.range 4).map (fun n => (admSetQ 5 (n + 1)).card) = [1, 2, 5, 14]

set_option linter.hashCommand false in
#guard (List.range 4).map
    (fun n => ∑ os ∈ validCompsQ 5 n, (os.map (fun o => (admSetQ 5 o).card)).prod) =
  [1, 2, 5, 14]

end AcceleratedCollatz
