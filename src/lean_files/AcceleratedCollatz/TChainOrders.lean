-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChain
import AcceleratedCollatz.TChainQ

/-!
  The chain grammar depends only on the Orders o_1 .. o_k of the chain blocks.
  With `LevelUp os` (level 3^(1+Σo) / 2^(1+Σp2(o)) > 1) and `ValidOrders os`
  (`LevelUp` at every inner boundary): an admissible PV of Order ≥ 1 is exactly
  1 :: (A1 ++ ... ++ Ak ++ t) with chain blocks Ai whose Orders are valid, and
  t = [0] if `LevelUp` of all Orders, t = [] otherwise (`admissible_iff_chain`).
  The representation is unique (`chain_unique`). The blocks' bits are free.
  `LevelUp` is the q = 3 case of `LevelUpQ` (`levelUpQ_three`).
-/

namespace AcceleratedCollatz

/-- Level after a leading 1 and blocks of Orders os is > 1. -/
def LevelUp (os : List ℕ) : Prop :=
  2 ^ (1 + (os.map p2_of).sum) < 3 ^ (1 + os.sum)

/-- `LevelUp` is `LevelUpQ` at q = 3. -/
theorem levelUpQ_three : LevelUpQ 3 = LevelUp := rfl

/-- LevelUp at every inner boundary 1 ≤ i < |os|. -/
def ValidOrders (os : List ℕ) : Prop :=
  ∀ i, 1 ≤ i → i < os.length → LevelUp (os.take i)

/-- The level after 1 :: blocks is > 1 iff `LevelUp` holds for their Orders. -/
theorem one_lt_level_iff (bs : List (List Bool)) (hbs : ∀ b ∈ bs, IsChainBlock b) :
    1 < seqProduct (true :: bs.flatten) ↔ LevelUp (bs.map order) := by
  rw [← seqProductQ_three, ← levelUpQ_three]
  exact one_lt_levelQ_iff le_rfl bs (fun b hb => (admissibleQ_three b).mpr (hbs b hb).adm)

/-- The levels at all inner block boundaries are > 1 iff the Orders are valid. -/
theorem inner_levels_iff (bs : List (List Bool)) (hbs : ∀ b ∈ bs, IsChainBlock b) :
    (∀ i, 1 ≤ i → i < bs.length → 1 < seqProduct (true :: (bs.take i).flatten)) ↔
      ValidOrders (bs.map order) := by
  have htake : ∀ i, ∀ b ∈ bs.take i, IsChainBlock b :=
    fun i b hb => hbs b (List.mem_of_mem_take hb)
  constructor
  · intro h i hi hil
    rw [List.length_map] at hil
    rw [← List.map_take, ← one_lt_level_iff _ (htake i)]
    exact h i hi hil
  · intro h i hi hil
    rw [one_lt_level_iff _ (htake i), List.map_take]
    have hil' : i < (bs.map order).length := by
      rw [List.length_map]
      exact hil
    exact h i hi hil'

/-- Chains of blocks with tails in {[], [0]} that flatten to the same word are equal. -/
theorem chain_unique (bs bs' : List (List Bool)) (t t' : List Bool)
    (hbs : ∀ b ∈ bs, IsChainBlock b) (hbs' : ∀ b ∈ bs', IsChainBlock b)
    (ht : t = [] ∨ t = [false]) (ht' : t' = [] ∨ t' = [false])
    (h : bs.flatten ++ t = bs'.flatten ++ t') : bs = bs' ∧ t = t' := by
  have hfl : ∀ (cs : List (List Bool)) (u : List Bool), (u = [] ∨ u = [false]) →
      cs.flatten ++ u = (cs ++ (if u = [] then [] else [[false]])).flatten := by
    intro cs u hu
    rcases hu with rfl | rfl
    · simp
    · simp
  have hadm : ∀ (cs : List (List Bool)) (u : List Bool), (∀ c ∈ cs, IsChainBlock c) →
      ∀ c ∈ cs ++ (if u = [] then [] else [[false]]), Admissible c := by
    intro cs u hcs c hc
    rcases List.mem_append.mp hc with hc' | hc'
    · exact (hcs c hc').1
    · split_ifs at hc' with hu
      · simp at hc'
      · rw [List.mem_singleton] at hc'
        rw [hc']
        exact admissible_singleton_false
  have heq := flatten_inj_of_admissible _ _ (hadm bs t hbs) (hadm bs' t' hbs')
    (by rw [← hfl bs t ht, ← hfl bs' t' ht', h])
  have hnot : ∀ (cs : List (List Bool)), (∀ c ∈ cs, IsChainBlock c) → [false] ∉ cs := by
    intro cs hcs hmem
    have h1 := (hcs [false] hmem).2
    simp [order] at h1
  rcases ht with rfl | rfl
  · rcases ht' with rfl | rfl
    · simpa using heq
    · simp only [↓reduceIte, List.append_nil, reduceCtorEq] at heq
      exact absurd (heq ▸ List.mem_append_right bs' (List.mem_singleton_self _)) (hnot bs hbs)
  · rcases ht' with rfl | rfl
    · simp only [↓reduceIte, List.append_nil, reduceCtorEq] at heq
      exact absurd (heq ▸ List.mem_append_right bs (List.mem_singleton_self _)) (hnot bs' hbs')
    · simp only [reduceCtorEq, ↓reduceIte, List.append_cancel_right_eq] at heq
      exact ⟨heq, rfl⟩

/-- Chain characterization: admissible PVs of Order ≥ 1 are exactly 1 :: (chain ++ tail)
    with valid Orders, tail determined by `LevelUp` of all Orders. -/
theorem admissible_iff_chain (s : List Bool) :
    (Admissible s ∧ 1 ≤ order s) ↔
      ∃ (bs : List (List Bool)) (t : List Bool),
        s = true :: (bs.flatten ++ t) ∧ (∀ b ∈ bs, IsChainBlock b) ∧
        ValidOrders (bs.map order) ∧
        ((LevelUp (bs.map order) ∧ t = [false]) ∨ (¬ LevelUp (bs.map order) ∧ t = [])) := by
  constructor
  · rintro ⟨hA, hord⟩
    obtain ⟨bs, t, hs, hbs, ht, htiff⟩ := exists_chain s hA hord
    refine ⟨bs, t, hs, hbs, ?_, ?_⟩
    · rw [← inner_levels_iff bs hbs]
      intro i hi hil
      rcases ht with rfl | rfl
      · rw [List.append_nil] at hs
        rw [hs] at hA
        exact ((admissible_split_iff bs (fun b hb => (hbs b hb).adm)).mp hA).1 i hi hil
      · have hA' : Admissible (true :: (bs ++ [[false]]).flatten) := by
          rw [hs] at hA
          simpa using hA
        have hsA : ∀ b ∈ bs ++ [[false]], Admissible b := by
          intro b hb
          rcases List.mem_append.mp hb with hb' | hb'
          · exact (hbs b hb').adm
          · rw [List.mem_singleton] at hb'
            rw [hb']
            exact admissible_singleton_false
        have hil' : i < (bs ++ [[false]]).length := by
          rw [List.length_append]
          omega
        have h := ((admissible_split_iff _ hsA).mp hA').1 i hi hil'
        rw [List.take_append_of_le_length hil.le] at h
        exact h
    · rw [← one_lt_level_iff bs hbs, ← htiff]
      rcases ht with rfl | rfl
      · right
        exact ⟨by simp, rfl⟩
      · left
        exact ⟨rfl, rfl⟩
  · rintro ⟨bs, t, rfl, hbs, hvalid, htail⟩
    have hinner := (inner_levels_iff bs hbs).mpr hvalid
    have hparts := admissible_chain bs hbs hinner
    refine ⟨?_, ?_⟩
    · rcases htail with ⟨hup, rfl⟩ | ⟨hup, rfl⟩
      · exact hparts.2 ((one_lt_level_iff bs hbs).mpr hup)
      · rw [List.append_nil]
        apply hparts.1
        have hne := seqProduct_ne_one (true :: bs.flatten) (List.cons_ne_nil _ _)
        have hng : ¬ 1 < seqProduct (true :: bs.flatten) := by
          rw [one_lt_level_iff bs hbs]
          exact hup
        rcases lt_trichotomy (seqProduct (true :: bs.flatten)) 1 with hl | he | hg
        · exact hl
        · exact absurd he hne
        · exact absurd hg hng
    · rw [order_cons]
      simp

end AcceleratedCollatz
