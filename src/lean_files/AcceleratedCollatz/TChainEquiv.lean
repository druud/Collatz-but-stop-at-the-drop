-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TAdmSet
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

/-!
  Chain decomposition as an equivalence. `chainBlocks n` = the block lists with
  chain blocks, valid Orders and Order sum n; `chainWord bs` = 1 :: (bs ++ t),
  t = [0] iff `LevelUp` of the Orders. `chainEquiv n`: the admissible PVs of Order
  n + 1 correspond to `chainBlocks n` via `chainWord`.
  (d, c) encoding: a block of Order d is coded by d and its index c in the
  lexicographic list (0 < 1) of `admSet d` (`admIndex`, `blockCode`); `codeEquiv n`:
  the admissible PVs of Order n + 1 correspond to the lists of codes with d ≥ 1,
  valid Orders and Order sum n (`chainCodes n`).
-/

namespace AcceleratedCollatz

/-- Block lists of chain blocks with valid Orders summing to n. -/
def chainBlocks (n : ℕ) : Set (List (List Bool)) :=
  {bs | (∀ b ∈ bs, IsChainBlock b) ∧ ValidOrders (bs.map order) ∧ (bs.map order).sum = n}

/-- Tail fixed by the Orders. -/
def chainTail (bs : List (List Bool)) : List Bool :=
  if LevelUp (bs.map order) then [false] else []

/-- 1 :: (blocks ++ tail). -/
def chainWord (bs : List (List Bool)) : List Bool :=
  true :: (bs.flatten ++ chainTail bs)

theorem chainTail_cases (bs : List (List Bool)) :
    (LevelUp (bs.map order) ∧ chainTail bs = [false]) ∨
      (¬ LevelUp (bs.map order) ∧ chainTail bs = []) := by
  unfold chainTail
  by_cases hl : LevelUp (bs.map order)
  · left
    exact ⟨hl, by simp [hl]⟩
  · right
    exact ⟨hl, by simp [hl]⟩

theorem order_chainWord (bs : List (List Bool)) :
    order (chainWord bs) = 1 + (bs.map order).sum := by
  have htl : order (chainTail bs) = 0 := by
    rcases chainTail_cases bs with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]
      simp [order]
    · rw [h]
      simp [order]
  unfold chainWord
  rw [order_cons, order_append, order_flatten, htl]
  simp only [↓reduceIte]
  omega

theorem chainWord_mem {n : ℕ} {bs : List (List Bool)} (h : bs ∈ chainBlocks n) :
    chainWord bs ∈ admSet (n + 1) := by
  obtain ⟨hcb, hvalid, hsum⟩ := h
  rw [mem_admSet]
  refine ⟨((admissible_iff_chain _).mpr ⟨bs, chainTail bs, rfl, hcb, hvalid,
    chainTail_cases bs⟩).1, ?_⟩
  rw [order_chainWord, hsum]
  omega

theorem chainWord_injOn (n : ℕ) : Set.InjOn chainWord (chainBlocks n) := by
  intro bs hbs bs' hbs' h
  unfold chainWord at h
  rw [List.cons.injEq] at h
  have ht : ∀ c, chainTail c = [] ∨ chainTail c = [false] := by
    intro c
    rcases chainTail_cases c with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  exact (chain_unique bs bs' _ _ hbs.1 hbs'.1 (ht bs) (ht bs') h.2).1

theorem chainWord_surjOn (n : ℕ) :
    Set.SurjOn chainWord (chainBlocks n) (admSet (n + 1) : Set (List Bool)) := by
  intro s hs
  rw [Finset.mem_coe, mem_admSet] at hs
  obtain ⟨bs, t, rfl, hcb, hvalid, htail⟩ :=
    (admissible_iff_chain s).mp ⟨hs.1, by omega⟩
  have htt : t = chainTail bs := by
    rcases htail with ⟨hl, rfl⟩ | ⟨hl, rfl⟩
    · simp [chainTail, hl]
    · simp [chainTail, hl]
  subst htt
  have hord := order_chainWord bs
  unfold chainWord at hord
  exact ⟨bs, ⟨hcb, hvalid, by omega⟩, rfl⟩

/-- Chain decomposition: admissible PVs of Order n + 1 ≃ `chainBlocks n`. -/
noncomputable def chainEquiv (n : ℕ) : (admSet (n + 1) : Set (List Bool)) ≃ chainBlocks n :=
  (Set.BijOn.equiv chainWord
    ⟨fun _ h => chainWord_mem h, chainWord_injOn n, chainWord_surjOn n⟩).symm

theorem chainWord_chainEquiv (n : ℕ) (s : (admSet (n + 1) : Set (List Bool))) :
    chainWord (chainEquiv n s) = s := by
  unfold chainEquiv
  exact congrArg Subtype.val ((Set.BijOn.equiv chainWord _).apply_symm_apply s)

/-- Admissible PVs of Order d in lexicographic order, indexed from 0. -/
noncomputable def admIndex (d : ℕ) : Fin (admSet d).card ≃o admSet d :=
  (admSet d).orderIsoOfFin rfl

/-- (d, c) code of a block: its Order and its index in that Order's sorted list. -/
noncomputable def blockCode (b : List Bool) (hb : b ∈ admSet (order b)) :
    Σ d, Fin (admSet d).card :=
  ⟨order b, (admIndex (order b)).symm ⟨b, hb⟩⟩

/-- Block of a (d, c) code. -/
noncomputable def codeBlock (x : Σ d, Fin (admSet d).card) : List Bool :=
  (admIndex x.1 x.2).1

theorem codeBlock_mem (x : Σ d, Fin (admSet d).card) : codeBlock x ∈ admSet x.1 :=
  (admIndex x.1 x.2).2

theorem order_codeBlock (x : Σ d, Fin (admSet d).card) : order (codeBlock x) = x.1 :=
  ((mem_admSet _ _).mp (codeBlock_mem x)).2

theorem codeBlock_blockCode (b : List Bool) (hb : b ∈ admSet (order b)) :
    codeBlock (blockCode b hb) = b := by
  unfold codeBlock blockCode
  rw [OrderIso.apply_symm_apply]

theorem blockCode_codeBlock (x : Σ d, Fin (admSet d).card)
    (hb : codeBlock x ∈ admSet (order (codeBlock x))) : blockCode (codeBlock x) hb = x := by
  obtain ⟨d, i⟩ := x
  have key : ∀ e (h : e = d) (hm : (admIndex d i).1 ∈ admSet e),
      (⟨e, (admIndex e).symm ⟨(admIndex d i).1, hm⟩⟩ : Σ d, Fin (admSet d).card) = ⟨d, i⟩ := by
    intro e h hm
    subst h
    simp
  exact key _ (order_codeBlock ⟨d, i⟩) hb

/-- (d, c) codes of Order n + 1: lists of codes with d ≥ 1, valid Orders, Order sum n. -/
def chainCodes (n : ℕ) : Set (List (Σ d, Fin (admSet d).card)) :=
  {l | (∀ x ∈ l, 1 ≤ x.1) ∧ ValidOrders (l.map Sigma.fst) ∧ (l.map Sigma.fst).sum = n}

theorem mem_admSet_order_of_chainBlock {b : List Bool} (h : IsChainBlock b) :
    b ∈ admSet (order b) :=
  (mem_admSet _ b).mpr ⟨h.adm, rfl⟩

theorem map_fst_pmap_blockCode (bs : List (List Bool)) (h : ∀ b ∈ bs, b ∈ admSet (order b)) :
    (bs.pmap blockCode h).map Sigma.fst = bs.map order := by
  rw [List.map_pmap]
  exact List.pmap_eq_map _

theorem map_order_map_codeBlock (l : List (Σ d, Fin (admSet d).card)) :
    (l.map codeBlock).map order = l.map Sigma.fst := by
  rw [List.map_map]
  exact List.map_congr_left (fun x _ => order_codeBlock x)

/-- Chain blocks ≃ their (d, c) codes. -/
noncomputable def chainCodeEquiv (n : ℕ) : chainBlocks n ≃ chainCodes n where
  toFun bs := ⟨bs.1.pmap blockCode
      (fun b hb => mem_admSet_order_of_chainBlock (bs.2.1 b hb)), by
    obtain ⟨_, hvalid, hsum⟩ := bs.2
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_pmap.mp hx
      exact (bs.2.1 b hb).order_pos
    · rw [map_fst_pmap_blockCode]
      exact hvalid
    · rw [map_fst_pmap_blockCode]
      exact hsum⟩
  invFun l := ⟨l.1.map codeBlock, by
    obtain ⟨hpos, hvalid, hsum⟩ := l.2
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
      exact ⟨((mem_admSet _ _).mp (codeBlock_mem x)).1,
        le_of_le_of_eq (hpos x hx) (order_codeBlock x).symm⟩
    · rw [map_order_map_codeBlock]
      exact hvalid
    · rw [map_order_map_codeBlock]
      exact hsum⟩
  left_inv bs := by
    apply Subtype.ext
    simp only [List.map_pmap, codeBlock_blockCode]
    exact List.pmap_eq_self.mpr fun _ _ => rfl
  right_inv l := by
    apply Subtype.ext
    simp only [List.pmap_map, blockCode_codeBlock]
    exact List.pmap_eq_self.mpr fun _ _ => rfl

/-- (d, c) encoding: admissible PVs of Order n + 1 ≃ `chainCodes n`. -/
noncomputable def codeEquiv (n : ℕ) : (admSet (n + 1) : Set (List Bool)) ≃ chainCodes n :=
  (chainEquiv n).trans (chainCodeEquiv n)

end AcceleratedCollatz
