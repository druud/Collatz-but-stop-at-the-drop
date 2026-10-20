-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainQ
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

/-!
  The chain decomposition of the q-family (odd q ≥ 3) as an equivalence.
  `chainBlocksQ q n` = the lists of admissible blocks, of any Orders, whose Orders sum
  to n, keep the level above 1 before the last block and bring it below 1 after it;
  `chainWordQ bs` = 1 :: (B1 ++ ... ++ Bm). `chainEquivQ`: the admissible words of
  Order n + 1 correspond to `chainBlocksQ q n` via `chainWordQ`.
  (d, c) encoding: a block of Order d is coded by d and its index c in the
  lexicographic list (0 < 1) of `admSetQ q d` (`admIndexQ`, `blockCodeQ`);
  `codeEquivQ`: the admissible words of Order n + 1 correspond to the lists of codes
  whose Orders satisfy the same condition (`chainCodesQ q n`). An Order-0 block has the
  code (0, 0).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Lists of admissible blocks with Order sum n whose Orders keep the level above 1
    before the last block and bring it below 1 after it. -/
def chainBlocksQ (q n : ℕ) : Set (List (List Bool)) :=
  {bs | (∀ b ∈ bs, AdmissibleQ q b) ∧ LevelUpQ q (bs.map order).dropLast ∧
    ¬LevelUpQ q (bs.map order) ∧ (bs.map order).sum = n}

/-- 1 :: blocks. -/
def chainWordQ (bs : List (List Bool)) : List Bool :=
  true :: bs.flatten

theorem order_chainWordQ (bs : List (List Bool)) :
    order (chainWordQ bs) = 1 + (bs.map order).sum :=
  order_cons_flatten bs

theorem chainWordQ_mem (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {bs : List (List Bool)}
    (h : bs ∈ chainBlocksQ q n) : chainWordQ bs ∈ admSetQ q (n + 1) := by
  obtain ⟨hadm, hup, hend, hsum⟩ := h
  rw [mem_admSetQ (by omega)]
  refine ⟨(admissibleQ_iff_chainQ hodd hq bs hadm).mpr ⟨hup, hend⟩, ?_⟩
  rw [order_chainWordQ, hsum]
  omega

theorem chainWordQ_injOn (q n : ℕ) : Set.InjOn chainWordQ (chainBlocksQ q n) := by
  intro bs hbs bs' hbs' h
  unfold chainWordQ at h
  rw [List.cons.injEq] at h
  exact flatten_inj_of_admissibleQ bs bs' hbs.1 hbs'.1 h.2

theorem chainWordQ_surjOn (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    Set.SurjOn chainWordQ (chainBlocksQ q n) (admSetQ q (n + 1) : Set (List Bool)) := by
  intro s hs
  rw [Finset.mem_coe, mem_admSetQ (by omega)] at hs
  obtain ⟨bs, hsplit, hup, hend⟩ :=
    (admissibleQ_iff_exists_chainQ hodd hq s).mp ⟨hs.1, by omega⟩
  have hord := order_splitQ hsplit
  exact ⟨bs, ⟨hsplit.adm, hup, hend, by omega⟩, hsplit.eq.symm⟩

/-- `chainWordQ` maps `chainBlocksQ q n` one to one onto the admissible words of
    Order n + 1. -/
theorem chainWordQ_bijOn (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    Set.BijOn chainWordQ (chainBlocksQ q n) (admSetQ q (n + 1) : Set (List Bool)) :=
  ⟨fun _ h => chainWordQ_mem hodd hq h, chainWordQ_injOn q n, chainWordQ_surjOn hodd hq n⟩

/-- Chain decomposition: admissible words of Order n + 1 ≃ `chainBlocksQ q n`. -/
noncomputable def chainEquivQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (admSetQ q (n + 1) : Set (List Bool)) ≃ chainBlocksQ q n :=
  (Set.BijOn.equiv chainWordQ (chainWordQ_bijOn hodd hq n)).symm

theorem chainWordQ_chainEquivQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ)
    (s : (admSetQ q (n + 1) : Set (List Bool))) :
    chainWordQ (chainEquivQ hodd hq n s) = s := by
  unfold chainEquivQ
  exact congrArg Subtype.val ((Set.BijOn.equiv chainWordQ _).apply_symm_apply s)

/-- Admissible words of Order d in lexicographic order, indexed from 0. -/
noncomputable def admIndexQ (q d : ℕ) : Fin (admSetQ q d).card ≃o admSetQ q d :=
  (admSetQ q d).orderIsoOfFin rfl

/-- (d, c) code of a block: its Order and its index in that Order's sorted list. -/
noncomputable def blockCodeQ (q : ℕ) (b : List Bool) (hb : b ∈ admSetQ q (order b)) :
    Σ d, Fin (admSetQ q d).card :=
  ⟨order b, (admIndexQ q (order b)).symm ⟨b, hb⟩⟩

/-- Block of a (d, c) code. -/
noncomputable def codeBlockQ (x : Σ d, Fin (admSetQ q d).card) : List Bool :=
  (admIndexQ q x.1 x.2).1

theorem codeBlockQ_mem (x : Σ d, Fin (admSetQ q d).card) : codeBlockQ x ∈ admSetQ q x.1 :=
  (admIndexQ q x.1 x.2).2

theorem order_codeBlockQ (hq : 3 ≤ q) (x : Σ d, Fin (admSetQ q d).card) :
    order (codeBlockQ x) = x.1 :=
  ((mem_admSetQ (by omega) _ _).mp (codeBlockQ_mem x)).2

theorem codeBlockQ_blockCodeQ (b : List Bool) (hb : b ∈ admSetQ q (order b)) :
    codeBlockQ (blockCodeQ q b hb) = b := by
  unfold codeBlockQ blockCodeQ
  rw [OrderIso.apply_symm_apply]

theorem blockCodeQ_codeBlockQ (hq : 3 ≤ q) (x : Σ d, Fin (admSetQ q d).card)
    (hb : codeBlockQ x ∈ admSetQ q (order (codeBlockQ x))) :
    blockCodeQ q (codeBlockQ x) hb = x := by
  obtain ⟨d, i⟩ := x
  have key : ∀ e (h : e = d) (hm : (admIndexQ q d i).1 ∈ admSetQ q e),
      (⟨e, (admIndexQ q e).symm ⟨(admIndexQ q d i).1, hm⟩⟩ : Σ d, Fin (admSetQ q d).card) =
        ⟨d, i⟩ := by
    intro e h hm
    subst h
    simp
  exact key _ (order_codeBlockQ hq ⟨d, i⟩) hb

/-- (d, c) codes of Order n + 1: lists of codes with Order sum n whose Orders keep the
    level above 1 before the last one and bring it below 1 after it. -/
def chainCodesQ (q n : ℕ) : Set (List (Σ d, Fin (admSetQ q d).card)) :=
  {l | LevelUpQ q (l.map Sigma.fst).dropLast ∧ ¬LevelUpQ q (l.map Sigma.fst) ∧
    (l.map Sigma.fst).sum = n}

theorem mem_admSetQ_order (hq : 3 ≤ q) {b : List Bool} (h : AdmissibleQ q b) :
    b ∈ admSetQ q (order b) :=
  (mem_admSetQ (by omega) _ b).mpr ⟨h, rfl⟩

theorem map_fst_pmap_blockCodeQ (bs : List (List Bool))
    (h : ∀ b ∈ bs, b ∈ admSetQ q (order b)) :
    (bs.pmap (blockCodeQ q) h).map Sigma.fst = bs.map order := by
  rw [List.map_pmap]
  exact List.pmap_eq_map _

theorem map_order_map_codeBlockQ (hq : 3 ≤ q) (l : List (Σ d, Fin (admSetQ q d).card)) :
    (l.map codeBlockQ).map order = l.map Sigma.fst := by
  rw [List.map_map]
  exact List.map_congr_left (fun x _ => order_codeBlockQ hq x)

/-- Blocks ≃ their (d, c) codes. -/
noncomputable def chainCodeEquivQ (hq : 3 ≤ q) (n : ℕ) : chainBlocksQ q n ≃ chainCodesQ q n where
  toFun bs := ⟨bs.1.pmap (blockCodeQ q) (fun b hb => mem_admSetQ_order hq (bs.2.1 b hb)), by
    obtain ⟨_, hup, hend, hsum⟩ := bs.2
    refine ⟨?_, ?_, ?_⟩
    · rw [map_fst_pmap_blockCodeQ]
      exact hup
    · rw [map_fst_pmap_blockCodeQ]
      exact hend
    · rw [map_fst_pmap_blockCodeQ]
      exact hsum⟩
  invFun l := ⟨l.1.map codeBlockQ, by
    obtain ⟨hup, hend, hsum⟩ := l.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
      exact ((mem_admSetQ (by omega) _ _).mp (codeBlockQ_mem x)).1
    · rw [map_order_map_codeBlockQ hq]
      exact hup
    · rw [map_order_map_codeBlockQ hq]
      exact hend
    · rw [map_order_map_codeBlockQ hq]
      exact hsum⟩
  left_inv bs := by
    apply Subtype.ext
    simp only [List.map_pmap, codeBlockQ_blockCodeQ]
    exact List.pmap_eq_self.mpr fun _ _ => rfl
  right_inv l := by
    apply Subtype.ext
    simp only [List.pmap_map, blockCodeQ_codeBlockQ hq]
    exact List.pmap_eq_self.mpr fun _ _ => rfl

/-- (d, c) encoding: admissible words of Order n + 1 ≃ `chainCodesQ q n`. -/
noncomputable def codeEquivQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (admSetQ q (n + 1) : Set (List Bool)) ≃ chainCodesQ q n :=
  (chainEquivQ hodd hq n).trans (chainCodeEquivQ hq n)

end AcceleratedCollatz
