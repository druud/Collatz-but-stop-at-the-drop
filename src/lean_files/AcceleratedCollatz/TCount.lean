-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainEquiv

/-!
  Counting recursion for admissible PVs (A100982). With `admSet n` the admissible
  PVs of Order n, `comps n` the compositions of n (positive parts) and
  `blockSet os` the block lists with Orders os:
  |admSet (n+1)| = Σ over compositions os of n with `ValidOrders os` of
  ∏ |admSet o_i| (`card_admSet_succ`). The block lists over the valid compositions
  of n are `chainBlocks n` (`mem_sigma_blockSet`), which `chainWord` maps one to
  one onto `admSet (n + 1)`.
-/

namespace AcceleratedCollatz

variable (n : ℕ)

/-- Compositions of n with positive parts (fuel f ≥ n). -/
def compsAux : ℕ → ℕ → List (List ℕ)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | f + 1, n + 1 =>
    (List.range (n + 1)).flatMap (fun j => (compsAux f (n - j)).map (List.cons (j + 1)))

/-- Compositions of n with positive parts. -/
def comps (n : ℕ) : List (List ℕ) := compsAux n n

/-- Membership in `compsAux f n` for n ≤ f. -/
theorem mem_compsAux : ∀ (f n : ℕ), n ≤ f → ∀ os : List ℕ,
    os ∈ compsAux f n ↔ (∀ o ∈ os, 1 ≤ o) ∧ os.sum = n
  | f, 0, _, os => by
    cases f with
    | zero =>
      cases os with
      | nil =>
        simp [compsAux]
      | cons o t =>
        constructor
        · intro h
          simp [compsAux] at h
        · rintro ⟨h1, h2⟩
          have := h1 o List.mem_cons_self
          rw [List.sum_cons] at h2
          omega
    | succ f =>
      cases os with
      | nil =>
        simp [compsAux]
      | cons o t =>
        constructor
        · intro h
          simp [compsAux] at h
        · rintro ⟨h1, h2⟩
          have := h1 o List.mem_cons_self
          rw [List.sum_cons] at h2
          omega
  | 0, n + 1, h, _ => by
    omega
  | f + 1, n + 1, h, os => by
    simp only [compsAux, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨j, hj, t, ht, rfl⟩
      rw [mem_compsAux f (n - j) (by omega) t] at ht
      refine ⟨?_, ?_⟩
      · intro o ho
        rcases List.mem_cons.mp ho with rfl | ho'
        · omega
        · exact ht.1 o ho'
      · rw [List.sum_cons, ht.2]
        omega
    · rintro ⟨hpos, hsum⟩
      cases os with
      | nil =>
        simp at hsum
      | cons o t =>
        have ho := hpos o List.mem_cons_self
        rw [List.sum_cons] at hsum
        refine ⟨o - 1, by omega, t, ?_, by rw [Nat.sub_add_cancel ho]⟩
        rw [mem_compsAux f (n - (o - 1)) (by omega) t]
        refine ⟨fun x hx => hpos x (List.mem_cons_of_mem o hx), ?_⟩
        omega

/-- Membership in `comps n`. -/
theorem mem_comps (os : List ℕ) :
    os ∈ comps n ↔ (∀ o ∈ os, 1 ≤ o) ∧ os.sum = n :=
  mem_compsAux n n le_rfl os

/-- Block lists with Orders os, every block admissible. -/
def blockSet : List ℕ → Finset (List (List Bool))
  | [] => {[]}
  | o :: os => (admSet o ×ˢ blockSet os).image (fun p => p.1 :: p.2)

/-- Membership in `blockSet os`. -/
theorem mem_blockSet : ∀ (os : List ℕ) (bs : List (List Bool)),
    bs ∈ blockSet os ↔ bs.map order = os ∧ ∀ b ∈ bs, Admissible b
  | [], bs => by
    cases bs with
    | nil =>
      simp [blockSet]
    | cons b t =>
      simp [blockSet]
  | o :: os, bs => by
    simp only [blockSet, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨b, t, ⟨hb, ht⟩, rfl⟩
      rw [mem_admSet] at hb
      rw [mem_blockSet os t] at ht
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
        · rw [mem_admSet]
          exact ⟨hadm b List.mem_cons_self, hmap.1⟩
        · rw [mem_blockSet os t]
          exact ⟨hmap.2, fun c hc => hadm c (List.mem_cons_of_mem b hc)⟩

/-- Number of block lists with Orders os: the product of a(o). -/
theorem card_blockSet : ∀ os : List ℕ,
    (blockSet os).card = (os.map (fun o => (admSet o).card)).prod
  | [] => by
    simp [blockSet]
  | o :: os => by
    rw [blockSet, Finset.card_image_of_injective, Finset.card_product, card_blockSet os,
      List.map_cons, List.prod_cons]
    intro p q h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2

/-- Valid compositions of n. -/
def validComps (n : ℕ) : Finset (List ℕ) :=
  (comps n).toFinset.filter ValidOrders

/-- The block lists over the valid compositions of n are `chainBlocks n`. -/
theorem mem_sigma_blockSet (os : List ℕ) (bs : List (List Bool)) :
    (⟨os, bs⟩ : Σ _ : List ℕ, List (List Bool)) ∈ (validComps n).sigma blockSet ↔
      bs ∈ chainBlocks n ∧ bs.map order = os := by
  simp only [Finset.mem_sigma, validComps, Finset.mem_filter, List.mem_toFinset, mem_comps,
    mem_blockSet]
  constructor
  · rintro ⟨⟨⟨hpos, hsum⟩, hvalid⟩, rfl, hadm⟩
    exact ⟨⟨fun b hb => ⟨hadm b hb, hpos _ (List.mem_map_of_mem hb)⟩, hvalid, hsum⟩, rfl⟩
  · rintro ⟨⟨hcb, hvalid, hsum⟩, rfl⟩
    refine ⟨⟨⟨fun o ho => ?_, hsum⟩, hvalid⟩, rfl, fun b hb => (hcb b hb).adm⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ho
    exact (hcb b hb).order_pos

/-- A100982 recursion: |admSet (n+1)| = Σ over valid compositions os of n of ∏ |admSet o_i|. -/
theorem card_admSet_succ :
    (admSet (n + 1)).card =
      ∑ os ∈ validComps n, (os.map (fun o => (admSet o).card)).prod := by
  have himg : ((validComps n).sigma blockSet).image (fun p => chainWord p.2) =
      admSet (n + 1) := by
    ext s
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨os, bs⟩, hp, rfl⟩
      exact chainWord_mem ((mem_sigma_blockSet n os bs).mp hp).1
    · intro hs
      obtain ⟨bs, hbs, rfl⟩ := chainWord_surjOn n (Finset.mem_coe.mpr hs)
      exact ⟨⟨bs.map order, bs⟩, (mem_sigma_blockSet n _ bs).mpr ⟨hbs, rfl⟩, rfl⟩
  have hinj : Set.InjOn (fun p : Σ _ : List ℕ, List (List Bool) => chainWord p.2)
      ((validComps n).sigma blockSet) := by
    rintro ⟨os, bs⟩ hp ⟨os', bs'⟩ hq h
    rw [Finset.mem_coe, mem_sigma_blockSet] at hp hq
    have hbb : bs = bs' := chainWord_injOn n hp.1 hq.1 h
    subst hbb
    rw [← hp.2, ← hq.2]
  rw [← himg, Finset.card_image_of_injOn hinj, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro os _
  exact card_blockSet os

-- The first terms of A100982: a(1..7) = 1, 1, 2, 3, 7, 12, 30.
set_option linter.hashCommand false in
#guard (List.range 7).map (fun n => (admSet (n + 1)).card) = [1, 1, 2, 3, 7, 12, 30]

end AcceleratedCollatz
