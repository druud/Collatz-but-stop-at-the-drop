-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracket
import AcceleratedCollatz.TCount
import AcceleratedCollatz.TWordQ

/-!
  Sweep map for the q-family (odd q ≥ 3): the steps of a word sorted by the level
  q^o / 2^j at their endpoints, highest first. The sweep maps admissible words of
  Order n to admissible words of Order n (`sweepQ_mem_admSetQ`, Thiel's argument).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Step indices of s, sorted by endpoint level, highest first. -/
def sweepIdxQ (q : ℕ) (s : List Bool) : List ℕ :=
  (List.range s.length).mergeSort (fun i k => decide (lvlQ q s (k + 1) ≤ lvlQ q s (i + 1)))

/-- Sweep map: the steps of s in the order of `sweepIdxQ`. -/
def sweepQ (q : ℕ) (s : List Bool) : List Bool := (sweepIdxQ q s).map (fun i => s.getD i false)

theorem sweepIdxQ_perm (q : ℕ) (s : List Bool) : (sweepIdxQ q s).Perm (List.range s.length) :=
  List.mergeSort_perm _ _

theorem sweepIdxQ_nodup (q : ℕ) (s : List Bool) : (sweepIdxQ q s).Nodup :=
  (sweepIdxQ_perm q s).nodup_iff.mpr List.nodup_range

theorem mem_sweepIdxQ {s : List Bool} {i : ℕ} : i ∈ sweepIdxQ q s ↔ i < s.length := by
  rw [(sweepIdxQ_perm q s).mem_iff, List.mem_range]

theorem sweepIdxQ_pairwise (q : ℕ) (s : List Bool) :
    (sweepIdxQ q s).Pairwise (fun i k => lvlQ q s (k + 1) ≤ lvlQ q s (i + 1)) := by
  have h := List.pairwise_mergeSort
    (le := fun i k => decide (lvlQ q s (k + 1) ≤ lvlQ q s (i + 1)))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hbc hab)
    (fun a b => by
      rcases le_total (lvlQ q s (b + 1)) (lvlQ q s (a + 1)) with h | h
      · simp [h]
      · simp [h])
    (List.range s.length)
  exact h.imp (fun hab => by simpa using hab)

theorem map_getD_range (s : List Bool) :
    (List.range s.length).map (fun i => s.getD i false) = s := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

/-- The sweep permutes the steps. -/
theorem sweepQ_perm (q : ℕ) (s : List Bool) : (sweepQ q s).Perm s := by
  have h := (sweepIdxQ_perm q s).map (fun i => s.getD i false)
  rw [map_getD_range] at h
  exact h

theorem length_sweepQ (q : ℕ) (s : List Bool) : (sweepQ q s).length = s.length :=
  (sweepQ_perm q s).length_eq

theorem seqProductQ_sweepQ (q : ℕ) (s : List Bool) :
    seqProductQ q (sweepQ q s) = seqProductQ q s :=
  ((sweepQ_perm q s).map (factorQ q)).prod_eq

theorem order_sweepQ (q : ℕ) (s : List Bool) : order (sweepQ q s) = order s :=
  ((sweepQ_perm q s).filter id).length_eq

/-- Levels after different step counts differ. -/
theorem lvlQ_ne_of_ne (hodd : Odd q) {s : List Bool} {i k : ℕ} (hi : i ≤ s.length)
    (hk : k ≤ s.length) (hne : i ≠ k) : lvlQ q s i ≠ lvlQ q s k := by
  intro heq
  have key : ∀ {a b : ℕ}, a ≤ s.length → b ≤ s.length → a < b → lvlQ q s a = lvlQ q s b →
      False := by
    intro a b ha hb hab he
    have h1 := lvlQ_mul_pow q ha
    have h2 := lvlQ_mul_pow q hb
    have hsplit : (2 : ℚ) ^ b = 2 ^ a * 2 ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    have hq : ((q ^ order (s.take b) : ℕ) : ℚ) =
        ((q ^ order (s.take a) * 2 ^ (b - a) : ℕ) : ℚ) := by
      push_cast
      rw [← h1, ← h2, ← he, hsplit]
      ring
    have hn : q ^ order (s.take b) = q ^ order (s.take a) * 2 ^ (b - a) := by
      exact_mod_cast hq
    have hoddp : (q ^ order (s.take b)) % 2 = 1 :=
      Nat.odd_iff.mp (hodd.pow)
    have heven : (q ^ order (s.take a) * 2 ^ (b - a)) % 2 = 0 := by
      have hba : b - a = (b - a - 1) + 1 := by omega
      rw [hba, pow_succ]
      simp [← mul_assoc, Nat.mul_mod_left]
    omega
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key hi hk h heq
  · exact key hk hi h heq.symm

/-- The steps whose endpoint levels reach t > 1, and no others, multiply to more than 1. -/
theorem prod_gt_one_of_upperQ (hq0 : 0 < q) (s : List Bool) (T : Finset ℕ) {t : ℚ} (ht : 1 < t)
    (hT : ∀ i ∈ T, i < s.length ∧ t ≤ lvlQ q s (i + 1))
    (hN : ∀ i < s.length, i ∉ T → lvlQ q s (i + 1) < t) (hne : T.Nonempty) :
    1 < ∏ i ∈ T, factorQ q (s.getD i false) := by
  let g : ℕ → ℚ := fun m => ∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hfac : ∀ i, 0 < factorQ q (s.getD i false) := by
    intro i
    unfold factorQ
    split_ifs
    · exact div_pos hq0' (by norm_num)
    · norm_num
  have hg_succ_mem : ∀ m, m ∈ T → g (m + 1) = g m * factorQ q (s.getD m false) := by
    intro m hm
    change ∏ i ∈ (Finset.range (m + 1)).filter (· ∈ T), factorQ q (s.getD i false) =
      (∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)) *
        factorQ q (s.getD m false)
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hm, ↓reduceIte]
    rw [Finset.prod_insert (by simp), mul_comm]
  have hg_succ_not : ∀ m, m ∉ T → g (m + 1) = g m := by
    intro m hm
    change ∏ i ∈ (Finset.range (m + 1)).filter (· ∈ T), factorQ q (s.getD i false) =
      ∏ i ∈ (Finset.range m).filter (· ∈ T), factorQ q (s.getD i false)
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [hm, ↓reduceIte]
  have hg_empty : ∀ m, (∀ i ∈ T, m ≤ i) → g m = 1 := by
    intro m hm
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have := hm i hi.2
    omega
  have inv : ∀ m ≤ s.length,
      lvlQ q s m < g m * t ∧ ((∃ i ∈ T, i < m) → 1 < g m) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [lvlQ_zero q, hg_empty 0 (fun i _ => Nat.zero_le i), one_mul]
        exact ht
      · rintro ⟨i, _, hi⟩
        omega
    | succ m ih =>
      intro hm
      obtain ⟨ihA, ihJ⟩ := ih (by omega)
      have hlt : m < s.length := by omega
      have hget : s[m]? = some (s.getD m false) := by
        simp [List.getD_eq_getElem?_getD, hlt]
      have hstep := lvlQ_succ q s hget
      by_cases hmT : m ∈ T
      · rw [hg_succ_mem m hmT]
        have hA : lvlQ q s (m + 1) < g m * factorQ q (s.getD m false) * t := by
          rw [hstep]
          have hf := hfac m
          nlinarith
        refine ⟨hA, fun _ => ?_⟩
        have ht_le := (hT m hmT).2
        have hpos : 0 < t := by linarith
        by_contra hle
        push Not at hle
        nlinarith
      · rw [hg_succ_not m hmT]
        have hlow := hN m hlt hmT
        by_cases hex : ∃ i ∈ T, i < m
        · have h1 := ihJ hex
          refine ⟨by nlinarith, fun _ => h1⟩
        · push Not at hex
          rw [hg_empty m hex]
          refine ⟨by linarith, ?_⟩
          rintro ⟨i, hi, him⟩
          have := hex i hi
          have hne' : i ≠ m := fun h => hmT (h ▸ hi)
          omega
  obtain ⟨_, hJ⟩ := inv s.length le_rfl
  obtain ⟨i, hi⟩ := hne
  have hfilter : (Finset.range s.length).filter (· ∈ T) = T := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨(hT k h).1, h⟩
  have h1 := hJ ⟨i, hi, (hT i hi).1⟩
  change 1 < ∏ i ∈ (Finset.range s.length).filter (· ∈ T), factorQ q (s.getD i false) at h1
  rwa [hfilter] at h1

/-- The sweep maps admissible words of Order n to admissible words of Order n. -/
theorem sweepQ_mem_admSetQ (hodd : Odd q) (hq2 : 2 ≤ q) {n : ℕ} {s : List Bool}
    (hs : s ∈ admSetQ q n) :
    sweepQ q s ∈ admSetQ q n := by
  rw [mem_admSetQ hq2 n] at hs ⊢
  obtain ⟨hA, hord⟩ := hs
  refine ⟨⟨?_, ?_⟩, by rw [order_sweepQ, hord]⟩
  · intro m hm1 hmL
    rw [length_sweepQ] at hmL
    set l := sweepIdxQ q s with hl
    have hnd : l.Nodup := sweepIdxQ_nodup q s
    have hpw := sweepIdxQ_pairwise q s
    have hlen : l.length = s.length := by
      rw [(sweepIdxQ_perm q s).length_eq, List.length_range]
    have hsplit : (l.take m ++ l.drop m).Nodup := by
      rw [List.take_append_drop]
      exact hnd
    obtain ⟨hnd1, _, hdisj⟩ := List.nodup_append.mp hsplit
    set T := (l.take m).toFinset with hTdef
    have hprod : seqProductQ q ((sweepQ q s).take m) = ∏ i ∈ T, factorQ q (s.getD i false) := by
      rw [List.prod_toFinset _ hnd1]
      unfold sweepQ seqProductQ
      rw [← List.map_take, List.map_map]
      rfl
    rw [hprod]
    have hmemT : ∀ i ∈ T, i < s.length := by
      intro i hi
      rw [List.mem_toFinset] at hi
      exact mem_sweepIdxQ.mp (List.mem_of_mem_take hi)
    have hbelow : ∀ i ∈ T, ∀ k, k < s.length → k ∉ T → lvlQ q s (k + 1) < lvlQ q s (i + 1) := by
      intro i hi k hk hkT
      rw [List.mem_toFinset] at hi hkT
      have hkl : k ∈ l := mem_sweepIdxQ.mpr hk
      rw [← List.take_append_drop m l, List.mem_append] at hkl
      have hkd : k ∈ l.drop m := hkl.resolve_left hkT
      have hle := hpw.rel_of_mem_take_of_mem_drop hi hkd
      have hik : i ≠ k := hdisj i hi k hkd
      have hi' := mem_sweepIdxQ.mp (List.mem_of_mem_take hi)
      exact lt_of_le_of_ne hle (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
    have hne : T.Nonempty := by
      rw [List.toFinset_nonempty_iff, ← List.length_pos_iff]
      rw [List.length_take]
      omega
    have hgt1 : ∀ i ∈ T, 1 < lvlQ q s (i + 1) := by
      intro i hi
      have hiL := hmemT i hi
      by_cases hlast : i + 1 < s.length
      · exact hA.prefix_gt (i + 1) (by omega) hlast
      · exfalso
        have hdrop : (l.drop m).length ≠ 0 := by
          rw [List.length_drop]
          omega
        obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos
          (Nat.pos_of_ne_zero hdrop))
        have hkL : k < s.length := mem_sweepIdxQ.mp (List.mem_of_mem_drop hk)
        have hkT : k ∉ T := by
          rw [List.mem_toFinset]
          intro hkt
          exact hdisj k hkt k hk rfl
        have hlt := hbelow i hi k hkL hkT
        have hik : k ≠ i := by
          intro h
          exact hkT (h ▸ hi)
        have hk1 : k + 1 < s.length := by omega
        have hkgt := hA.prefix_gt (k + 1) (by omega) hk1
        have hend : lvlQ q s (i + 1) < 1 := by
          have heq : i + 1 = s.length := by omega
          rw [heq]
          unfold lvlQ
          rw [List.take_length]
          exact hA.lt_one
        change 1 < lvlQ q s (k + 1) at hkgt
        linarith
    apply prod_gt_one_of_upperQ (by omega) s T (t := T.inf' hne (fun i => lvlQ q s (i + 1)))
    · rw [Finset.lt_inf'_iff]
      exact hgt1
    · exact fun i hi => ⟨hmemT i hi, Finset.inf'_le _ hi⟩
    · intro k hk hkT
      rw [Finset.lt_inf'_iff]
      exact fun i hi => hbelow i hi k hk hkT
    · exact hne
  · rw [seqProductQ_sweepQ]
    exact hA.lt_one

end AcceleratedCollatz
