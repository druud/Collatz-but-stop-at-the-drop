-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Zeta.TNoDropCount
import AcceleratedCollatz.TBinomial
import AcceleratedCollatz.TAdmSet

/-!
  The words that never drop, from below (C195; zeta paper, Theorem thm:nodrop).

  `noDropCount_mul_le` bounds S(k) from above. From below, in natural numbers: let a, b, t be such
  that 2^(a+b) < 3^a (a share a/(a+b) of ones above 1/log2 3) and 2^(t+b) < 3^t. Then a run of
  t ones followed by any m blocks of a+b letters with a ones each never drops: the run lifts the
  level above 2^b, each block multiplies it by 3^a/2^(a+b) > 1, and inside a block at most b
  zeros have come. These words are distinct, so

    C(a+b, a)^m ≤ S(t + (a+b) m)        (`choose_pow_le_noDropCount`).

  When a + b grows with a/(a+b) falling to p = 1/log2 3, C(a+b, a)^(1/(a+b)) tends to 2^H(p),
  the value of the upper bound: H(p) is the exact growth rate of S(k), both ways in integers
  (S(k) grows with k, `noDropCount_le_succ`).
  The words form a product set, block by block, so the same construction is a self-similar subset
  of E of dimension log2 C(a+b, a)/(a+b) (not formalized).
-/

namespace AcceleratedCollatz

open Finset

/-- Every nonempty prefix of a list has level above 1. -/
def NoDropL (l : List Bool) : Prop :=
  ∀ j, 1 ≤ j → j ≤ l.length → 2 ^ j < 3 ^ order (l.take j)

theorem order_replicate_true (j : ℕ) : order (List.replicate j true) = j := by
  unfold order; simp

/-- The ones of `v` before `j` are the ones of the first `j` letters of `List.ofFn v`. -/
theorem onesUpTo_eq_order : ∀ {k : ℕ} (v : Fin k → Bool) (j : ℕ),
    onesUpTo v j = order ((List.ofFn v).take j)
  | 0, v, j => by
    unfold onesUpTo; simp [order]
  | k + 1, v, j => by
    have hsplit : List.ofFn v = List.ofFn (Fin.init v) ++ [v (Fin.last k)] := by
      rw [List.ofFn_succ', List.concat_eq_append]; rfl
    rcases Nat.lt_or_ge k j with hj | hj
    · -- all letters
      have htk : (List.ofFn v).take j = List.ofFn v := List.take_of_length_le (by simp; omega)
      have hk : (List.ofFn (Fin.init v)).take k = List.ofFn (Fin.init v) :=
        List.take_of_length_le (by simp)
      have ih := onesUpTo_eq_order (Fin.init v) k
      rw [hk] at ih
      rw [htk, hsplit, order_append, ← ih, ← onesUpTo_init v le_rfl]
      unfold onesUpTo
      rw [card_filter, card_filter, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc]
      have e : ∀ i : Fin k, (if (i : ℕ) < j ∧ v i.castSucc = true then 1 else 0) =
          (if (i : ℕ) < k ∧ v i.castSucc = true then 1 else 0) := by
        intro i
        have : (i : ℕ) < k := i.isLt
        simp [this, show (i : ℕ) < j by omega]
      rw [Finset.sum_congr rfl (fun i _ => e i)]
      cases v (Fin.last k) <;> simp [order, hj]
    · rw [onesUpTo_init v hj, onesUpTo_eq_order (Fin.init v) j, hsplit,
        List.take_append_of_le_length (by simp; omega)]

/-- A list of length k read as a word `Fin k → Bool`. -/
def toWord (k : ℕ) (l : List Bool) : Fin k → Bool := fun i => l.getD i false

theorem ofFn_toWord {k : ℕ} {l : List Bool} (hl : l.length = k) : List.ofFn (toWord k l) = l := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [toWord, List.getElem?_eq_getElem h2]

theorem noDrop_toWord {k : ℕ} {l : List Bool} (hl : l.length = k) (h : NoDropL l) :
    NoDrop (toWord k l) := by
  intro j h1 hj
  rw [onesUpTo_eq_order, ofFn_toWord hl]
  exact h j h1 (by omega)

/-- S(k) is at least the number of lists of length k that never drop, from any family. -/
theorem card_le_noDropCount {k : ℕ} {s : Finset (List Bool)}
    (hs : ∀ l ∈ s, l.length = k ∧ NoDropL l) : s.card ≤ noDropCount k := by
  unfold noDropCount
  apply card_le_card_of_injOn (toWord k)
  · intro l hl
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    exact noDrop_toWord (hs l hl).1 (hs l hl).2
  · intro l hl l' hl' he
    rw [← ofFn_toWord (hs l hl).1, ← ofFn_toWord (hs l' hl').1]
    exact congrArg List.ofFn he

/-- A run of t ones, then m blocks of a+b letters with a ones each. -/
def runBlockSet (t a b : ℕ) : ℕ → Finset (List Bool)
  | 0 => {List.replicate t true}
  | m + 1 => ((runBlockSet t a b m) ×ˢ wordSet (a + b) a).image (fun p => p.1 ++ p.2)

theorem length_of_mem_runBlockSet {t a b : ℕ} : ∀ {m : ℕ} {l : List Bool},
    l ∈ runBlockSet t a b m → l.length = t + (a + b) * m
  | 0, l, h => by
    simp only [runBlockSet, mem_singleton] at h; subst h; simp
  | m + 1, l, h => by
    simp only [runBlockSet, mem_image, mem_product, mem_wordSet] at h
    obtain ⟨⟨w, B⟩, ⟨hw, hB⟩, rfl⟩ := h
    rw [List.length_append, length_of_mem_runBlockSet hw, hB.1]; ring

theorem card_runBlockSet (t a b : ℕ) : ∀ m, (runBlockSet t a b m).card = (a + b).choose a ^ m
  | 0 => by simp [runBlockSet]
  | m + 1 => by
    rw [runBlockSet, card_image_of_injOn, card_product, card_runBlockSet t a b m, card_wordSet,
      pow_succ]
    rintro ⟨w, B⟩ hp ⟨w', B'⟩ hp' he
    simp only [coe_product, Set.mem_prod, mem_coe] at hp hp'
    have hl : w.length = w'.length := by
      rw [length_of_mem_runBlockSet hp.1, length_of_mem_runBlockSet hp'.1]
    obtain ⟨h1, h2⟩ := List.append_inj he hl
    exact Prod.ext h1 h2

/-- The words of `runBlockSet` never drop, and end with level above 2^b. -/
theorem noDropL_of_mem_runBlockSet {t a b : ℕ} (ht : 2 ^ (t + b) < 3 ^ t)
    (hab : 2 ^ (a + b) < 3 ^ a) : ∀ {m : ℕ} {l : List Bool},
    l ∈ runBlockSet t a b m → NoDropL l ∧ 2 ^ (l.length + b) < 3 ^ order l
  | 0, l, h => by
    simp only [runBlockSet, mem_singleton] at h; subst h
    refine ⟨fun j h1 hj => ?_, by rw [List.length_replicate, order_replicate_true]; exact ht⟩
    rw [List.length_replicate] at hj
    rw [List.take_replicate, min_eq_left hj, order_replicate_true]
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  | m + 1, l, h => by
    simp only [runBlockSet, mem_image, mem_product, mem_wordSet] at h
    obtain ⟨⟨w, B⟩, ⟨hw, hBl, hBo⟩, rfl⟩ := h
    dsimp only at hw hBl hBo ⊢
    obtain ⟨hwd, hwe⟩ := noDropL_of_mem_runBlockSet ht hab hw
    refine ⟨fun j h1 hj => ?_, ?_⟩
    · rw [List.length_append] at hj
      rcases Nat.lt_or_ge w.length j with hjw | hjw
      · obtain ⟨r, rfl⟩ : ∃ r, j = w.length + r := ⟨j - w.length, by omega⟩
        rw [List.take_length_add_append, order_append]
        -- the ones of the first r letters of B: at least r - b
        have hsplit := order_append (B.take r) (B.drop r)
        rw [List.take_append_drop] at hsplit
        have hd := order_le_length (B.drop r)
        rw [List.length_drop] at hd
        have hc : r ≤ order (B.take r) + b := by omega
        rcases le_or_gt r b with hrb | hrb
        · calc 2 ^ (w.length + r) ≤ 2 ^ (w.length + b) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
            _ < 3 ^ order w := hwe
            _ ≤ 3 ^ (order w + order (B.take r)) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
        · calc 2 ^ (w.length + r) = 2 ^ (w.length + b) * 2 ^ (r - b) := by
                rw [← pow_add]; congr 1; omega
            _ < 3 ^ order w * 3 ^ (r - b) :=
                Nat.mul_lt_mul_of_lt_of_le hwe
                  (Nat.pow_le_pow_left (by norm_num) _) (by positivity)
            _ ≤ 3 ^ (order w + order (B.take r)) := by
                rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      · rw [List.take_append_of_le_length hjw]
        exact hwd j h1 hjw
    · rw [List.length_append, order_append, hBl, hBo]
      calc 2 ^ (w.length + (a + b) + b) = 2 ^ (w.length + b) * 2 ^ (a + b) := by
            rw [← pow_add]; congr 1; omega
        _ < 3 ^ order w * 3 ^ a := Nat.mul_lt_mul'' hwe hab
        _ = 3 ^ (order w + a) := (pow_add _ _ _).symm

/-- C195: for 2^(a+b) < 3^a and 2^(t+b) < 3^t, C(a+b, a)^m ≤ S(t + (a+b) m). -/
theorem choose_pow_le_noDropCount {t a b : ℕ} (ht : 2 ^ (t + b) < 3 ^ t)
    (hab : 2 ^ (a + b) < 3 ^ a) (m : ℕ) :
    (a + b).choose a ^ m ≤ noDropCount (t + (a + b) * m) := by
  rw [← card_runBlockSet t a b m]
  exact card_le_noDropCount fun l hl =>
    ⟨length_of_mem_runBlockSet hl, (noDropL_of_mem_runBlockSet ht hab hl).1⟩

/-- One more letter, at least as many words that never drop (append a one). -/
theorem noDropCount_le_succ (k : ℕ) : noDropCount k ≤ noDropCount (k + 1) := by
  unfold noDropCount
  apply card_le_card_of_injOn (fun v : Fin k → Bool => (Fin.snoc v true : Fin (k + 1) → Bool))
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    rw [noDrop_succ_iff, Fin.init_snoc]
    refine ⟨hv, ?_⟩
    rw [onesUpTo_eq_order, List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [List.take_of_length_le (by simp), order_append]
    have h1 : order [true] = 1 := rfl
    rw [h1, pow_succ, pow_succ]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [order]
    · have := hv k hk le_rfl
      rw [onesUpTo_eq_order, List.take_of_length_le (by simp)] at this
      exact Nat.mul_lt_mul_of_lt_of_le this (by norm_num) (by norm_num)
  · intro v _ v' _ he
    have := congrArg Fin.init he
    simpa [Fin.init_snoc] using this

/-! The first drops are the drop words (C201): S(k) = 2^k - Σ_{p2(m) ≤ k} N(m) 2^(k - p2(m)). -/

theorem succ_le_p2_of (m : ℕ) : m + 1 ≤ p2_of m := by
  unfold p2_of
  have : m ≤ Nat.log 2 (3 ^ m) :=
    Nat.le_log_of_pow_le (by norm_num) (Nat.pow_le_pow_left (by norm_num) m)
  omega

/-- A word drops first at its end iff it is a drop word. -/
theorem firstDrop_iff_admissible {j : ℕ} (v : Fin (j + 1) → Bool) :
    (NoDrop (Fin.init v) ∧ 3 ^ onesUpTo v (j + 1) ≤ 2 ^ (j + 1)) ↔
      Admissible (List.ofFn v) := by
  have hlen : (List.ofFn v).length = j + 1 := List.length_ofFn
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi1 hi2 => ?_, ?_⟩
    · rw [hlen] at hi2
      have := h1 i hi1 (by omega)
      rw [← onesUpTo_init v (by omega), onesUpTo_eq_order] at this
      rw [one_lt_seqProduct_iff, List.length_take, min_eq_left (by omega)]
      exact this
    · rw [seqProduct_lt_one_iff, hlen]
      rw [onesUpTo_eq_order, List.take_of_length_le (by omega)] at h2
      rcases h2.lt_or_eq with h | h
      · exact h
      · exfalso
        have h3 : (3 : ℕ) ^ order (List.ofFn v) % 2 = 1 := by
          rw [Nat.pow_mod]; simp
        rw [h, pow_succ] at h3
        simp at h3
  · intro ha
    refine ⟨fun i hi1 hi2 => ?_, ?_⟩
    · rw [← onesUpTo_init v hi2, onesUpTo_eq_order]
      have := ha.prefix_gt i hi1 (by omega)
      rw [one_lt_seqProduct_iff, List.length_take, min_eq_left (by omega)] at this
      exact this
    · have := ha.lt_one
      rw [seqProduct_lt_one_iff, hlen] at this
      rw [onesUpTo_eq_order, List.take_of_length_le (by omega)]
      exact this.le

/-- The first drops at length j+1 are the drop words of the Orders m with p2(m) = j+1. -/
theorem firstDropCount_eq (j : ℕ) :
    firstDropCount j = ∑ m ∈ range (j + 1), if p2_of m = j + 1 then (admSet m).card else 0 := by
  rw [← sum_filter, ← card_biUnion]
  · unfold firstDropCount
    apply card_bij (fun v _ => List.ofFn v)
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      rw [firstDrop_iff_admissible] at hv
      simp only [mem_biUnion, mem_filter, mem_range, mem_admSet]
      have hl := admissible_length _ hv
      rw [List.length_ofFn] at hl
      refine ⟨order (List.ofFn v), ⟨?_, hl.symm⟩, hv, rfl⟩
      have := succ_le_p2_of (order (List.ofFn v)); omega
    · intro v _ w _ h; exact List.ofFn_injective h
    · intro l hl
      simp only [mem_biUnion, mem_filter, mem_range, mem_admSet] at hl
      obtain ⟨m, ⟨_, hm⟩, ha, ho⟩ := hl
      have hlen : l.length = j + 1 := by rw [admissible_length _ ha, ho, hm]
      refine ⟨toWord (j + 1) l, ?_, ofFn_toWord hlen⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [firstDrop_iff_admissible, ofFn_toWord hlen]; exact ha
  · intro m _ m' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro l h1 h2
    rw [mem_admSet] at h1 h2
    exact hne (h1.2.symm.trans h2.2)

/-- C201: S(k) + Σ_{m : p2(m) ≤ k} N(m) 2^(k - p2(m)) = 2^k, N(m) = |admSet m| (zeta paper,
    before Corollary cor:norate). -/
theorem noDropCount_add_sum_admSet (k : ℕ) :
    noDropCount k + ∑ m ∈ (range (k + 1)).filter (fun m => p2_of m ≤ k),
      (admSet m).card * 2 ^ (k - p2_of m) = 2 ^ k := by
  rw [← noDropCount_add_sum k]
  congr 1
  have h1 : ∀ j ∈ range k, firstDropCount j * 2 ^ (k - 1 - j) =
      ∑ m ∈ range (k + 1),
        if p2_of m = j + 1 then (admSet m).card * 2 ^ (k - p2_of m) else 0 := by
    intro j hj
    rw [mem_range] at hj
    rw [firstDropCount_eq, sum_mul, ← sum_range_add_sum_Ico _ (show j + 1 ≤ k + 1 by omega)]
    have hz : ∑ m ∈ Ico (j + 1) (k + 1),
        (if p2_of m = j + 1 then (admSet m).card * 2 ^ (k - p2_of m) else 0) = 0 := by
      apply sum_eq_zero
      intro m hm
      rw [mem_Ico] at hm
      have := succ_le_p2_of m
      rw [ite_eq_right_iff]; intro h; omega
    rw [hz, add_zero]
    apply sum_congr rfl
    intro m _
    split_ifs with h
    · rw [h, show k - 1 - j = k - (j + 1) by omega]
    · simp
  rw [sum_congr rfl h1, sum_comm, sum_filter]
  apply sum_congr rfl
  intro m _
  have hp := succ_le_p2_of m
  have e : ∀ j, (p2_of m = j + 1) ↔ (p2_of m - 1 = j) := fun j => by omega
  simp_rw [e]
  rw [sum_ite_eq]
  by_cases h : p2_of m ≤ k
  · simp only [h, ↓reduceIte, mem_range, show p2_of m - 1 < k by omega]
  · simp only [h, ↓reduceIte, mem_range, show ¬ p2_of m - 1 < k by omega]

/-- Small values of the drop-word form: S(5) = 2^5 - N(0) 2^4 - N(1) 2^3 - N(2) 2^1 - N(3) 2^0. -/
example : noDropCount 5 = 4 := by decide

end AcceleratedCollatz
