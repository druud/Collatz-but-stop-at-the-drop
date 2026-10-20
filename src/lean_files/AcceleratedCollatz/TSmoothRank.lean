-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TFloorSum
import AcceleratedCollatz.TSmoothPlace

/-!
  The place of a 3-smooth number among those of its number of binary digits. Below
  2^(B - p2(i)) 3^i (B binary digits) lie the 3-smooth numbers below 2^(B - 1) and those
  of B binary digits with a smaller block factor (`card_smoothBelowAt_class`). Along
  k a mod (a + b) for the last record Orders a, b below N, the Orders below N with a
  smaller block factor than that at k are those at the k' < k (`card_blockFactor_lt_eq`),
  and all of them occur below a + b (`card_mul_mod_lt`). The A003586 program counts them
  by floor sums: k + fs(k, M, a, 0) - fs(k, M, a, M - N) (`classCount_eq`).
-/

namespace AcceleratedCollatz

open Finset

/-- Below 2^(B - p2(i)) 3^i, B ≥ 1 and p2(i) ≤ B, lie the 3-smooth numbers below
    2^(B - 1) and the 2^(B - p2(i')) 3^i' with i' below the round-up of B log 2 / log 3
    and a smaller block factor. -/
theorem card_smoothBelowAt_class {B i : ℕ} (hB : 1 ≤ B) (hi : p2_of i ≤ B) :
    (smoothBelowAt (B - p2_of i) i).card = (smoothBelow (B - 1)).card +
      ((range (Nat.clog 3 (2 ^ B))).filter (fun i' => blockFactor i' < blockFactor i)).card := by
  set C := (range (Nat.clog 3 (2 ^ B))).filter (fun i' => blockFactor i' < blockFactor i)
    with hC
  have hx : 2 ^ (B - 1) ≤ 2 ^ (B - p2_of i) * 3 ^ i ∧ 2 ^ (B - p2_of i) * 3 ^ i < 2 ^ B :=
    (smooth_digits hB).mpr (by omega)
  have hinj : Set.InjOn (fun i' => (B - p2_of i', i')) C := by
    intro x _ y _ hxy
    exact (Prod.mk.inj hxy).2
  have hsplit : smoothBelowAt (B - p2_of i) i =
      smoothBelow (B - 1) ∪ C.image (fun i' => (B - p2_of i', i')) := by
    ext ⟨j', i'⟩
    rw [mem_smoothBelowAt, mem_union, mem_smoothBelow, mem_image]
    dsimp only
    constructor
    · intro hlt
      have hlB : 2 ^ j' * 3 ^ i' < 2 ^ B := lt_trans hlt hx.2
      rw [smooth_lt_two_pow_iff] at hlB
      rcases Nat.lt_or_ge (j' + p2_of i') B with hl | hge
      · left
        rw [smooth_lt_two_pow_iff]
        omega
      · right
        refine ⟨i', ?_, ?_⟩
        · rw [hC, mem_filter, mem_range, ← p2_of_le_iff_lt_clog]
          refine ⟨by omega, ?_⟩
          have hj : j' = B - p2_of i' := by omega
          rw [hj] at hlt
          exact (smooth_class_lt_iff (by omega) hi).mp hlt
        · congr 1
          omega
    · rintro (hlow | ⟨i'', hmem, heq⟩)
      · exact lt_of_lt_of_le hlow hx.1
      · rw [hC, mem_filter, mem_range, ← p2_of_le_iff_lt_clog] at hmem
        have he := Prod.mk.inj heq
        change B - p2_of i'' = j' ∧ i'' = i' at he
        rw [← he.1, ← he.2]
        exact (smooth_class_lt_iff hmem.1 hi).mpr hmem.2
  have hdisj : Disjoint (smoothBelow (B - 1)) (C.image (fun i' => (B - p2_of i', i'))) := by
    rw [disjoint_left]
    rintro ⟨j', i'⟩ hlow himg
    rw [mem_smoothBelow, smooth_lt_two_pow_iff] at hlow
    dsimp only at hlow
    rw [mem_image] at himg
    obtain ⟨i'', hmem, heq⟩ := himg
    rw [hC, mem_filter, mem_range, ← p2_of_le_iff_lt_clog] at hmem
    have he := Prod.mk.inj heq
    change B - p2_of i'' = j' ∧ i'' = i' at he
    rw [← he.2] at hlow
    omega
  rw [hsplit, card_union_of_disjoint hdisj, card_image_of_injOn hinj]

/-- For the last record Orders a, b below N ≤ a + b and k < a + b:
    the Orders below N with a smaller block factor are the k' a mod (a + b) below N with
    k' < k. -/
theorem card_blockFactor_lt_eq {a b N k : ℕ} (h : LastRecords a b N) (hN : N ≤ a + b)
    (hk : k < a + b) :
    ((range N).filter (fun i' => blockFactor i' < blockFactor (k * a % (a + b)))).card =
      ((range k).filter (fun k' => k' * a % (a + b) < N)).card := by
  symm
  apply card_bij (fun k' _ => k' * a % (a + b))
  · intro k' hk'
    rw [mem_filter, mem_range] at hk' ⊢
    exact ⟨hk'.2, blockFactor_mul_mod_lt h hk'.1 hk⟩
  · intro k1 hk1 k2 hk2 heq
    rw [mem_filter, mem_range] at hk1 hk2
    rcases Nat.lt_trichotomy k1 k2 with hlt | hEq | hgt
    · have := blockFactor_mul_mod_lt h hlt (by omega)
      rw [heq] at this
      exact absurd this (lt_irrefl _)
    · exact hEq
    · have := blockFactor_mul_mod_lt h hgt (by omega)
      rw [heq] at this
      exact absurd this (lt_irrefl _)
  · intro i' hi'
    rw [mem_filter, mem_range] at hi'
    obtain ⟨k', hk'M, hk'i⟩ := exists_mul_mod_eq_of_lastRecords h (i := i') (by omega)
    refine ⟨k', ?_, hk'i⟩
    rw [mem_filter, mem_range]
    refine ⟨?_, by omega⟩
    rcases Nat.lt_trichotomy k' k with hlt | hEq | hgt
    · exact hlt
    · rw [hEq] at hk'i
      rw [← hk'i] at hi'
      exact absurd hi'.2 (lt_irrefl _)
    · have := blockFactor_mul_mod_lt h hgt hk'M
      rw [hk'i] at this
      exact absurd (lt_trans hi'.2 this) (lt_irrefl _)

/-- For the last record Orders a, b below N ≤ a + b: N of the k < a + b have
    k a mod (a + b) < N. -/
theorem card_mul_mod_lt {a b N : ℕ} (h : LastRecords a b N) (hN : N ≤ a + b) :
    ((range (a + b)).filter (fun k => k * a % (a + b) < N)).card = N := by
  conv_rhs => rw [← card_range N]
  apply card_bij (fun k _ => k * a % (a + b))
  · intro k hk
    rw [mem_filter] at hk
    rw [mem_range]
    exact hk.2
  · intro k1 hk1 k2 hk2 heq
    rw [mem_filter, mem_range] at hk1 hk2
    rcases Nat.lt_trichotomy k1 k2 with hlt | hEq | hgt
    · have := blockFactor_mul_mod_lt h hlt hk2.1
      rw [heq] at this
      exact absurd this (lt_irrefl _)
    · exact hEq
    · have := blockFactor_mul_mod_lt h hgt hk1.1
      rw [heq] at this
      exact absurd this (lt_irrefl _)
  · intro i' hi'
    rw [mem_range] at hi'
    obtain ⟨k', hk'M, hk'i⟩ := exists_mul_mod_eq_of_lastRecords h (i := i') (by omega)
    refine ⟨k', ?_, hk'i⟩
    rw [mem_filter, mem_range]
    exact ⟨hk'M, by omega⟩

/-- The count g of the A003586 program: k + fs(k, M, a, 0) - fs(k, M, a, M - N). -/
def classCount (M a N k : ℕ) : ℕ := k + floorSum k M a 0 - floorSum k M a (M - N)

/-- g(k) is the number of k' < k with k' a mod M < N, for N ≤ M. -/
theorem classCount_eq {M a N : ℕ} (hM : 0 < M) (hNM : N ≤ M) (k : ℕ) :
    classCount M a N k = ((range k).filter (fun k' => k' * a % M < N)).card := by
  have hterm : ∀ k' ∈ range k, (a * k' + (M - N)) / M =
      (a * k' + 0) / M + if N ≤ k' * a % M then 1 else 0 := by
    intro k' _
    have hd := Nat.div_add_mod (a * k') M
    have hs : a * k' % M < M := Nat.mod_lt _ hM
    have he : a * k' + (M - N) = M * (a * k' / M) + (a * k' % M + (M - N)) := by omega
    rw [he, Nat.mul_add_div hM, Nat.add_zero, Nat.mul_comm k' a]
    congr 1
    by_cases hN : N ≤ a * k' % M
    · simp only [hN, ↓reduceIte]
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
    · simp only [hN, ↓reduceIte]
      apply Nat.div_eq_of_lt
      omega
  unfold classCount
  rw [floorSum_eq hM, floorSum_eq hM, sum_congr rfl hterm, sum_add_distrib, ← card_filter]
  have hpart := card_filter_add_card_filter_not (s := range k) (fun k' => k' * a % M < N)
  rw [card_range] at hpart
  have hnot : (range k).filter (fun k' => ¬k' * a % M < N) =
      (range k).filter (fun k' => N ≤ k' * a % M) := by
    apply filter_congr
    intro x _
    omega
  rw [hnot] at hpart
  omega

end AcceleratedCollatz
