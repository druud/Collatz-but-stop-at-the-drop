-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCorrespondence
import AcceleratedCollatz.TCovering
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
  Terras (1976): almost every x drops under T. The numbers x < N that never drop
  (no k ≥ 1 with T^k(x) < x) are a vanishing share of N (`terras_density`).
  The proof counts residues, without probability. rho s ≤ 6^|s| (`rho_le`), so for
  x > 6^m a coefficient below 1 at step m is a drop (`tStep_iterate_lt`); a number
  x > 6^m that never drops has 2^m < 3^o, o the number of odd steps among its
  first m (`pow_lt_of_not_drops`), a condition on x mod 2^m. The lifts r and r + 2^m
  of a residue part at step m (`tStep_iterate_add_pow`), so the residues below 2^m
  weighted by u^o sum to (1 + u)^m (`sum_pow_order_tBits`); with u = √3 the residues
  with 2^m < 3^o number at most ((1 + √3)/√2)^m (`card_pow_lt_le`), a share c^m of
  2^m with c = (1 + √3)/(2√2) < 1 (`terrasC_lt_one`).
-/

namespace AcceleratedCollatz

open Filter Topology Finset

/-- affineNum grows at most by 3 per step, plus the scaled 1. -/
theorem affineNum_le : ∀ (t : List Bool) (j N : ℕ),
    affineNum t j N ≤ 3 ^ t.length * N + 3 ^ t.length * 2 ^ (j + t.length)
  | [], j, N => by simp [affineNum]
  | b :: t, j, N => by
    have ih := affineNum_le t (j + 1) (if b then 3 * N + 2 ^ j else N)
    have hb : (if b then 3 * N + 2 ^ j else N) ≤ 3 * N + 2 ^ j := by
      split
      · exact le_rfl
      · exact (by omega : N ≤ 3 * N).trans (Nat.le_add_right _ _)
    have hj : 2 ^ j ≤ 2 ^ (j + (t.length + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [affineNum, List.length_cons]
    have e1 : j + 1 + t.length = j + (t.length + 1) := by omega
    rw [e1] at ih
    have step := ih.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (3 ^ t.length) hb) _)
    refine step.trans ?_
    rw [pow_succ]
    generalize 3 ^ t.length = P at *
    generalize 2 ^ (j + (t.length + 1)) = Q at *
    generalize 2 ^ j = R at *
    have := Nat.mul_le_mul_left P hj
    nlinarith

/-- The remainder term is at most 6^|s|. -/
theorem rho_le (s : List Bool) : rho s ≤ 6 ^ s.length := by
  have h := affineNum_le s 0 0
  simp only [mul_zero, zero_add] at h
  calc rho s ≤ 3 ^ s.length * 2 ^ s.length := h
    _ = 6 ^ s.length := by rw [← mul_pow]; norm_num

/-- A coefficient below 1 at step m is a drop once x > 6^m. -/
theorem tStep_iterate_lt (x m : ℕ) (h : 3 ^ order (tBits x m) < 2 ^ m) (hx : 6 ^ m < x) :
    tStep^[m] x < x := by
  have hN := tStep_iterate_nForm m x
  have hr : rho (tBits x m) < x := by
    have := rho_le (tBits x m)
    rw [length_tBits] at this
    omega
  have h1 : 3 ^ order (tBits x m) * x + x ≤ 2 ^ m * x := by
    have := Nat.mul_le_mul_right x (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this
    exact this
  have h2 : 2 ^ m * tStep^[m] x < 2 ^ m * x := by omega
  exact Nat.lt_of_mul_lt_mul_left h2

/-- A number above 6^m that never drops has 2^m < 3^o after m steps. -/
theorem pow_lt_of_not_drops (x m : ℕ) (hm : 1 ≤ m) (hx : 6 ^ m < x)
    (hD : ¬ ∃ k, 1 ≤ k ∧ tStep^[k] x < x) : 2 ^ m < 3 ^ order (tBits x m) := by
  have hne := two_pow_ne_three_pow m (order (tBits x m)) hm
  by_contra hlt
  exact hD ⟨m, hm, tStep_iterate_lt x m (by omega) hx⟩

/-- The lift x + 2^m runs m steps like x, ending 3^o higher. -/
theorem tStep_iterate_add_pow (x m : ℕ) :
    tStep^[m] (2 ^ m + x) = tStep^[m] x + 3 ^ order (tBits x m) := by
  have hc : tBits (2 ^ m + x) m = tBits x m :=
    tBits_congr _ _ _ (Nat.add_modEq_left)
  have h1 := tStep_iterate_nForm m (2 ^ m + x)
  have h2 := tStep_iterate_nForm m x
  rw [hc] at h1
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ m)
  rw [h1, Nat.mul_add (2 ^ m) (tStep^[m] x), h2]
  ring

theorem order_append_single (l : List Bool) (b : Bool) :
    order (l ++ [b]) = order l + if b then 1 else 0 := by
  cases b <;> simp [order, List.filter_append]

theorem order_tBits_succ (x m : ℕ) :
    order (tBits x (m + 1)) =
      order (tBits x m) + if tStep^[m] x % 2 = 1 then 1 else 0 := by
  rw [tBits_add x m 1]
  simp only [tBits]
  rw [order_append_single]
  simp

/-- The residues below 2^m, weighted by u^(number of odd steps), sum to (1 + u)^m. -/
theorem sum_pow_order_tBits (u : ℝ) : ∀ m : ℕ,
    ∑ x ∈ range (2 ^ m), u ^ order (tBits x m) = (1 + u) ^ m
  | 0 => by simp [tBits, order]
  | m + 1 => by
    rw [pow_succ 2 m, mul_two, Finset.sum_range_add, pow_succ (1 + u) m,
      ← sum_pow_order_tBits u m, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hc : tBits (2 ^ m + x) m = tBits x m := tBits_congr _ _ _ (Nat.add_modEq_left)
    rw [order_tBits_succ, order_tBits_succ, hc, tStep_iterate_add_pow]
    have hodd : 3 ^ order (tBits x m) % 2 = 1 := Nat.odd_iff.mp ((by decide : Odd 3).pow)
    rcases Nat.mod_two_eq_zero_or_one (tStep^[m] x) with h | h
    · have h' : (tStep^[m] x + 3 ^ order (tBits x m)) % 2 = 1 := by omega
      simp [h, h', pow_succ]
      ring
    · have h' : (tStep^[m] x + 3 ^ order (tBits x m)) % 2 = 0 := by omega
      simp [h, h', pow_succ]
      ring

/-- At most ((1 + √3)/√2)^m residues below 2^m have 2^m < 3^o after m steps. -/
theorem card_pow_lt_le (m : ℕ) :
    (((range (2 ^ m)).filter (fun x => 2 ^ m < 3 ^ order (tBits x m))).card : ℝ) ≤
      ((1 + √3) / √2) ^ m := by
  have h2 : 0 < √2 := by positivity
  have key : ∀ x ∈ (range (2 ^ m)).filter (fun x => 2 ^ m < 3 ^ order (tBits x m)),
      (1 : ℝ) ≤ √3 ^ order (tBits x m) / √2 ^ m := by
    intro x hx
    have hlt : (2 : ℝ) ^ m < 3 ^ order (tBits x m) := by
      exact_mod_cast (Finset.mem_filter.mp hx).2
    have hs : √2 ^ m < √3 ^ order (tBits x m) := by
      refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
      rw [← pow_mul, ← pow_mul, mul_comm m, mul_comm (order _), pow_mul, pow_mul,
        Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
      exact hlt
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc (((range (2 ^ m)).filter (fun x => 2 ^ m < 3 ^ order (tBits x m))).card : ℝ)
      = ∑ x ∈ (range (2 ^ m)).filter (fun x => 2 ^ m < 3 ^ order (tBits x m)), (1 : ℝ) := by
        simp
    _ ≤ ∑ x ∈ (range (2 ^ m)).filter (fun x => 2 ^ m < 3 ^ order (tBits x m)),
          √3 ^ order (tBits x m) / √2 ^ m := Finset.sum_le_sum key
    _ ≤ ∑ x ∈ range (2 ^ m), √3 ^ order (tBits x m) / √2 ^ m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
    _ = ((1 + √3) / √2) ^ m := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, sum_pow_order_tBits, mul_pow, inv_pow]

/-- c = (1 + √3)/(2√2) < 1. -/
theorem terrasC_lt_one : (1 + √3) / (2 * √2) < 1 := by
  have h3 : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h2 : 0 < √2 := by positivity
  rw [div_lt_one (by positivity)]
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  nlinarith [Real.sqrt_nonneg 3]

/-- A set of x < N that depends on x mod 2^m has at most N / 2^m + 1 members per residue. -/
theorem card_filter_mod_le (N m : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((range N).filter (fun x => P (x % 2 ^ m))).card ≤
      (N / 2 ^ m + 1) * ((range (2 ^ m)).filter P).card := by
  rw [← Finset.card_range (N / 2 ^ m + 1), ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun x => (x / 2 ^ m, x % 2 ^ m)) ?_ ?_
  · intro x hx
    have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
      Finset.mem_filter]
    refine ⟨?_, Nat.mod_lt _ (by positivity), hx'.2⟩
    have := Nat.div_le_div_right (c := 2 ^ m) (Finset.mem_range.mp hx'.1).le
    omega
  · intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    rw [← Nat.div_add_mod x (2 ^ m), ← Nat.div_add_mod y (2 ^ m), h.1, h.2]

open Classical in
/-- The numbers below N that never drop, for m ≥ 1. -/
theorem card_not_drops_le (N m : ℕ) (hm : 1 ≤ m) :
    (((range N).filter (fun x => ¬ ∃ k, 1 ≤ k ∧ tStep^[k] x < x)).card : ℝ) ≤
      (6 ^ m + 1) + ((N : ℝ) / 2 ^ m + 1) * ((1 + √3) / √2) ^ m := by
  let P : ℕ → Prop := fun r => 2 ^ m < 3 ^ order (tBits r m)
  have hsub : (range N).filter (fun x => ¬ ∃ k, 1 ≤ k ∧ tStep^[k] x < x) ⊆
      range (6 ^ m + 1) ∪ (range N).filter (fun x => P (x % 2 ^ m)) := by
    intro x hx
    obtain ⟨hxN, hD⟩ := Finset.mem_filter.mp hx
    rcases le_or_gt x (6 ^ m) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxN, ?_⟩)
      change 2 ^ m < 3 ^ order (tBits (x % 2 ^ m) m)
      rw [tBits_mod]
      exact pow_lt_of_not_drops x m hm h hD
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hp := card_filter_mod_le N m P
  have hG := card_pow_lt_le m
  have hdiv : ((N / 2 ^ m : ℕ) : ℝ) ≤ (N : ℝ) / 2 ^ m := by
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast Nat.div_mul_le_self N (2 ^ m)
  calc (((range N).filter (fun x => ¬ ∃ k, 1 ≤ k ∧ tStep^[k] x < x)).card : ℝ)
      ≤ (6 ^ m + 1 : ℕ) + ((N / 2 ^ m + 1 : ℕ) : ℝ) * ((range (2 ^ m)).filter P).card := by
        rw [Finset.card_range] at hc
        exact_mod_cast hc.trans (Nat.add_le_add_left hp _)
    _ ≤ (6 ^ m + 1) + ((N : ℝ) / 2 ^ m + 1) * ((1 + √3) / √2) ^ m := by
        push_cast
        gcongr

open Classical in
/-- Terras: the share of the x < N that never drop under T tends to 0. -/
theorem terras_density :
    Tendsto (fun N : ℕ =>
      (((range N).filter (fun x => ¬ ∃ k, 1 ≤ k ∧ tStep^[k] x < x)).card : ℝ) / N)
      atTop (𝓝 0) := by
  set c : ℝ := (1 + √3) / (2 * √2)
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := terrasC_lt_one
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m0, hm0⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).eventually
    (gt_mem_nhds (half_pos hε))).exists_forall_of_atTop
  set m := m0 + 1
  have hm : 1 ≤ m := by omega
  have hcm := hm0 m (by omega)
  set A : ℝ := 6 ^ m + 1 + ((1 + √3) / √2) ^ m
  have hA : 0 < A := by positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * A / ε)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNbig : 2 * A / ε < N := by
    have : (N0 : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  have hkey : ((1 + √3) / √2) ^ m / 2 ^ m = c ^ m := by
    rw [← div_pow, div_div, mul_comm √2 2]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  rw [div_lt_iff₀ hNpos]
  have hb := card_not_drops_le N m hm
  have hA' : A < ε / 2 * N := by
    rw [div_lt_iff₀ hε] at hNbig
    linarith
  have hcN : (N : ℝ) / 2 ^ m * ((1 + √3) / √2) ^ m = c ^ m * N := by
    rw [← hkey]
    ring
  nlinarith [hcN, hb, hA', hcm]

end AcceleratedCollatz
