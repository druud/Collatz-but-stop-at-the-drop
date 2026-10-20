-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TFirstWord
import AcceleratedCollatz.TRhoLower

/-!
  The largest rho over the admissible words of Order n. In an admissible word the odd
  step that follows m odd steps stands at a position k with k + 1 ≤ p2(m)
  (`admissible_step_le`). Each odd step at position k adds 2^k to rho before the
  later odd steps multiply it by 3, so rho s ≤ rhoMax (order s), with
  rhoMax 0 = 0 and rhoMax (o + 1) = 3 rhoMax o + 2^(p2(o) - 1) (`rho_le_rhoMax`).
  Equality holds exactly when every odd step stands at its latest position, and the one
  admissible word of Order n with that property is the first word of Order n
  (`rho_eq_rhoMax_iff`, `rho_firstWord`). In closed form rhoMax n is the sum of
  3^(n-1-m) 2^(p2(m)-1) over m < n (`rhoMax_eq_sum`), and the slack of
  `rho_le_of_admissible` is a sum of the lower deficits 2 3^m - 2^p2(m)
  (`rhoMax_slack`). The least rho, 3^n - 2^n, is in TRhoLower (`three_pow_le_rho_add`,
  `rho_add_eq_three_pow_iff`).
-/

namespace AcceleratedCollatz

/-- The largest rho of an admissible word of Order o. -/
def rhoMax : ℕ → ℕ
  | 0 => 0
  | o + 1 => 3 * rhoMax o + 2 ^ (p2_of o - 1)

theorem rhoMax_succ (o : ℕ) : rhoMax (o + 1) = 3 * rhoMax o + 2 ^ (p2_of o - 1) :=
  rfl

/-- The word of length L with an odd step at each position p2(m) - 1, m < o, and halvings
    elsewhere. -/
def latestWord (o L : ℕ) : List Bool :=
  (List.range L).map (fun k => decide (∃ m < o, k + 1 = p2_of m))

theorem latestWord_succ (o L : ℕ) :
    latestWord o (L + 1) = latestWord o L ++ [decide (∃ m < o, L + 1 = p2_of m)] := by
  simp [latestWord, List.range_succ]

theorem length_latestWord (o L : ℕ) : (latestWord o L).length = L := by
  simp [latestWord]

/-- `latestWord` depends only on the positions below L. -/
theorem latestWord_congr {o o' L : ℕ}
    (h : ∀ k < L, (∃ m < o, k + 1 = p2_of m) ↔ (∃ m < o', k + 1 = p2_of m)) :
    latestWord o L = latestWord o' L := by
  unfold latestWord
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [decide_eq_decide]
  exact h k hk

/-- An odd step at the end of a prefix of length L adds 2^L, and the Order bound
    L + 1 ≤ p2(o) makes 2^L ≤ 2^(p2(o) - 1). Under that bound at every odd step,
    rho s ≤ rhoMax (order s); at equality s is the latest word of its Order and length,
    and its length reaches p2(order s - 1), the latest place of its last odd step. -/
theorem rho_le_rhoMax_of_steps (s : List Bool)
    (H : ∀ k, s[k]? = some true → k + 1 ≤ p2_of (order (s.take k))) :
    rho s ≤ rhoMax (order s) ∧
      (rho s = rhoMax (order s) →
        s = latestWord (order s) s.length ∧
          (order s = 0 ∨ p2_of (order s - 1) ≤ s.length)) := by
  induction s using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp [rho, affineNum, rhoMax, order]
    · intro _
      refine ⟨?_, ?_⟩
      · simp [latestWord]
      · left
        simp [order]
  | append_singleton p b ih =>
    have Hp : ∀ k, p[k]? = some true → k + 1 ≤ p2_of (order (p.take k)) := by
      intro k hk
      have hlt : k < p.length := by
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at hk
        simp at hk
      have hk' : (p ++ [b])[k]? = some true := by
        rw [List.getElem?_append_left hlt]
        exact hk
      have h := H k hk'
      rwa [List.take_append_of_le_length hlt.le] at h
    obtain ⟨hle, heq⟩ := ih Hp
    cases b with
    | false =>
      rw [rho_append_false, order_append_single]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, List.length_append,
        List.length_singleton]
      refine ⟨hle, ?_⟩
      intro hr
      obtain ⟨hw, hJ⟩ := heq hr
      refine ⟨?_, ?_⟩
      · have hd : decide (∃ m < order p, p.length + 1 = p2_of m) = false := by
          apply decide_eq_false
          rintro ⟨m, hm, hpm⟩
          rcases hJ with h0 | hJ
          · omega
          · have hmono := p2_of_mono (Nat.le_sub_one_of_lt hm)
            omega
        rw [latestWord_succ, ← hw, hd]
      · rcases hJ with h0 | hJ
        · left
          exact h0
        · right
          omega
    | true =>
      have hlast : p.length + 1 ≤ p2_of (order p) := by
        have h := H p.length (by simp)
        rwa [List.take_append_of_le_length le_rfl, List.take_length] at h
      have hpow : 2 ^ p.length ≤ 2 ^ (p2_of (order p) - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [rho_append_true, order_append_single]
      simp only [↓reduceIte, rhoMax_succ, List.length_append, List.length_singleton,
        Nat.add_sub_cancel]
      refine ⟨by omega, ?_⟩
      intro hr
      have hrp : rho p = rhoMax (order p) := by
        omega
      have hpw : 2 ^ p.length = 2 ^ (p2_of (order p) - 1) := by
        omega
      have hL : p.length = p2_of (order p) - 1 :=
        Nat.pow_right_injective (le_refl 2) hpw
      obtain ⟨hw, _⟩ := heq hrp
      refine ⟨?_, ?_⟩
      · rw [latestWord_succ]
        have hcongr : latestWord (order p + 1) p.length = latestWord (order p) p.length := by
          apply latestWord_congr
          intro k hk
          constructor
          · rintro ⟨m, hm, hkm⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm'
            · exact ⟨m, hm', hkm⟩
            · rw [hm'] at hkm
              omega
          · rintro ⟨m, hm, hkm⟩
            exact ⟨m, by omega, hkm⟩
        have hd : decide (∃ m < order p + 1, p.length + 1 = p2_of m) = true :=
          decide_eq_true ⟨order p, by omega, by omega⟩
        rw [hcongr, ← hw, hd]
      · right
        omega

/-- In an admissible word, the odd step that follows m odd steps stands at a position k
    with k + 1 ≤ p2(m). -/
theorem admissible_step_le {s : List Bool} (hA : Admissible s) :
    ∀ k, s[k]? = some true → k + 1 ≤ p2_of (order (s.take k)) := by
  intro k hk
  have hlt : k < s.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hk
    simp at hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, List.take_zero]
    have h1 : p2_of (order []) = 1 := by
      simp [order, p2_of]
    omega
  · have h := hA.prefix_gt k hpos hlt
    rw [one_lt_seqProduct_iff, List.length_take, min_eq_left hlt.le] at h
    by_contra hcon
    have h2 : 2 ^ p2_of (order (s.take k)) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 := p2_of_spec (order (s.take k))
    omega

/-- rho s ≤ rhoMax n for an admissible word s of Order n. -/
theorem rho_le_rhoMax {s : List Bool} (hA : Admissible s) : rho s ≤ rhoMax (order s) :=
  (rho_le_rhoMax_of_steps s (admissible_step_le hA)).1

/-- An admissible word of Order n with rho = rhoMax n is the latest word of Order n. -/
theorem eq_latestWord_of_rho_eq {s : List Bool} (hA : Admissible s)
    (h : rho s = rhoMax (order s)) : s = latestWord (order s) (p2_of (order s)) := by
  have hw := ((rho_le_rhoMax_of_steps s (admissible_step_le hA)).2 h).1
  rwa [admissible_length (s := s) hA] at hw

/-- rho of the first word of Order n without its final halving is rhoMax n. -/
theorem rho_firstBody (n : ℕ) : rho (firstBody n) = rhoMax n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    have hlen := length_firstBody n
    have hsplit : firstBody (n + 1) = (firstBody n ++ [true]) ++
        List.replicate (p2_of (n + 1) - p2_of n - 1) false := by
      rw [firstBody_succ, List.append_assoc, List.singleton_append]
    rw [hsplit, rho_append_replicate_false, rho_append_true, ih, rhoMax_succ]
    congr 2
    omega

/-- rho of the first word of Order n is rhoMax n. -/
theorem rho_firstWord (n : ℕ) : rho (firstWord n) = rhoMax n := by
  rw [firstWord, rho_append_false, rho_firstBody]

/-- The admissible words of Order n with rho = rhoMax n: only the first word. -/
theorem rho_eq_rhoMax_iff {s : List Bool} (hA : Admissible s) :
    rho s = rhoMax (order s) ↔ s = firstWord (order s) := by
  constructor
  · intro h
    have hs := eq_latestWord_of_rho_eq hA h
    have hF := eq_latestWord_of_rho_eq (firstWord_admissible (order s))
      (by rw [order_firstWord, rho_firstWord])
    rw [order_firstWord] at hF
    exact hs.trans hF.symm
  · intro h
    rw [h, rho_firstWord, order_firstWord]

/-- Over the admissible words of Order n, rho is largest at the first word, and only
    there. -/
theorem rho_lt_rho_firstWord {n : ℕ} {s : List Bool} (hs : s ∈ admSet n)
    (hne : s ≠ firstWord n) : rho s < rho (firstWord n) := by
  obtain ⟨hA, hn⟩ := (mem_admSet n s).mp hs
  rw [rho_firstWord, ← hn]
  have hle := rho_le_rhoMax hA
  have hne' : rho s ≠ rhoMax (order s) := by
    rw [ne_eq, rho_eq_rhoMax_iff hA, hn]
    exact hne
  omega

/-- rhoMax n = sum over m < n of 3^(n-1-m) 2^(p2(m) - 1). -/
theorem rhoMax_eq_sum (n : ℕ) :
    rhoMax n = ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ (p2_of m - 1) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [rhoMax_succ, ih, Finset.sum_range_succ, Finset.mul_sum]
    have h0 : n + 1 - 1 - n = 0 := by
      omega
    have hlast : 3 ^ (n + 1 - 1 - n) * 2 ^ (p2_of n - 1) = 2 ^ (p2_of n - 1) := by
      rw [h0, pow_zero, one_mul]
    rw [hlast]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    have hm' : n + 1 - 1 - m = (n - 1 - m) + 1 := by
      omega
    rw [hm', pow_succ]
    ring

/-- 2^p2(m) ≤ 2 3^m: the lower deficit 2 3^m - 2^p2(m) is a natural number. -/
theorem two_pow_p2_of_le_nat (m : ℕ) : 2 ^ p2_of m ≤ 2 * 3 ^ m := by
  have h := p2_of_spec_lower m
  have hpos : 1 ≤ p2_of m := by
    unfold p2_of
    omega
  have he : 2 ^ p2_of m = 2 * 2 ^ (p2_of m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  omega

/-- The slack of `rho_le_of_admissible` at the first word, in additive form:
    2 rhoMax n + sum over m < n of 3^(n-1-m) (2 3^m - 2^p2(m)) = 2 n 3^(n-1). -/
theorem rhoMax_slack (n : ℕ) :
    2 * rhoMax n + ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * (2 * 3 ^ m - 2 ^ p2_of m) =
      2 * (n * 3 ^ (n - 1)) := by
  rw [rhoMax_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hterm : ∀ m ∈ Finset.range n,
      2 * (3 ^ (n - 1 - m) * 2 ^ (p2_of m - 1)) +
        3 ^ (n - 1 - m) * (2 * 3 ^ m - 2 ^ p2_of m) = 2 * 3 ^ (n - 1) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hpos : 1 ≤ p2_of m := by
      unfold p2_of
      omega
    have he : 2 * 2 ^ (p2_of m - 1) = 2 ^ p2_of m := by
      rw [← pow_succ', Nat.sub_add_cancel hpos]
    have hd := two_pow_p2_of_le_nat m
    have h3 : 3 ^ (n - 1 - m) * 3 ^ m = 3 ^ (n - 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 * (3 ^ (n - 1 - m) * 2 ^ (p2_of m - 1)) +
          3 ^ (n - 1 - m) * (2 * 3 ^ m - 2 ^ p2_of m)
        = 3 ^ (n - 1 - m) * (2 ^ p2_of m + (2 * 3 ^ m - 2 ^ p2_of m)) := by
          rw [← he]
          ring
      _ = 3 ^ (n - 1 - m) * (2 * 3 ^ m) := by
          rw [Nat.add_sub_cancel' hd]
      _ = 2 * 3 ^ (n - 1) := by
          rw [← h3]
          ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

set_option linter.hashCommand false in
#guard (List.range 8).map rhoMax = [0, 1, 5, 23, 85, 319, 1085, 3767]

end AcceleratedCollatz
