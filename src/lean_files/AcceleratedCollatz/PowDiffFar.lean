-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.PowDiffWalk

/-!
# Both walk bounds for any certified range

`rhinBoundUpTo_one_two` (TRhinCheck) and `lowAt_upTo` (PowDiffWalk) hold up to Order 10^60,
from one kernel walk each at K = 2^400. Their proofs use the walk only through its result,
so here they are stated for any bracket K = 2^m from B bits, any bound N and any fuel f:
a walk that returns true gives the upper side 3^n ≤ p2(n)^2 (2^p2(n) - 3^n)
(`rhinBoundUpTo_of_walk`) and the lower side 2^(Q-1) (1 + Q^2) ≤ Q^2 3^n
(`lowAt_of_walk`) for every Order 1 ≤ n ≤ N, and both together
min(2^i, 3^j) ≤ p2(j)^2 |2^i - 3^j| for 1 ≤ j ≤ N (`min_le_of_walks`). The kernel runs of
larger walks are in `PowDiffFarCheck`.
-/

namespace PowDiff

open AcceleratedCollatz

/-- A successful upper walk at K = 2^m (bracket from B bits) up to N gives `RhinBound 1 2`
    for every Order 1 ≤ n ≤ N. -/
theorem rhinBoundUpTo_of_walk {B m N f : ℕ}
    (hw : rhinWalk (2 ^ m) (log2Lo 3 B m) (log2Hi 3 B m) N f (sbWalk 0) = true) :
    RhinBoundUpTo 1 2 N := by
  apply rhinBoundUpTo_of_records
  intro a ha1 haN hR
  have hbr := log2Bracket_pow3 B m
  have hK : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨k, -, hNk, hall⟩ := rhinWalk_spec hbr hK f 0 hw
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · exfalso
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have : k = 0 := by omega
        subst this
        have : (sbWalk 0).loDen + (sbWalk 0).hiDen = 1 := by
          decide +kernel
        omega
      · have : k = 1 := by omega
        subst this
        have : (sbWalk 1).loDen + (sbWalk 1).hiDen = 1 := by
          decide +kernel
        omega
    · exact hge
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
  have hp21 : p2Q 3 1 = 2 := p2_of_one
  have hlt : a < (sbWalkQ 3 (p2Q 3 1 + j)).loDen + (sbWalkQ 3 (p2Q 3 1 + j)).hiDen := by
    rw [hp21]
    change a < (sbWalk (2 + j)).loDen + (sbWalk (2 + j)).hiDen
    omega
  obtain ⟨i, hij, hi⟩ := exists_sbWalkQ_hiDen (by decide) le_rfl j a ha1 hlt hR
  rw [hp21] at hi
  change (sbWalk (2 + i)).hiDen = a at hi
  have hok := hall (2 + i) (by omega) (by omega)
  have hnum := sbWalk_hiNum (k := 2 + i) (by omega)
  rw [hnum, hi] at hok
  exact rhinOK_spec hbr.2 hK hok

/-- A successful lower walk at K = 2^m (bracket from B bits) up to N gives the lower side
    for every Order 1 ≤ n ≤ N. -/
theorem lowAt_of_walk {B m N f : ℕ}
    (hw : lowWalk (2 ^ m) (log2Lo 3 B m) (log2Hi 3 B m) N f (sbWalk 0) = true) :
    ∀ n, 1 ≤ n → n ≤ N → LowAt n := by
  apply lowAt_of_records
  intro c hc1 hcN hR
  have hbr := log2Bracket_pow3 B m
  have hK : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨k, -, hNk, hall⟩ := lowWalk_spec hbr hK f 0 hw
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · exfalso
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have : k = 0 := by omega
        subst this
        have : (sbWalk 0).loDen + (sbWalk 0).hiDen = 1 := by
          decide +kernel
        omega
      · have : k = 1 := by omega
        subst this
        have : (sbWalk 1).loDen + (sbWalk 1).hiDen = 1 := by
          decide +kernel
        omega
    · exact hge
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
  have hp21 : p2Q 3 1 = 2 := p2_of_one
  have hlt : c < (sbWalkQ 3 (p2Q 3 1 + j)).loDen + (sbWalkQ 3 (p2Q 3 1 + j)).hiDen := by
    rw [hp21]
    change c < (sbWalk (2 + j)).loDen + (sbWalk (2 + j)).hiDen
    omega
  obtain ⟨i, hij, hi⟩ := exists_sbWalkQ_loDen (by decide) le_rfl j c hc1 hlt hR
  rw [hp21] at hi
  change (sbWalk (2 + i)).loDen = c at hi
  have hok := hall (2 + i) (by omega) (by omega)
  have hnum := sbWalk_loNum (k := 2 + i) (by omega)
  rw [hi] at hnum
  have hs := lowOK_spec hbr.1 hK hok
  rw [hi] at hs
  unfold LowAt
  rw [← hnum, Nat.add_sub_cancel]
  exact hs

/-- Both sides up to N: min(2^i, 3^j) ≤ p2(j)^2 |2^i - 3^j| for 1 ≤ j ≤ N. -/
theorem min_le_of_walks {N i j : ℕ} (hU : RhinBoundUpTo 1 2 N)
    (hL : ∀ n, 1 ≤ n → n ≤ N → LowAt n) (hj1 : 1 ≤ j) (hj : j ≤ N) :
    min (2 ^ i) (3 ^ j) ≤ p2_of j ^ 2 * D (2 ^ i) (3 ^ j) := by
  set Q := p2_of j with hQ
  have hlo : 2 ^ (Q - 1) ≤ 3 ^ j := p2_of_spec_lower j
  have hhi : 3 ^ j < 2 ^ Q := p2_of_spec j
  have hne : 2 ^ i ≠ 3 ^ j := two_pow_ne_three_pow_right hj1
  unfold D
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hi : i ≤ Q - 1 := by
      by_contra hc
      have : 2 ^ Q ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h2 : 2 ^ i ≤ 2 ^ (Q - 1) := Nat.pow_le_pow_right (by decide) hi
    have hL' := hL j hj1 hj
    unfold LowAt at hL'
    rw [← hQ] at hL'
    rw [min_eq_left h.le, Nat.sub_eq_zero_of_le h.le, Nat.zero_add, sq]
    have hm : Q * Q * (3 ^ j - 2 ^ (Q - 1)) ≤ Q * Q * (3 ^ j - 2 ^ i) :=
      Nat.mul_le_mul_left _ (by omega)
    have hm2 : 2 ^ (Q - 1) ≤ Q * Q * (3 ^ j - 2 ^ (Q - 1)) := by
      rw [Nat.mul_sub]
      have : 2 ^ (Q - 1) * (1 + Q * Q) = 2 ^ (Q - 1) + Q * Q * 2 ^ (Q - 1) := by ring
      omega
    omega
  · have hi : Q ≤ i := by
      by_contra hc
      have : 2 ^ i ≤ 2 ^ (Q - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h2 : 2 ^ Q ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
    have hU' := hU j hj1 hj
    rw [← hQ, Nat.one_mul] at hU'
    rw [min_eq_right h.le, Nat.sub_eq_zero_of_le h.le, Nat.add_zero]
    calc 3 ^ j ≤ Q ^ 2 * (2 ^ Q - 3 ^ j) := hU'
      _ ≤ Q ^ 2 * (2 ^ i - 3 ^ j) := Nat.mul_le_mul_left _ (by omega)

-- The 10^60 results again, from the generic forms (no new kernel run).
example : RhinBoundUpTo 1 2 (10 ^ 60) := rhinBoundUpTo_of_walk rhinWalk_ok
example : ∀ n, 1 ≤ n → n ≤ 10 ^ 60 → LowAt n := lowAt_of_walk lowWalk_ok

end PowDiff
