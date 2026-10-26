-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.PowDiff
import AcceleratedCollatz.TRhinCheck
import AcceleratedCollatz.TRulerPair

/-!
# The numbers |2^i - 3^j| with j ≤ 10^60, unconditionally

Companion of `PowDiff` and `PowDiffRhin`. `TRhinCheck` gives the upper side up to Order
10^60: 3^n ≤ Q^2 (2^Q - 3^n) with Q = p2(n). Here the lower side, by the same certified
walk on the fractions below log2 3: 2^(Q-1) (1 + Q^2) ≤ Q^2 3^n for 1 ≤ n ≤ 10^60
(`lowAt_upTo`). Between lower record Orders the ratio 3^n/2^(Q-1) does not fall below its
value at the last record (`blockFactor_ge_of_lowerRecord`) and Q does not fall, so the
records suffice (`lowAt_of_records`). At a record fraction p/n (p = Q - 1) the bound is
checked exactly for n ≤ 100 and otherwise from a bracket 2^a ≤ 3^K by
p K + K/(Q^2/2) + 1 ≤ a n (`lowOK_spec`). The kernel runs the walk at K = 2^400
(`lowWalk_ok`).

Both sides together: min(2^i, 3^j) ≤ p2(j)^2 |2^i - 3^j| for 1 ≤ j ≤ 10^60
(`min_le_of_walk`), so v = |2^i - 3^j| with j ≤ 10^60 has i, j < B for any B ≥ 3 with
(4 B^2 + 1) v < 2^B (`lt_of_walk`). Without `RhinInt`, only j > 10^60 is left open.
-/

namespace PowDiff

open AcceleratedCollatz

/-! ### The check at a fraction below -/

/-- The bound at the fraction p/n below log2 3, Q = p + 1: exact for n ≤ 100, else by the
    bracket end a. -/
def lowOK (K a p n : ℕ) : Bool :=
  if n ≤ 100 then decide (2 ^ p * (1 + (p + 1) * (p + 1)) ≤ (p + 1) * (p + 1) * 3 ^ n)
  else decide (1 ≤ p) && decide (p * K + K / ((p + 1) * (p + 1) / 2) + 1 ≤ a * n)

/-- The check gives 2^p (1 + Q^2) ≤ Q^2 3^n with Q = p + 1. -/
theorem lowOK_spec {K a p n : ℕ} (ha : 2 ^ a ≤ 3 ^ K) (hK : 1 ≤ K)
    (h : lowOK K a p n = true) :
    2 ^ p * (1 + (p + 1) * (p + 1)) ≤ (p + 1) * (p + 1) * 3 ^ n := by
  unfold lowOK at h
  by_cases hn : n ≤ 100
  · rw [ite_eq_left hn] at h
    exact of_decide_eq_true h
  · rw [ite_eq_right hn, Bool.and_eq_true] at h
    have hp := of_decide_eq_true h.1
    have hc := of_decide_eq_true h.2
    have hM : 2 ≤ (p + 1) * (p + 1) := by nlinarith
    set Q := p + 1
    by_contra hlt
    push Not at hlt
    have h1 : (Q * Q * 3 ^ n) ^ K < (2 ^ p * (1 + Q * Q)) ^ K :=
      Nat.pow_lt_pow_left hlt (by omega)
    have h2 : 2 ^ (a * n) ≤ (3 ^ n) ^ K := by
      calc 2 ^ (a * n) = (2 ^ a) ^ n := pow_mul 2 a n
        _ ≤ (3 ^ K) ^ n := Nat.pow_le_pow_left ha n
        _ = (3 ^ n) ^ K := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have h3 : (1 + Q * Q) ^ K ≤ 2 ^ (K / (Q * Q / 2) + 1) * (Q * Q) ^ K := by
      rw [Nat.add_comm]
      exact succ_pow_le hM K
    have h4 : (2 ^ p * (1 + Q * Q)) ^ K ≤ (Q * Q * 3 ^ n) ^ K := by
      calc (2 ^ p * (1 + Q * Q)) ^ K = 2 ^ (p * K) * (1 + Q * Q) ^ K := by
            rw [Nat.mul_pow, ← pow_mul]
        _ ≤ 2 ^ (p * K) * (2 ^ (K / (Q * Q / 2) + 1) * (Q * Q) ^ K) :=
            Nat.mul_le_mul_left _ h3
        _ = 2 ^ (p * K + (K / (Q * Q / 2) + 1)) * (Q * Q) ^ K := by
            rw [pow_add]
            ring
        _ ≤ 2 ^ (a * n) * (Q * Q) ^ K :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
        _ ≤ (3 ^ n) ^ K * (Q * Q) ^ K := Nat.mul_le_mul_right _ h2
        _ = (Q * Q * 3 ^ n) ^ K := by
            rw [Nat.mul_pow (Q * Q)]
            ring
    exact absurd (h1.trans_le h4) (lt_irrefl _)

/-! ### The checked walk -/

/-- The certified walk that checks the lower fraction of every node until the sum of the
    denominators passes N. -/
def lowWalk (K a b N : ℕ) : ℕ → SBNode → Bool
  | 0, _ => false
  | f + 1, s =>
    lowOK K a s.loNum s.loDen &&
      (decide (N < s.loDen + s.hiDen) ||
        match sbCertStep K a b s with
        | some t => lowWalk K a b N f t
        | none => false)

/-- A successful checked walk from node j reaches a node k ≥ j whose denominators sum past
    N, and every node from j to k passes the check. -/
theorem lowWalk_spec {K a b N : ℕ} (h : Log2Bracket K a b) (hK : 1 ≤ K) :
    ∀ f j, lowWalk K a b N f (sbWalk j) = true →
      ∃ k, j ≤ k ∧ N < (sbWalk k).loDen + (sbWalk k).hiDen ∧
        ∀ i, j ≤ i → i ≤ k → lowOK K a (sbWalk i).loNum (sbWalk i).loDen = true := by
  intro f
  induction f with
  | zero =>
    intro j hw
    exact absurd hw (by simp [lowWalk])
  | succ f ih =>
    intro j hw
    rw [lowWalk, Bool.and_eq_true, Bool.or_eq_true] at hw
    obtain ⟨hok, hrest⟩ := hw
    rcases hrest with hN | hstep
    · refine ⟨j, le_rfl, of_decide_eq_true hN, fun i hi1 hi2 => ?_⟩
      have : i = j := by omega
      rw [this]
      exact hok
    · cases ht : sbCertStep K a b (sbWalk j) with
      | none =>
        rw [ht] at hstep
        exact absurd hstep (by simp)
      | some t =>
        rw [ht] at hstep
        have hs : 1 ≤ (sbWalk j).loDen := one_le_sbWalkQ_loDen 3 j
        have htw : t = sbWalk (j + 1) := by
          rw [sbCertStep_eq h hK hs ht]
          exact (sbWalkQ_succ 3 j).symm
        rw [htw] at hstep
        obtain ⟨k, hjk, hNk, hall⟩ := ih (j + 1) hstep
        refine ⟨k, by omega, hNk, fun i hi1 hi2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hi1 with heq | hlt
        · rw [← heq]
          exact hok
        · exact hall i (by omega) hi2

set_option exponentiation.threshold 500 in
/-- The checked walk at K = 2^400 (bracket from 803 bits) up to 10^60, fuel 1000,
    computed by the kernel. -/
theorem lowWalk_ok :
    lowWalk (2 ^ 400) (log2Lo 3 803 400) (log2Hi 3 803 400) (10 ^ 60) 1000 (sbWalk 0) = true := by
  decide +kernel

/-! ### From the lower records to every Order -/

/-- The lower bound in product form: 2^(Q-1) (1 + Q^2) ≤ Q^2 3^n with Q = p2(n). -/
def LowAt (n : ℕ) : Prop :=
  2 ^ (p2_of n - 1) * (1 + p2_of n * p2_of n) ≤ p2_of n * p2_of n * 3 ^ n

/-- The product form at the last lower record Order c ≤ n gives it at n. -/
theorem lowAt_of_record {c n : ℕ} (hc1 : 1 ≤ c) (hR : LowerRecord c)
    (hno : ∀ x, c < x → x ≤ n → ¬LowerRecord x) (hcn : c ≤ n) (hA : LowAt c) :
    LowAt n := by
  have hbf := blockFactor_ge_of_lowerRecord hR hno (K := n) (by omega) le_rfl
  rw [blockFactor_le_iff] at hbf
  have hcross : 3 ^ c * 2 ^ p2_of n ≤ 3 ^ n * 2 ^ p2_of c := by exact_mod_cast hbf
  have hPQ : p2_of c ≤ p2_of n := p2_of_mono hcn
  unfold LowAt at hA ⊢
  set P := p2_of c
  set Q := p2_of n
  have hP1 : 1 ≤ P := by
    change 1 ≤ p2_of c
    unfold p2_of
    omega
  have hQ1 : 1 ≤ Q := le_trans hP1 hPQ
  have hcross' : 3 ^ c * 2 ^ (Q - 1) ≤ 3 ^ n * 2 ^ (P - 1) := by
    have eP : 2 ^ P = 2 * 2 ^ (P - 1) := by
      rw [← pow_succ']
      congr 1
    have eQ : 2 ^ Q = 2 * 2 ^ (Q - 1) := by
      rw [← pow_succ']
      congr 1
    rw [eP, eQ] at hcross
    have h2 : 2 * (3 ^ c * 2 ^ (Q - 1)) ≤ 2 * (3 ^ n * 2 ^ (P - 1)) := by
      calc 2 * (3 ^ c * 2 ^ (Q - 1)) = 3 ^ c * (2 * 2 ^ (Q - 1)) := by ring
        _ ≤ 3 ^ n * (2 * 2 ^ (P - 1)) := hcross
        _ = 2 * (3 ^ n * 2 ^ (P - 1)) := by ring
    omega
  have hPP : 0 < P * P * 3 ^ c := Nat.mul_pos (Nat.mul_pos hP1 hP1) (Nat.pow_pos (by decide))
  have hq : (1 + Q * Q) * (P * P) ≤ (1 + P * P) * (Q * Q) := by nlinarith
  apply Nat.le_of_mul_le_mul_right _ hPP
  calc 2 ^ (Q - 1) * (1 + Q * Q) * (P * P * 3 ^ c)
      = 2 ^ (Q - 1) * 3 ^ c * ((1 + Q * Q) * (P * P)) := by ring
    _ ≤ 2 ^ (Q - 1) * 3 ^ c * ((1 + P * P) * (Q * Q)) := Nat.mul_le_mul_left _ hq
    _ = 3 ^ c * 2 ^ (Q - 1) * ((1 + P * P) * (Q * Q)) := by ring
    _ ≤ 3 ^ n * 2 ^ (P - 1) * ((1 + P * P) * (Q * Q)) := Nat.mul_le_mul_right _ hcross'
    _ = Q * Q * 3 ^ n * (2 ^ (P - 1) * (1 + P * P)) := by ring
    _ ≤ Q * Q * 3 ^ n * (P * P * 3 ^ c) := Nat.mul_le_mul_left _ hA

/-- The product form at every lower record Order up to N gives it at every Order up to N. -/
theorem lowAt_of_records {N : ℕ}
    (h : ∀ c, 1 ≤ c → c ≤ N → LowerRecord c → LowAt c) :
    ∀ n, 1 ≤ n → n ≤ N → LowAt n := by
  intro n hn1 hnN
  have hex : ∃ c, c ≤ n ∧ 1 ≤ c ∧ LowerRecord c := ⟨1, hn1, le_rfl, fun x hx1 hx => by omega⟩
  classical
  let c := Nat.findGreatest (fun c => 1 ≤ c ∧ LowerRecord c) n
  obtain ⟨c0, hc0n, hc0⟩ := hex
  have hspec : 1 ≤ c ∧ LowerRecord c :=
    Nat.findGreatest_spec (P := fun c => 1 ≤ c ∧ LowerRecord c) hc0n hc0
  have hcn : c ≤ n := Nat.findGreatest_le n
  have hno : ∀ x, c < x → x ≤ n → ¬LowerRecord x := by
    intro x hcx hxn hx
    exact Nat.findGreatest_is_greatest hcx hxn ⟨by omega, hx⟩
  exact lowAt_of_record hspec.1 hspec.2 hno hcn (h c hspec.1 (by omega) hspec.2)

set_option exponentiation.threshold 500 in
/-- 2^(Q-1) (1 + Q^2) ≤ Q^2 3^n with Q = p2(n), for every Order 1 ≤ n ≤ 10^60. -/
theorem lowAt_upTo : ∀ n, 1 ≤ n → n ≤ 10 ^ 60 → LowAt n := by
  apply lowAt_of_records
  intro c hc1 hcN hR
  have hbr := log2Bracket_pow3 803 400
  have hK : 1 ≤ 2 ^ 400 := Nat.one_le_two_pow
  obtain ⟨k, -, hNk, hall⟩ := lowWalk_spec hbr hK 1000 0 lowWalk_ok
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
  have hs := lowOK_spec (log2Bracket_pow3 803 400).1 hK hok
  rw [hi] at hs
  unfold LowAt
  rw [← hnum, Nat.add_sub_cancel]
  exact hs

/-! ### Both sides -/

/-- min(2^i, 3^j) ≤ p2(j)^2 |2^i - 3^j| for 1 ≤ j ≤ 10^60. -/
theorem min_le_of_walk {i j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 10 ^ 60) :
    min (2 ^ i) (3 ^ j) ≤ p2_of j ^ 2 * D (2 ^ i) (3 ^ j) := by
  set Q := p2_of j with hQ
  have hlo : 2 ^ (Q - 1) ≤ 3 ^ j := p2_of_spec_lower j
  have hhi : 3 ^ j < 2 ^ Q := p2_of_spec j
  have hne : 2 ^ i ≠ 3 ^ j := two_pow_ne_three_pow_right hj1
  unfold D
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · -- 2^i < 3^j: i ≤ Q - 1
    have hi : i ≤ Q - 1 := by
      by_contra hc
      have : 2 ^ Q ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h2 : 2 ^ i ≤ 2 ^ (Q - 1) := Nat.pow_le_pow_right (by decide) hi
    have hL := lowAt_upTo j hj1 hj
    unfold LowAt at hL
    rw [← hQ] at hL
    rw [min_eq_left h.le, Nat.sub_eq_zero_of_le h.le, Nat.zero_add, sq]
    have hm : Q * Q * (3 ^ j - 2 ^ (Q - 1)) ≤ Q * Q * (3 ^ j - 2 ^ i) :=
      Nat.mul_le_mul_left _ (by omega)
    have hm2 : 2 ^ (Q - 1) ≤ Q * Q * (3 ^ j - 2 ^ (Q - 1)) := by
      rw [Nat.mul_sub]
      have : 2 ^ (Q - 1) * (1 + Q * Q) = 2 ^ (Q - 1) + Q * Q * 2 ^ (Q - 1) := by ring
      omega
    omega
  · -- 3^j < 2^i: Q ≤ i
    have hi : Q ≤ i := by
      by_contra hc
      have : 2 ^ i ≤ 2 ^ (Q - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h2 : 2 ^ Q ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
    have hU := rhinBoundUpTo_one_two j hj1 hj
    rw [← hQ, Nat.one_mul] at hU
    rw [min_eq_right h.le, Nat.sub_eq_zero_of_le h.le, Nat.add_zero]
    calc 3 ^ j ≤ Q ^ 2 * (2 ^ Q - 3 ^ j) := hU
      _ ≤ Q ^ 2 * (2 ^ i - 3 ^ j) := Nat.mul_le_mul_left _ (by omega)

/-- (4 B^2 + 1) v < 2^B with B ≥ 3 gives (4 H^2 + 1) v < 2^H for every H ≥ B. -/
theorem lt_two_pow_of_le_sq {B v : ℕ} (hB : 3 ≤ B) (hv : (4 * B ^ 2 + 1) * v < 2 ^ B) :
    ∀ H, B ≤ H → (4 * H ^ 2 + 1) * v < 2 ^ H := by
  intro H hH
  induction H, hH using Nat.le_induction with
  | base => exact hv
  | succ H hBH ih =>
    have hs : 4 * (H + 1) ^ 2 + 1 ≤ 2 * (4 * H ^ 2 + 1) := by nlinarith
    calc (4 * (H + 1) ^ 2 + 1) * v ≤ 2 * ((4 * H ^ 2 + 1) * v) := by nlinarith
      _ < 2 * 2 ^ H := by omega
      _ = 2 ^ (H + 1) := by ring

/-- v = |2^i - 3^j| with j ≤ 10^60 has i, j < B for every B ≥ 3 with (4 B^2 + 1) v < 2^B. -/
theorem lt_of_walk {v B i j : ℕ} (hB : 3 ≤ B) (hv : (4 * B ^ 2 + 1) * v < 2 ^ B)
    (hj : j ≤ 10 ^ 60) (he : D (2 ^ i) (3 ^ j) = v) : i < B ∧ j < B := by
  rcases Nat.eq_zero_or_pos j with h0 | hj1
  · subst h0
    have h1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    unfold D at he
    rw [pow_zero] at he
    have hi : 2 ^ i < 2 ^ B := by
      rcases Nat.eq_zero_or_pos v with hv0 | hvp
      · have : 2 ^ i = 1 := by omega
        have h2 : 1 < 2 ^ B := Nat.one_lt_two_pow (by omega)
        omega
      · have e : 2 ^ i = v + 1 := by omega
        have hB2 : 1 ≤ 4 * B ^ 2 := by nlinarith
        calc 2 ^ i = v + 1 := e
          _ ≤ (4 * B ^ 2 + 1) * v := by nlinarith
          _ < 2 ^ B := hv
    exact ⟨(Nat.pow_lt_pow_iff_right (by decide)).mp hi, by omega⟩
  · by_contra hc
    have hH : B ≤ max i j := by omega
    set H := max i j
    have hm := min_le_of_walk (i := i) hj1 hj
    have hQ : p2_of j ≤ 2 * H := le_trans (p2_of_le_two_mul hj1) (by omega)
    have hQ2 : p2_of j ^ 2 ≤ 4 * H ^ 2 := by
      calc p2_of j ^ 2 ≤ (2 * H) ^ 2 := Nat.pow_le_pow_left hQ 2
        _ = 4 * H ^ 2 := by ring
    have h2 : 2 ^ H ≤ max (2 ^ i) (3 ^ j) := by
      rcases le_total j i with h | h
      · have : H = i := max_eq_left h
        rw [this]
        exact le_max_left _ _
      · have : H = j := max_eq_right h
        rw [this]
        exact le_trans (Nat.pow_le_pow_left (by decide) j) (le_max_right _ _)
    have hmax : max (2 ^ i) (3 ^ j) = min (2 ^ i) (3 ^ j) + D (2 ^ i) (3 ^ j) := by
      unfold D
      omega
    have hlt := lt_two_pow_of_le_sq hB hv H hH
    rw [he] at hm hmax
    have : 2 ^ H ≤ (4 * H ^ 2 + 1) * v := by
      calc 2 ^ H ≤ min (2 ^ i) (3 ^ j) + v := by omega
        _ ≤ p2_of j ^ 2 * v + v := by omega
        _ ≤ 4 * H ^ 2 * v + v := by nlinarith
        _ = (4 * H ^ 2 + 1) * v := by ring
    omega

end PowDiff
