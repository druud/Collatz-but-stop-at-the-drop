-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhinBound
import AcceleratedCollatz.TSternBrocotCert
import AcceleratedCollatz.TWidthRecord

/-!
  `RhinBound 1 2` up to Order 10^60: 3^n ≤ p2(n)^2 (2^p2(n) - 3^n) for 1 ≤ n ≤ 10^60
  (`rhinBoundUpTo_one_two`). Between upper record Orders the ratio 2^p2(n)/3^n does not fall
  below its value at the last record and p2 does not fall, so the records suffice
  (`rhinBoundUpTo_of_records`). At a record fraction p/n the bound is checked exactly for
  n ≤ 100 and otherwise from a bracket 3^K < 2^b by b n + K/(p^2/2) + 1 ≤ p K
  (`rhinOK_spec`), with (M + 1)^K ≤ 2^(K/(M/2) + 1) M^K (`succ_pow_le`). The certified walk
  at K = 2^400 checks every node until the denominators pass 10^60 (`rhinWalk_spec`); every
  upper record Order up to 10^60 is the upper denominator of one of these nodes. The walk
  is computed by the kernel (`rhinWalk_ok`): 649 steps, the 320 upper record Orders.
-/

namespace AcceleratedCollatz

/-! ### (M + 1)^K against M^K -/

/-- (M + 1)^j (t + 1) ≤ M^(j + 1) for M = j + t + 1. -/
theorem succ_pow_mul_le : ∀ j t, (j + t + 2) ^ j * (t + 1) ≤ (j + t + 1) ^ (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro t
    simp
  | succ j ih =>
    intro t
    have h := ih (t + 1)
    have he1 : j + (t + 1) + 2 = j + 1 + t + 2 := by ring
    have he2 : j + (t + 1) + 1 = j + 1 + t + 1 := by ring
    rw [he1, he2] at h
    have hk : (j + 1 + t + 2) * (t + 1) ≤ (j + 1 + t + 1) * (t + 1 + 1) := by nlinarith
    calc (j + 1 + t + 2) ^ (j + 1) * (t + 1)
        = (j + 1 + t + 2) ^ j * ((j + 1 + t + 2) * (t + 1)) := by ring
      _ ≤ (j + 1 + t + 2) ^ j * ((j + 1 + t + 1) * (t + 1 + 1)) := Nat.mul_le_mul_left _ hk
      _ = (j + 1 + t + 2) ^ j * (t + 1 + 1) * (j + 1 + t + 1) := by ring
      _ ≤ (j + 1 + t + 1) ^ (j + 1) * (j + 1 + t + 1) := Nat.mul_le_mul_right _ h
      _ = (j + 1 + t + 1) ^ (j + 1 + 1) := (pow_succ _ _).symm

/-- (M + 1)^j ≤ 2 M^j for 2j ≤ M. -/
theorem succ_pow_le_two_mul {M j : ℕ} (hj : 2 * j ≤ M) : (M + 1) ^ j ≤ 2 * M ^ j := by
  rcases Nat.eq_zero_or_pos M with h0 | hM
  · have : j = 0 := by omega
    subst this
    simp
  · obtain ⟨t, rfl⟩ : ∃ t, M = j + t + 1 := ⟨M - j - 1, by omega⟩
    have h := succ_pow_mul_le j t
    have hj' : j ≤ t + 1 := by omega
    have h2 : (j + t + 1) ^ (j + 1) ≤ 2 * (j + t + 1) ^ j * (t + 1) := by
      rw [pow_succ]
      have : j + t + 1 ≤ 2 * (t + 1) := by omega
      calc (j + t + 1) ^ j * (j + t + 1) ≤ (j + t + 1) ^ j * (2 * (t + 1)) :=
            Nat.mul_le_mul_left _ this
        _ = 2 * (j + t + 1) ^ j * (t + 1) := by ring
    exact Nat.le_of_mul_le_mul_right (h.trans h2) (by omega)

/-- (M + 1)^K ≤ 2^(K/(M/2) + 1) M^K for M ≥ 2. -/
theorem succ_pow_le {M : ℕ} (hM : 2 ≤ M) (K : ℕ) :
    (M + 1) ^ K ≤ 2 ^ (K / (M / 2) + 1) * M ^ K := by
  have hh : 0 < M / 2 := by omega
  have hh2 : 2 * (M / 2) ≤ M := Nat.mul_div_le M 2
  have hr : K % (M / 2) < M / 2 := Nat.mod_lt _ hh
  have hK : K = M / 2 * (K / (M / 2)) + K % (M / 2) := (Nat.div_add_mod K (M / 2)).symm
  have hA : ((M + 1) ^ (M / 2)) ^ (K / (M / 2)) ≤ (2 * M ^ (M / 2)) ^ (K / (M / 2)) :=
    Nat.pow_le_pow_left (succ_pow_le_two_mul hh2) _
  have hB : (M + 1) ^ (K % (M / 2)) ≤ 2 * M ^ (K % (M / 2)) :=
    succ_pow_le_two_mul (by omega)
  calc (M + 1) ^ K = ((M + 1) ^ (M / 2)) ^ (K / (M / 2)) * (M + 1) ^ (K % (M / 2)) := by
        conv_lhs => rw [hK]
        rw [pow_add, pow_mul]
    _ ≤ (2 * M ^ (M / 2)) ^ (K / (M / 2)) * (2 * M ^ (K % (M / 2))) := Nat.mul_le_mul hA hB
    _ = 2 ^ (K / (M / 2) + 1) * M ^ (M / 2 * (K / (M / 2)) + K % (M / 2)) := by
        rw [Nat.mul_pow, ← pow_mul, pow_add M, pow_succ 2]
        ring
    _ = 2 ^ (K / (M / 2) + 1) * M ^ K := by
        rw [← hK]

/-! ### The check at a fraction -/

/-- The bound at p/n: exact for n ≤ 100, else by the bracket end b. -/
def rhinOK (K b p n : ℕ) : Bool :=
  if n ≤ 100 then decide (3 ^ n * (1 + p * p) ≤ p * p * 2 ^ p)
  else decide (2 ≤ p) && decide (b * n + K / (p * p / 2) + 1 ≤ p * K)

/-- The check gives 3^n (1 + p^2) ≤ p^2 2^p. -/
theorem rhinOK_spec {K b p n : ℕ} (hb : 3 ^ K < 2 ^ b) (hK : 1 ≤ K)
    (h : rhinOK K b p n = true) : 3 ^ n * (1 + p * p) ≤ p * p * 2 ^ p := by
  unfold rhinOK at h
  by_cases hn : n ≤ 100
  · rw [ite_eq_left hn] at h
    exact of_decide_eq_true h
  · rw [ite_eq_right hn, Bool.and_eq_true] at h
    have hp := of_decide_eq_true h.1
    have hc := of_decide_eq_true h.2
    have hM : 2 ≤ p * p := by nlinarith
    by_contra hlt
    push Not at hlt
    have h1 : (p * p * 2 ^ p) ^ K < (3 ^ n * (1 + p * p)) ^ K :=
      Nat.pow_lt_pow_left hlt (by omega)
    have h2 : (3 ^ n) ^ K < 2 ^ (b * n) := by
      calc (3 ^ n) ^ K = (3 ^ K) ^ n := by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ < (2 ^ b) ^ n := Nat.pow_lt_pow_left hb (by omega)
        _ = 2 ^ (b * n) := (pow_mul 2 b n).symm
    have h3 : (1 + p * p) ^ K ≤ 2 ^ (K / (p * p / 2) + 1) * (p * p) ^ K := by
      rw [Nat.add_comm]
      exact succ_pow_le hM K
    have hpos : 0 < (1 + p * p) ^ K := Nat.pow_pos (by omega)
    have h4 : (3 ^ n * (1 + p * p)) ^ K < (p * p * 2 ^ p) ^ K := by
      calc (3 ^ n * (1 + p * p)) ^ K = (3 ^ n) ^ K * (1 + p * p) ^ K := Nat.mul_pow _ _ _
        _ < 2 ^ (b * n) * (1 + p * p) ^ K := Nat.mul_lt_mul_of_pos_right h2 hpos
        _ ≤ 2 ^ (b * n) * (2 ^ (K / (p * p / 2) + 1) * (p * p) ^ K) :=
            Nat.mul_le_mul_left _ h3
        _ = 2 ^ (b * n + (K / (p * p / 2) + 1)) * (p * p) ^ K := by
            rw [pow_add]
            ring
        _ ≤ 2 ^ (p * K) * (p * p) ^ K :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
        _ = (p * p * 2 ^ p) ^ K := by
            rw [Nat.mul_pow, pow_mul]
            ring
    exact absurd (h1.trans h4) (lt_irrefl _)

/-! ### The checked walk -/

/-- The certified walk that checks the upper fraction of every node until the sum of the
    denominators passes N. -/
def rhinWalk (K a b N : ℕ) : ℕ → SBNode → Bool
  | 0, _ => false
  | f + 1, s =>
    rhinOK K b s.hiNum s.hiDen &&
      (decide (N < s.loDen + s.hiDen) ||
        match sbCertStep K a b s with
        | some t => rhinWalk K a b N f t
        | none => false)

/-- A successful checked walk from node j reaches a node k ≥ j whose denominators sum past
    N, and every node from j to k passes the check. -/
theorem rhinWalk_spec {K a b N : ℕ} (h : Log2Bracket K a b) (hK : 1 ≤ K) :
    ∀ f j, rhinWalk K a b N f (sbWalk j) = true →
      ∃ k, j ≤ k ∧ N < (sbWalk k).loDen + (sbWalk k).hiDen ∧
        ∀ i, j ≤ i → i ≤ k → rhinOK K b (sbWalk i).hiNum (sbWalk i).hiDen = true := by
  intro f
  induction f with
  | zero =>
    intro j hw
    exact absurd hw (by simp [rhinWalk])
  | succ f ih =>
    intro j hw
    rw [rhinWalk, Bool.and_eq_true, Bool.or_eq_true] at hw
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
theorem rhinWalk_ok :
    rhinWalk (2 ^ 400) (log2Lo 3 803 400) (log2Hi 3 803 400) (10 ^ 60) 1000 (sbWalk 0) = true := by
  decide +kernel

/-! ### From the records to every Order -/

/-- `RhinBound K C` for the Orders 1 ≤ n ≤ N. -/
def RhinBoundUpTo (K C N : ℕ) : Prop :=
  ∀ n, 1 ≤ n → n ≤ N → 3 ^ n ≤ K * p2_of n ^ C * (2 ^ p2_of n - 3 ^ n)

/-- The bound in product form: 3^n (1 + Q^2) ≤ Q^2 2^Q with Q = p2(n). -/
def RhinAt (n : ℕ) : Prop := 3 ^ n * (1 + p2_of n * p2_of n) ≤ p2_of n * p2_of n * 2 ^ p2_of n

/-- The product form at every Order up to N gives `RhinBoundUpTo 1 2 N`. -/
theorem rhinBoundUpTo_of_rhinAt {N : ℕ} (h : ∀ n, 1 ≤ n → n ≤ N → RhinAt n) :
    RhinBoundUpTo 1 2 N := by
  intro n hn1 hnN
  have hr := h n hn1 hnN
  unfold RhinAt at hr
  rw [Nat.one_mul, pow_two, Nat.mul_sub]
  have he : 3 ^ n * (1 + p2_of n * p2_of n) = 3 ^ n + p2_of n * p2_of n * 3 ^ n := by ring
  omega

/-- The product form at the last upper record Order a ≤ n gives it at n. -/
theorem rhinAt_of_record {a n : ℕ} (ha : 1 ≤ a) (hR : UpperRecord a)
    (hno : ∀ k, a < k → k ≤ n → ¬UpperRecord k) (han : a ≤ n) (hA : RhinAt a) :
    RhinAt n := by
  have hbf := blockFactor_le_of_upperRecord hR hno n (by omega) le_rfl
  rw [blockFactor_le_iff] at hbf
  have hcross : 3 ^ n * 2 ^ p2_of a ≤ 3 ^ a * 2 ^ p2_of n := by exact_mod_cast hbf
  have hPQ : p2_of a ≤ p2_of n := p2_of_mono han
  unfold RhinAt at hA ⊢
  set P := p2_of a
  set Q := p2_of n
  have hP1 : 1 ≤ P := by
    change 1 ≤ p2_of a
    unfold p2_of
    omega
  have hPP : 0 < P * P * 3 ^ a := Nat.mul_pos (Nat.mul_pos hP1 hP1) (Nat.pow_pos (by decide))
  have hq : (1 + Q * Q) * (P * P) ≤ (1 + P * P) * (Q * Q) := by nlinarith
  apply Nat.le_of_mul_le_mul_right _ hPP
  calc 3 ^ n * (1 + Q * Q) * (P * P * 3 ^ a)
      = 3 ^ n * 3 ^ a * ((1 + Q * Q) * (P * P)) := by ring
    _ ≤ 3 ^ n * 3 ^ a * ((1 + P * P) * (Q * Q)) := Nat.mul_le_mul_left _ hq
    _ = 3 ^ n * (Q * Q) * (3 ^ a * (1 + P * P)) := by ring
    _ ≤ 3 ^ n * (Q * Q) * (P * P * 2 ^ P) := Nat.mul_le_mul_left _ hA
    _ = (3 ^ n * 2 ^ P) * (P * P * (Q * Q)) := by ring
    _ ≤ (3 ^ a * 2 ^ Q) * (P * P * (Q * Q)) := Nat.mul_le_mul_right _ hcross
    _ = Q * Q * 2 ^ Q * (P * P * 3 ^ a) := by ring

/-- The product form at every upper record Order up to N gives `RhinBoundUpTo 1 2 N`. -/
theorem rhinBoundUpTo_of_records {N : ℕ}
    (h : ∀ a, 1 ≤ a → a ≤ N → UpperRecord a → RhinAt a) : RhinBoundUpTo 1 2 N := by
  apply rhinBoundUpTo_of_rhinAt
  intro n hn1 hnN
  have hex : ∃ a, a ≤ n ∧ 1 ≤ a ∧ UpperRecord a := ⟨1, hn1, le_rfl, fun x hx1 hx => by omega⟩
  classical
  let a := Nat.findGreatest (fun a => 1 ≤ a ∧ UpperRecord a) n
  obtain ⟨a0, ha0n, ha0⟩ := hex
  have hspec : 1 ≤ a ∧ UpperRecord a :=
    Nat.findGreatest_spec (P := fun a => 1 ≤ a ∧ UpperRecord a) ha0n ha0
  have han : a ≤ n := Nat.findGreatest_le n
  have hno : ∀ k, a < k → k ≤ n → ¬UpperRecord k := by
    intro k hak hkn hk
    exact Nat.findGreatest_is_greatest hak hkn ⟨by omega, hk⟩
  exact rhinAt_of_record hspec.1 hspec.2 hno han (h a hspec.1 (by omega) hspec.2)

set_option exponentiation.threshold 500 in
/-- `RhinBound 1 2` for every Order 1 ≤ n ≤ 10^60. -/
theorem rhinBoundUpTo_one_two : RhinBoundUpTo 1 2 (10 ^ 60) := by
  apply rhinBoundUpTo_of_records
  intro a ha1 haN hR
  have hbr := log2Bracket_pow3 803 400
  have hK : 1 ≤ 2 ^ 400 := Nat.one_le_two_pow
  obtain ⟨k, -, hNk, hall⟩ := rhinWalk_spec hbr hK 1000 0 rhinWalk_ok
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
  exact rhinOK_spec (log2Bracket_pow3 803 400).2 hK hok

end AcceleratedCollatz
