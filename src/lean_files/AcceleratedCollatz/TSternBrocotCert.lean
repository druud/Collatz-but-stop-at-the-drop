-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSmoothProgram
import AcceleratedCollatz.TSternBrocot

/-!
  The integer convergent of log2 3: the Stern–Brocot walk towards log2 3 with an integer
  interval, in place of real numbers. A bracket a, b for K ≥ 1 is 2^a ≤ 3^K < 2^b
  (`Log2Bracket`), so a/K ≤ log2 3 < b/K. The certified walk (`sbCert`) compares each
  mediant p/n only with these two fractions: p K ≤ a n puts it below log2 3, b n ≤ p K
  above; else it stops. Each decided step is the step of `sbWalk` (`sbCertStep_eq`), so the
  walk ends at a node of `sbWalk` (`exists_sbCert`), whose fractions are record fractions
  (`recordFrac_sbWalk_hi`, `recordFrac_sbWalk_lo`, `recordFrac_sbBig`). With b ≤ a + 2,
  a mediant p/n is decided once K ≥ 2n(2^p + 3^n) (`sbCertStep_isSome`), by
  4^n M^K ≤ (M + 1)^K for K ≥ 2nM (`four_pow_mul_le`).
  The bracket for K = 2^m comes from fixed-point squaring with B bits: integer bounds
  lo 2^s ≤ u^K 2^B < hi 2^s for any base u ≥ 1 (`PowInv`, `powInv_sq`), lo rounded down
  and kept at B + 1 binary digits, hi rounded up (`log2Bracket_pow`, u = 3 for the walk);
  with B = 2m + 3 the bounds stay within a factor 2 (`powTight_powBounds`), so b ≤ a + 2
  (`log2Hi_le`). Then the walk `walkAt m` passes any numerator for every large m
  (`exists_lt_walkAt`), and the A003586
  program with the least such m (`smoothJIFind`) returns the exponents of the n-th 3-smooth
  number for every n ≥ 1 (`latticeOrd_smoothJIFind`).
-/

namespace AcceleratedCollatz

/-! ### The certified walk -/

/-- a, b bracket log2 3 at K: 2^a ≤ 3^K < 2^b. -/
def Log2Bracket (K a b : ℕ) : Prop := 2 ^ a ≤ 3 ^ K ∧ 3 ^ K < 2 ^ b

/-- One step of the certified walk: the mediant p/n replaces the lower fraction when
    p K ≤ a n, the upper one when b n ≤ p K; else none. -/
def sbCertStep (K a b : ℕ) (s : SBNode) : Option SBNode :=
  if (s.loNum + s.hiNum) * K ≤ a * (s.loDen + s.hiDen) then
    some ⟨s.loNum + s.hiNum, s.loDen + s.hiDen, s.hiNum, s.hiDen⟩
  else if b * (s.loDen + s.hiDen) ≤ (s.loNum + s.hiNum) * K then
    some ⟨s.loNum, s.loDen, s.loNum + s.hiNum, s.loDen + s.hiDen⟩
  else none

/-- The certified walk with fuel f: it stops at the first undecided step. -/
def sbCert (K a b : ℕ) : ℕ → SBNode → SBNode
  | 0, s => s
  | f + 1, s =>
    match sbCertStep K a b s with
    | some t => sbCert K a b f t
    | none => s

/-- (p K ≤ a n) and 2^a ≤ 3^K give 2^p ≤ 3^n. -/
theorem pow_le_of_bracket {K a p n : ℕ} (ha : 2 ^ a ≤ 3 ^ K) (hK : 1 ≤ K)
    (hpn : p * K ≤ a * n) : 2 ^ p ≤ 3 ^ n := by
  have h1 : (2 ^ p) ^ K ≤ (3 ^ n) ^ K := by
    calc (2 ^ p) ^ K = 2 ^ (p * K) := (pow_mul 2 p K).symm
      _ ≤ 2 ^ (a * n) := Nat.pow_le_pow_right (by decide) hpn
      _ = (2 ^ a) ^ n := pow_mul 2 a n
      _ ≤ (3 ^ K) ^ n := Nat.pow_le_pow_left ha n
      _ = (3 ^ n) ^ K := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  exact (Nat.pow_le_pow_iff_left (by omega)).mp h1

/-- (b n ≤ p K), n ≥ 1 and 3^K < 2^b give 3^n < 2^p. -/
theorem lt_pow_of_bracket {K b p n : ℕ} (hb : 3 ^ K < 2 ^ b) (hK : 1 ≤ K) (hn : 1 ≤ n)
    (hpn : b * n ≤ p * K) : 3 ^ n < 2 ^ p := by
  have h1 : (3 ^ n) ^ K < (2 ^ p) ^ K := by
    calc (3 ^ n) ^ K = (3 ^ K) ^ n := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ < (2 ^ b) ^ n := Nat.pow_lt_pow_left hb (by omega)
      _ = 2 ^ (b * n) := (pow_mul 2 b n).symm
      _ ≤ 2 ^ (p * K) := Nat.pow_le_pow_right (by decide) hpn
      _ = (2 ^ p) ^ K := pow_mul 2 p K
  exact (Nat.pow_lt_pow_iff_left (by omega)).mp h1

/-- A decided step of the certified walk is the step of the walk towards log2 3. -/
theorem sbCertStep_eq {K a b : ℕ} (h : Log2Bracket K a b) (hK : 1 ≤ K) {s t : SBNode}
    (hs : 1 ≤ s.loDen) (ht : sbCertStep K a b s = some t) : t = sbStepQ 3 s := by
  unfold sbCertStep at ht
  by_cases h1 : (s.loNum + s.hiNum) * K ≤ a * (s.loDen + s.hiDen)
  · rw [ite_eq_left h1] at ht
    have hle := pow_le_of_bracket h.1 hK h1
    rw [sbStepQ_of_not_lt (by omega)]
    exact (Option.some.inj ht).symm
  · rw [ite_eq_right h1] at ht
    by_cases h2 : b * (s.loDen + s.hiDen) ≤ (s.loNum + s.hiNum) * K
    · rw [ite_eq_left h2] at ht
      rw [sbStepQ_of_lt (lt_pow_of_bracket h.2 hK (by omega) h2)]
      exact (Option.some.inj ht).symm
    · rw [ite_eq_right h2] at ht
      exact absurd ht (by simp)

/-- From a node of the walk towards log2 3, the certified walk ends at a later node. -/
theorem sbCert_sbWalk {K a b : ℕ} (h : Log2Bracket K a b) (hK : 1 ≤ K) :
    ∀ f k, ∃ j, sbCert K a b f (sbWalk k) = sbWalk (k + j) := by
  intro f
  induction f with
  | zero =>
    intro k
    exact ⟨0, rfl⟩
  | succ f ih =>
    intro k
    rw [sbCert]
    cases ht : sbCertStep K a b (sbWalk k) with
    | none =>
      exact ⟨0, rfl⟩
    | some t =>
      have hs : 1 ≤ (sbWalk k).loDen := one_le_sbWalkQ_loDen 3 k
      have htw : t = sbWalk (k + 1) := by
        rw [sbCertStep_eq h hK hs ht]
        exact (sbWalkQ_succ 3 k).symm
      obtain ⟨j, hj⟩ := ih (k + 1)
      refine ⟨j + 1, ?_⟩
      change sbCert K a b f t = sbWalk (k + (j + 1))
      rw [htw, hj, Nat.add_assoc, Nat.add_comm 1 j]

/-- The certified walk from the root ends at a node of the walk towards log2 3. -/
theorem exists_sbCert {K a b : ℕ} (h : Log2Bracket K a b) (hK : 1 ≤ K) (f : ℕ) :
    ∃ k, sbCert K a b f sbRoot = sbWalk k := by
  obtain ⟨j, hj⟩ := sbCert_sbWalk h hK f 0
  exact ⟨0 + j, hj⟩

/-- At an undecided node the certified walk stays. -/
theorem sbCert_of_none {K a b : ℕ} {s : SBNode} (h : sbCertStep K a b s = none) (g : ℕ) :
    sbCert K a b g s = s := by
  cases g with
  | zero => rfl
  | succ g =>
    rw [sbCert, h]

/-- Fuel f + g runs as f, then g. -/
theorem sbCert_add (K a b g : ℕ) :
    ∀ f s, sbCert K a b (f + g) s = sbCert K a b g (sbCert K a b f s) := by
  intro f
  induction f with
  | zero =>
    intro s
    rw [Nat.zero_add]
    rfl
  | succ f ih =>
    intro s
    rw [Nat.add_right_comm, sbCert, sbCert]
    cases ht : sbCertStep K a b s with
    | none =>
      exact (sbCert_of_none ht g).symm
    | some t =>
      exact ih t

/-- When the first f steps from node j are decided, the certified walk reaches node j + f. -/
theorem sbCert_reach {K a b : ℕ} (h : Log2Bracket K a b) (hK : 1 ≤ K) :
    ∀ f j, (∀ i, i < f → (sbCertStep K a b (sbWalk (j + i))).isSome) →
      sbCert K a b f (sbWalk j) = sbWalk (j + f) := by
  intro f
  induction f with
  | zero =>
    intro j _
    rfl
  | succ f ih =>
    intro j hd
    rw [sbCert]
    have h0 := hd 0 (by omega)
    rw [Nat.add_zero] at h0
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h0
    rw [ht]
    have hs : 1 ≤ (sbWalk j).loDen := one_le_sbWalkQ_loDen 3 j
    have htw : t = sbWalk (j + 1) := by
      rw [sbCertStep_eq h hK hs ht]
      exact (sbWalkQ_succ 3 j).symm
    rw [htw]
    have hrest := ih (j + 1) fun i hi => by
      rw [(by omega : j + 1 + i = j + (i + 1))]
      exact hd (i + 1) (by omega)
    change sbCert K a b f (sbWalk (j + 1)) = sbWalk (j + (f + 1))
    rw [hrest, Nat.add_assoc, Nat.add_comm 1 f]

/-! ### Every mediant is decided for a large K -/

/-- M^(j + 1) + (j + 1) M^j ≤ (M + 1)^(j + 1). -/
theorem pow_add_mul_le (M : ℕ) : ∀ j, M ^ (j + 1) + (j + 1) * M ^ j ≤ (M + 1) ^ (j + 1) := by
  intro j
  induction j with
  | zero =>
    simp
  | succ j ih =>
    calc M ^ (j + 1 + 1) + (j + 1 + 1) * M ^ (j + 1)
        ≤ (M ^ (j + 1) + (j + 1) * M ^ j) * (M + 1) := by
          rw [pow_succ M (j + 1), pow_succ M j]
          nlinarith [Nat.zero_le (M ^ j), Nat.zero_le M]
      _ ≤ (M + 1) ^ (j + 1) * (M + 1) := Nat.mul_le_mul_right _ ih
      _ = (M + 1) ^ (j + 1 + 1) := (pow_succ _ _).symm

/-- 2 M^M ≤ (M + 1)^M for M ≥ 1. -/
theorem two_mul_pow_self_le {M : ℕ} (hM : 1 ≤ M) : 2 * M ^ M ≤ (M + 1) ^ M := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  have h := pow_add_mul_le (j + 1) j
  have he : (j + 1) * (j + 1) ^ j = (j + 1) ^ (j + 1) := (pow_succ' _ _).symm
  omega

/-- 4^n M^K ≤ (M + 1)^K for M ≥ 1 and K ≥ 2 n M. -/
theorem four_pow_mul_le {M n K : ℕ} (hM : 1 ≤ M) (hK : 2 * n * M ≤ K) :
    4 ^ n * M ^ K ≤ (M + 1) ^ K := by
  obtain ⟨r, rfl⟩ : ∃ r, K = M * (2 * n) + r := ⟨K - M * (2 * n), by
    rw [Nat.mul_comm M]
    omega⟩
  have h2 : 2 ^ (2 * n) * (M ^ M) ^ (2 * n) ≤ ((M + 1) ^ M) ^ (2 * n) := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left (two_mul_pow_self_le hM) _
  have hr : M ^ r ≤ (M + 1) ^ r := Nat.pow_le_pow_left (by omega) r
  have h4 : 4 ^ n = 2 ^ (2 * n) := by
    rw [pow_mul]
    norm_num
  calc 4 ^ n * M ^ (M * (2 * n) + r) = 2 ^ (2 * n) * (M ^ M) ^ (2 * n) * M ^ r := by
        rw [pow_add, pow_mul M M (2 * n), h4, Nat.mul_assoc]
    _ ≤ ((M + 1) ^ M) ^ (2 * n) * (M + 1) ^ r := Nat.mul_le_mul h2 hr
    _ = (M + 1) ^ (M * (2 * n) + r) := by
        rw [pow_add, pow_mul (M + 1) M (2 * n)]

/-- 2^p ≠ 3^n for n ≥ 1. -/
theorem two_pow_ne_three_pow_right {p n : ℕ} (hn : 1 ≤ n) : 2 ^ p ≠ 3 ^ n := by
  intro h
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    have : 3 ^ 1 ≤ 3 ^ n := Nat.pow_le_pow_right (by decide) hn
    rw [pow_zero] at h
    omega
  · have he : Even (2 ^ p) := (Nat.even_pow' (by omega)).mpr even_two
    have ho : Odd (3 ^ n) := Odd.pow (by decide)
    rw [h] at he
    exact (Nat.not_even_iff_odd.mpr ho) he

/-- With b ≤ a + 2, the mediant p/n (n ≥ 1) is decided once K ≥ 2n(2^p + 3^n). -/
theorem sbCertStep_isSome {K a b : ℕ} (h : Log2Bracket K a b) (hab : b ≤ a + 2)
    {s : SBNode} (hn : 1 ≤ s.loDen + s.hiDen)
    (hK : 2 * (s.loDen + s.hiDen) * (2 ^ (s.loNum + s.hiNum) + 3 ^ (s.loDen + s.hiDen)) ≤ K) :
    (sbCertStep K a b s).isSome := by
  have hne := two_pow_ne_three_pow_right (p := s.loNum + s.hiNum) hn
  unfold sbCertStep
  by_cases h1 : (s.loNum + s.hiNum) * K ≤ a * (s.loDen + s.hiDen)
  · rw [ite_eq_left h1]
    rfl
  · rw [ite_eq_right h1]
    by_cases h2 : b * (s.loDen + s.hiDen) ≤ (s.loNum + s.hiNum) * K
    · rw [ite_eq_left h2]
      rfl
    · exfalso
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · -- below: 4^n 2^(pK) ≤ (2^p + 1)^K ≤ 3^(nK) < 2^((a + 2) n)
        have hM : 2 * (s.loDen + s.hiDen) * 2 ^ (s.loNum + s.hiNum) ≤ K := by
          have := Nat.mul_le_mul_left (2 * (s.loDen + s.hiDen))
            (Nat.le_add_right (2 ^ (s.loNum + s.hiNum)) (3 ^ (s.loDen + s.hiDen)))
          omega
        have hb := four_pow_mul_le (Nat.one_le_two_pow) hM
        have h3 : (2 ^ (s.loNum + s.hiNum) + 1) ^ K ≤ (3 ^ (s.loDen + s.hiDen)) ^ K :=
          Nat.pow_le_pow_left hlt K
        have h4 : (3 ^ (s.loDen + s.hiDen)) ^ K < (2 ^ (a + 2)) ^ (s.loDen + s.hiDen) := by
          calc (3 ^ (s.loDen + s.hiDen)) ^ K = (3 ^ K) ^ (s.loDen + s.hiDen) := by
                rw [← pow_mul, ← pow_mul, Nat.mul_comm]
            _ < (2 ^ b) ^ (s.loDen + s.hiDen) := Nat.pow_lt_pow_left h.2 (by omega)
            _ ≤ (2 ^ (a + 2)) ^ (s.loDen + s.hiDen) :=
                Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hab) _
        have h5 : 2 ^ (2 * (s.loDen + s.hiDen) + (s.loNum + s.hiNum) * K) <
            2 ^ ((a + 2) * (s.loDen + s.hiDen)) := by
          calc 2 ^ (2 * (s.loDen + s.hiDen) + (s.loNum + s.hiNum) * K)
              = 4 ^ (s.loDen + s.hiDen) * (2 ^ (s.loNum + s.hiNum)) ^ K := by
                rw [pow_add, pow_mul, pow_mul]
                norm_num
            _ < 2 ^ ((a + 2) * (s.loDen + s.hiDen)) := by
                rw [pow_mul]
                omega
        have h6 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h5
        have h7 : (a + 2) * (s.loDen + s.hiDen) =
            a * (s.loDen + s.hiDen) + 2 * (s.loDen + s.hiDen) := by ring
        omega
      · -- above: 4^n 3^(nK) ≤ (3^n + 1)^K ≤ 2^(pK) and 2^(a n) ≤ 3^(nK)
        have hM : 2 * (s.loDen + s.hiDen) * 3 ^ (s.loDen + s.hiDen) ≤ K := by
          have := Nat.mul_le_mul_left (2 * (s.loDen + s.hiDen))
            (Nat.le_add_left (3 ^ (s.loDen + s.hiDen)) (2 ^ (s.loNum + s.hiNum)))
          omega
        have hb := four_pow_mul_le (Nat.one_le_pow _ _ (by decide)) hM
        have h3 : (3 ^ (s.loDen + s.hiDen) + 1) ^ K ≤ (2 ^ (s.loNum + s.hiNum)) ^ K :=
          Nat.pow_le_pow_left hgt K
        have h4 : (2 ^ a) ^ (s.loDen + s.hiDen) ≤ (3 ^ (s.loDen + s.hiDen)) ^ K := by
          calc (2 ^ a) ^ (s.loDen + s.hiDen) ≤ (3 ^ K) ^ (s.loDen + s.hiDen) :=
                Nat.pow_le_pow_left h.1 _
            _ = (3 ^ (s.loDen + s.hiDen)) ^ K := by
                rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        have h5 : 2 ^ (2 * (s.loDen + s.hiDen) + a * (s.loDen + s.hiDen)) ≤
            2 ^ ((s.loNum + s.hiNum) * K) := by
          calc 2 ^ (2 * (s.loDen + s.hiDen) + a * (s.loDen + s.hiDen))
              = 4 ^ (s.loDen + s.hiDen) * (2 ^ a) ^ (s.loDen + s.hiDen) := by
                rw [pow_add, pow_mul, pow_mul]
                norm_num
            _ ≤ 4 ^ (s.loDen + s.hiDen) * (3 ^ (s.loDen + s.hiDen)) ^ K :=
                Nat.mul_le_mul_left _ h4
            _ ≤ 2 ^ ((s.loNum + s.hiNum) * K) := by
                rw [pow_mul]
                omega
        have h6 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h5
        have h7 : b * (s.loDen + s.hiDen) ≤ (a + 2) * (s.loDen + s.hiDen) :=
          Nat.mul_le_mul_right _ hab
        have h8 : (a + 2) * (s.loDen + s.hiDen) =
            a * (s.loDen + s.hiDen) + 2 * (s.loDen + s.hiDen) := by ring
        omega

/-! ### Record fractions on the walk -/

/-- An upper fraction of the walk with numerator at least 2 is a record fraction. -/
theorem recordFrac_sbWalk_hi {k : ℕ} (hk : 2 ≤ (sbWalk k).hiNum) :
    RecordFrac (sbWalk k).hiNum (sbWalk k).hiDen := by
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · exfalso
      have h1 : (sbWalk k).hiNum = 1 := by
        rcases Nat.lt_or_ge k 1 with hk0 | hk1
        · have : k = 0 := by omega
          subst this
          decide +kernel
        · have : k = 1 := by omega
          subst this
          decide +kernel
      omega
    · exact hge
  have hden : 1 ≤ (sbWalk k).hiDen := by
    rcases Nat.eq_zero_or_pos (sbWalk k).hiDen with h0 | hpos
    · exfalso
      have hdet := sbWalkQ_det 3 k
      change (sbWalk k).loDen * (sbWalk k).hiNum =
        (sbWalk k).loNum * (sbWalk k).hiDen + 1 at hdet
      rw [h0, Nat.mul_zero, Nat.zero_add] at hdet
      have hlo : 1 ≤ (sbWalk k).loDen := one_le_sbWalkQ_loDen 3 k
      have hm : 1 * 2 ≤ (sbWalk k).loDen * (sbWalk k).hiNum := Nat.mul_le_mul hlo hk
      omega
    · exact hpos
  exact ⟨hden, Or.inl ⟨(upperRecord_iff_sbWalk hden).mpr ⟨k, rfl⟩, sbWalk_hiNum hk2⟩⟩

/-- A lower fraction of the walk with numerator at least 1 is a record fraction. -/
theorem recordFrac_sbWalk_lo {k : ℕ} (hk : 1 ≤ (sbWalk k).loNum) :
    RecordFrac (sbWalk k).loNum (sbWalk k).loDen := by
  have hden : 1 ≤ (sbWalk k).loDen := one_le_sbWalkQ_loDen 3 k
  have hnum : (sbWalk k).loNum + 1 = p2_of (sbWalk k).loDen := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · exfalso
        have : k = 0 := by omega
        subst this
        have h0 : (sbWalk 0).loNum = 0 := by
          decide +kernel
        omega
      · have : k = 1 := by omega
        subst this
        decide +kernel
    · exact sbWalk_loNum hge
  refine ⟨hden, Or.inr ⟨(lowerRecord_iff_sbWalk hden).mpr ⟨k, rfl⟩, ?_⟩⟩
  omega

/-- The fraction of a node with the larger numerator (the upper one on a tie). -/
def sbBig (s : SBNode) : ℕ × ℕ :=
  if s.loNum ≤ s.hiNum then (s.hiNum, s.hiDen) else (s.loNum, s.loDen)

/-- The fraction of a node of the walk with the larger numerator, when that is at least 2,
    is a record fraction. -/
theorem recordFrac_sbBig {k : ℕ} (hk : 2 ≤ (sbBig (sbWalk k)).1) :
    RecordFrac (sbBig (sbWalk k)).1 (sbBig (sbWalk k)).2 := by
  unfold sbBig at hk ⊢
  by_cases h : (sbWalk k).loNum ≤ (sbWalk k).hiNum
  · rw [ite_eq_left h] at hk ⊢
    exact recordFrac_sbWalk_hi hk
  · rw [ite_eq_right h] at hk ⊢
    exact recordFrac_sbWalk_lo (by omega)

/-- The numerators of the walk: the upper one at least 1, the lower one at least 1 from
    step 1 on, and their sum at least k + 1. -/
theorem sbWalk_num (k : ℕ) :
    1 ≤ (sbWalk k).hiNum ∧ (1 ≤ k → 1 ≤ (sbWalk k).loNum) ∧
      k + 1 ≤ (sbWalk k).loNum + (sbWalk k).hiNum := by
  induction k with
  | zero =>
    refine ⟨?_, fun h => absurd h (by omega), ?_⟩
    · decide +kernel
    · decide +kernel
  | succ k ih =>
    obtain ⟨hhi, hlo, hsum⟩ := ih
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      refine ⟨?_, fun _ => ?_, ?_⟩
      · decide +kernel
      · decide +kernel
      · decide +kernel
    · have hlo' := hlo hkpos
      have hw : sbWalk (k + 1) = sbStepQ 3 (sbWalk k) := sbWalkQ_succ 3 k
      rw [hw]
      by_cases hc : 3 ^ ((sbWalk k).loDen + (sbWalk k).hiDen) <
          2 ^ ((sbWalk k).loNum + (sbWalk k).hiNum)
      · rw [sbStepQ_of_lt hc]
        refine ⟨?_, fun _ => hlo', ?_⟩
        · change 1 ≤ (sbWalk k).loNum + (sbWalk k).hiNum
          omega
        · change k + 1 + 1 ≤ (sbWalk k).loNum + ((sbWalk k).loNum + (sbWalk k).hiNum)
          omega
      · rw [sbStepQ_of_not_lt hc]
        refine ⟨hhi, fun _ => ?_, ?_⟩
        · change 1 ≤ (sbWalk k).loNum + (sbWalk k).hiNum
          omega
        · change k + 1 + 1 ≤ (sbWalk k).loNum + (sbWalk k).hiNum + (sbWalk k).hiNum
          omega

/-! ### Brackets by fixed-point squaring -/

variable {u : ℕ}

/-- Integer bounds on u^K: lo 2^s ≤ u^K 2^B < hi 2^s. -/
structure PowBounds where
  /-- The lower bound. -/
  lo : ℕ
  /-- The upper bound. -/
  hi : ℕ
  /-- The shift. -/
  s : ℕ
  deriving DecidableEq, Repr

/-- The bounds hold for K with B fractional bits. -/
def PowInv (u B K : ℕ) (t : PowBounds) : Prop :=
  t.lo * 2 ^ t.s ≤ u ^ K * 2 ^ B ∧ u ^ K * 2 ^ B < t.hi * 2 ^ t.s

/-- The shift r of a squaring: lo^2 / 2^(B + r) keeps B + 1 binary digits. -/
def powShift (B : ℕ) (t : PowBounds) : ℕ := Nat.log2 (t.lo * t.lo) - 2 * B

/-- One squaring: lo rounded down, hi rounded up, the shift doubled plus r. -/
def powSq (B : ℕ) (t : PowBounds) : PowBounds :=
  ⟨t.lo * t.lo / 2 ^ (B + powShift B t), t.hi * t.hi / 2 ^ (B + powShift B t) + 1,
    2 * t.s + powShift B t⟩

/-- The start: lo = u 2^B, hi = lo + 1, s = 0. -/
def powStart (u B : ℕ) : PowBounds := ⟨u * 2 ^ B, u * 2 ^ B + 1, 0⟩

/-- The bounds on u^(2^m) after m squarings. -/
def powBounds (u B m : ℕ) : PowBounds := (powSq B)^[m] (powStart u B)

theorem powBounds_succ (B m : ℕ) : powBounds u B (m + 1) = powSq B (powBounds u B m) :=
  Function.iterate_succ_apply' _ _ _

/-- A squaring takes bounds for K to bounds for 2K. -/
theorem powInv_sq {B K : ℕ} {t : PowBounds} (h : PowInv u B K t) :
    PowInv u B (2 * K) (powSq B t) := by
  have hD : 0 < 2 ^ (B + powShift B t) := Nat.two_pow_pos _
  have hB : 0 < 2 ^ B := Nat.two_pow_pos _
  have hs : 2 ^ (2 * t.s + powShift B t) * 2 ^ B =
      2 ^ (B + powShift B t) * (2 ^ t.s * 2 ^ t.s) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have h3 : u ^ (2 * K) * 2 ^ B * 2 ^ B = (u ^ K * 2 ^ B) * (u ^ K * 2 ^ B) := by
    rw [Nat.two_mul, pow_add]
    ring
  constructor
  · change t.lo * t.lo / 2 ^ (B + powShift B t) * 2 ^ (2 * t.s + powShift B t)
      ≤ u ^ (2 * K) * 2 ^ B
    have hq : t.lo * t.lo / 2 ^ (B + powShift B t) * 2 ^ (B + powShift B t)
        ≤ t.lo * t.lo := Nat.div_mul_le_self _ _
    have hsq : (t.lo * 2 ^ t.s) * (t.lo * 2 ^ t.s) ≤ (u ^ K * 2 ^ B) * (u ^ K * 2 ^ B) :=
      Nat.mul_le_mul h.1 h.1
    apply Nat.le_of_mul_le_mul_right _ hB
    calc t.lo * t.lo / 2 ^ (B + powShift B t) * 2 ^ (2 * t.s + powShift B t) * 2 ^ B
        = t.lo * t.lo / 2 ^ (B + powShift B t) * 2 ^ (B + powShift B t)
            * (2 ^ t.s * 2 ^ t.s) := by
          rw [Nat.mul_assoc, hs, Nat.mul_assoc]
      _ ≤ t.lo * t.lo * (2 ^ t.s * 2 ^ t.s) := Nat.mul_le_mul_right _ hq
      _ = (t.lo * 2 ^ t.s) * (t.lo * 2 ^ t.s) := by ring
      _ ≤ (u ^ K * 2 ^ B) * (u ^ K * 2 ^ B) := hsq
      _ = u ^ (2 * K) * 2 ^ B * 2 ^ B := h3.symm
  · change u ^ (2 * K) * 2 ^ B
      < (t.hi * t.hi / 2 ^ (B + powShift B t) + 1) * 2 ^ (2 * t.s + powShift B t)
    have hq : t.hi * t.hi < (t.hi * t.hi / 2 ^ (B + powShift B t) + 1) *
        2 ^ (B + powShift B t) := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.lt_div_mul_add hD
    have hsq : (u ^ K * 2 ^ B) * (u ^ K * 2 ^ B) < (t.hi * 2 ^ t.s) * (t.hi * 2 ^ t.s) :=
      Nat.mul_self_lt_mul_self h.2
    have hss : 0 < 2 ^ t.s * 2 ^ t.s := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ B)
    calc u ^ (2 * K) * 2 ^ B * 2 ^ B = (u ^ K * 2 ^ B) * (u ^ K * 2 ^ B) := h3
      _ < (t.hi * 2 ^ t.s) * (t.hi * 2 ^ t.s) := hsq
      _ = t.hi * t.hi * (2 ^ t.s * 2 ^ t.s) := by ring
      _ < (t.hi * t.hi / 2 ^ (B + powShift B t) + 1) * 2 ^ (B + powShift B t)
            * (2 ^ t.s * 2 ^ t.s) := Nat.mul_lt_mul_of_pos_right hq hss
      _ = (t.hi * t.hi / 2 ^ (B + powShift B t) + 1) * 2 ^ (2 * t.s + powShift B t)
            * 2 ^ B := by
          rw [Nat.mul_assoc _ (2 ^ (2 * t.s + powShift B t)), hs, Nat.mul_assoc]

/-- The bounds after m squarings hold for u^(2^m). -/
theorem powInv_powBounds (B m : ℕ) : PowInv u B (2 ^ m) (powBounds u B m) := by
  induction m with
  | zero =>
    constructor
    · change u * 2 ^ B * 2 ^ 0 ≤ u ^ 2 ^ 0 * 2 ^ B
      simp
    · change u ^ 2 ^ 0 * 2 ^ B < (u * 2 ^ B + 1) * 2 ^ 0
      simp
  | succ m ih =>
    rw [powBounds_succ, pow_succ, Nat.mul_comm]
    exact powInv_sq ih

/-- A squaring keeps lo at least 2^B. -/
theorem two_pow_le_powSq_lo {B : ℕ} {t : PowBounds} (h : 2 ^ B ≤ t.lo) :
    2 ^ B ≤ (powSq B t).lo := by
  change 2 ^ B ≤ t.lo * t.lo / 2 ^ (B + powShift B t)
  have hsq : 2 ^ (2 * B) ≤ t.lo * t.lo := by
    rw [Nat.two_mul, pow_add]
    exact Nat.mul_le_mul h h
  have hne : t.lo * t.lo ≠ 0 := by
    have := Nat.two_pow_pos (2 * B)
    omega
  have hL : 2 * B ≤ Nat.log2 (t.lo * t.lo) := (Nat.le_log2 hne).mpr hsq
  have hle : 2 ^ Nat.log2 (t.lo * t.lo) ≤ t.lo * t.lo := Nat.log2_self_le hne
  rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← pow_add]
  unfold powShift
  have he : B + (B + (Nat.log2 (t.lo * t.lo) - 2 * B)) = Nat.log2 (t.lo * t.lo) := by
    omega
  rw [he]
  exact hle

/-- lo stays at least 2^B. -/
theorem two_pow_le_powBounds_lo (hu : 1 ≤ u) (B m : ℕ) : 2 ^ B ≤ (powBounds u B m).lo := by
  induction m with
  | zero =>
    change 2 ^ B ≤ u * 2 ^ B
    exact Nat.le_mul_of_pos_left _ hu
  | succ m ih =>
    rw [powBounds_succ]
    exact two_pow_le_powSq_lo ih

/-- The bounds at step i are within a factor 1 + 8 4^i / 2^B. -/
def PowTight (B i : ℕ) (t : PowBounds) : Prop :=
  2 ^ B ≤ t.lo ∧ t.hi * 2 ^ B ≤ t.lo * (2 ^ B + 8 * 4 ^ i)

/-- A squaring takes the factor at step i to that at step i + 1, when 8 4^i ≤ 2^B. -/
theorem powTight_sq {B i : ℕ} {t : PowBounds} (h : PowTight B i t)
    (hg : 8 * 4 ^ i ≤ 2 ^ B) : PowTight B (i + 1) (powSq B t) := by
  obtain ⟨hlo, hhi⟩ := h
  refine ⟨two_pow_le_powSq_lo hlo, ?_⟩
  have hlo' := two_pow_le_powSq_lo hlo
  change (t.hi * t.hi / 2 ^ (B + powShift B t) + 1) * 2 ^ B ≤
    t.lo * t.lo / 2 ^ (B + powShift B t) * (2 ^ B + 8 * 4 ^ (i + 1))
  change 2 ^ B ≤ t.lo * t.lo / 2 ^ (B + powShift B t) at hlo'
  have hD : 0 < 2 ^ (B + powShift B t) := Nat.two_pow_pos _
  have hF : 0 < 2 ^ B := Nat.two_pow_pos _
  have h4 : 8 * 4 ^ (i + 1) = 4 * (8 * 4 ^ i) := by ring
  rw [h4]
  have hdivhi : t.hi * t.hi / 2 ^ (B + powShift B t) * 2 ^ (B + powShift B t) ≤
      t.hi * t.hi := Nat.div_mul_le_self _ _
  have hdivlo : t.lo * t.lo < (t.lo * t.lo / 2 ^ (B + powShift B t) + 1) *
      2 ^ (B + powShift B t) := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_div_mul_add hD
  have hsq : (t.hi * 2 ^ B) * (t.hi * 2 ^ B) ≤
      (t.lo * (2 ^ B + 8 * 4 ^ i)) * (t.lo * (2 ^ B + 8 * 4 ^ i)) := Nat.mul_le_mul hhi hhi
  have hg8 : 8 ≤ 8 * 4 ^ i := by
    have := Nat.one_le_pow i 4 (by decide)
    omega
  -- with D = 2^(B+r), F = 2^B, g = 8 4^i, L = lo^2 / D, H = hi^2 / D:
  -- H D F^2 ≤ lo^2 (F + g)^2 < (L + 1) D (F + g)^2, so H F^2 < (L + 1)(F + g)^2,
  -- and (H + 1) F^2 ≤ L F (F + 4g) by F ≤ L, 8 ≤ g ≤ F.
  have hHF : t.hi * t.hi / 2 ^ (B + powShift B t) * (2 ^ B * 2 ^ B) <
      (t.lo * t.lo / 2 ^ (B + powShift B t) + 1) * ((2 ^ B + 8 * 4 ^ i) *
        (2 ^ B + 8 * 4 ^ i)) := by
    apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ (B + powShift B t))
    calc t.hi * t.hi / 2 ^ (B + powShift B t) * (2 ^ B * 2 ^ B) * 2 ^ (B + powShift B t)
        = t.hi * t.hi / 2 ^ (B + powShift B t) * 2 ^ (B + powShift B t) *
            (2 ^ B * 2 ^ B) := by ring
      _ ≤ t.hi * t.hi * (2 ^ B * 2 ^ B) := Nat.mul_le_mul_right _ hdivhi
      _ = (t.hi * 2 ^ B) * (t.hi * 2 ^ B) := by ring
      _ ≤ (t.lo * (2 ^ B + 8 * 4 ^ i)) * (t.lo * (2 ^ B + 8 * 4 ^ i)) := hsq
      _ = t.lo * t.lo * ((2 ^ B + 8 * 4 ^ i) * (2 ^ B + 8 * 4 ^ i)) := by ring
      _ < (t.lo * t.lo / 2 ^ (B + powShift B t) + 1) * 2 ^ (B + powShift B t) *
            ((2 ^ B + 8 * 4 ^ i) * (2 ^ B + 8 * 4 ^ i)) :=
          Nat.mul_lt_mul_of_pos_right hdivlo (Nat.mul_pos (by omega) (by omega))
      _ = (t.lo * t.lo / 2 ^ (B + powShift B t) + 1) *
            ((2 ^ B + 8 * 4 ^ i) * (2 ^ B + 8 * 4 ^ i)) * 2 ^ (B + powShift B t) := by
          ring
  apply Nat.le_of_mul_le_mul_right _ hF
  generalize t.hi * t.hi / 2 ^ (B + powShift B t) = H at hHF ⊢
  generalize t.lo * t.lo / 2 ^ (B + powShift B t) = L at hHF hlo' ⊢
  generalize 2 ^ B = F at hHF hlo' hg hF ⊢
  generalize 8 * 4 ^ i = g at hHF hg hg8 ⊢
  nlinarith [Nat.mul_le_mul hlo' hg, Nat.mul_le_mul hlo' hg8, Nat.mul_le_mul hlo' hlo',
    Nat.mul_le_mul_left L hg]

/-- With 8 4^m ≤ 2^B the bounds after m squarings are within the factor of step m. -/
theorem powTight_powBounds (hu : 1 ≤ u) {B m : ℕ} (hg : 8 * 4 ^ m ≤ 2 ^ B) :
    PowTight B m (powBounds u B m) := by
  induction m with
  | zero =>
    refine ⟨by
      change 2 ^ B ≤ u * 2 ^ B
      exact Nat.le_mul_of_pos_left _ hu, ?_⟩
    change (u * 2 ^ B + 1) * 2 ^ B ≤ u * 2 ^ B * (2 ^ B + 8 * 4 ^ 0)
    have := Nat.two_pow_pos B
    have h8 : 8 * 4 ^ 0 = 8 := by norm_num
    rw [h8]
    nlinarith
  | succ m ih =>
    have hg' : 8 * 4 ^ m ≤ 2 ^ B := by
      have : 4 ^ m ≤ 4 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [powBounds_succ]
    exact powTight_sq (ih hg') hg'

/-- The lower end of the bracket: log2(lo) + s - B. -/
def log2Lo (u B m : ℕ) : ℕ := Nat.log2 (powBounds u B m).lo + (powBounds u B m).s - B

/-- The upper end of the bracket: log2(hi) + 1 + s - B. -/
def log2Hi (u B m : ℕ) : ℕ := Nat.log2 (powBounds u B m).hi + 1 + (powBounds u B m).s - B

/-- The fixed-point bounds bracket u^(2^m) between powers of 2. -/
theorem log2Bracket_pow (hu : 1 ≤ u) (B m : ℕ) :
    2 ^ log2Lo u B m ≤ u ^ 2 ^ m ∧ u ^ 2 ^ m < 2 ^ log2Hi u B m := by
  have hinv := powInv_powBounds (u := u) B m
  have hlo := two_pow_le_powBounds_lo hu B m
  have hB : 0 < 2 ^ B := Nat.two_pow_pos B
  have hlo0 : (powBounds u B m).lo ≠ 0 := by omega
  have hloB : B ≤ Nat.log2 (powBounds u B m).lo := (Nat.le_log2 hlo0).mpr hlo
  have hlohi : (powBounds u B m).lo < (powBounds u B m).hi := by
    have h1 := hinv.1.trans_lt hinv.2
    exact Nat.lt_of_mul_lt_mul_right h1
  have hhi0 : (powBounds u B m).hi ≠ 0 := by omega
  have hhiB : B ≤ Nat.log2 (powBounds u B m).hi :=
    (Nat.le_log2 hhi0).mpr (by omega)
  constructor
  · apply Nat.le_of_mul_le_mul_right _ hB
    calc 2 ^ log2Lo u B m * 2 ^ B
        = 2 ^ Nat.log2 (powBounds u B m).lo * 2 ^ (powBounds u B m).s := by
          rw [← pow_add, ← pow_add]
          unfold log2Lo
          congr 1
          omega
      _ ≤ (powBounds u B m).lo * 2 ^ (powBounds u B m).s :=
          Nat.mul_le_mul_right _ (Nat.log2_self_le hlo0)
      _ ≤ u ^ 2 ^ m * 2 ^ B := hinv.1
  · apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ B)
    calc u ^ 2 ^ m * 2 ^ B < (powBounds u B m).hi * 2 ^ (powBounds u B m).s := hinv.2
      _ ≤ 2 ^ (Nat.log2 (powBounds u B m).hi + 1) * 2 ^ (powBounds u B m).s :=
          Nat.mul_le_mul_right _ (Nat.lt_log2_self).le
      _ = 2 ^ log2Hi u B m * 2 ^ B := by
          rw [← pow_add, ← pow_add]
          unfold log2Hi
          congr 1
          omega

/-- With 8 4^m ≤ 2^B the bracket has width at most 2. -/
theorem log2Hi_le (hu : 1 ≤ u) {B m : ℕ} (hg : 8 * 4 ^ m ≤ 2 ^ B) :
    log2Hi u B m ≤ log2Lo u B m + 2 := by
  obtain ⟨hlo, hhi⟩ := powTight_powBounds hu hg
  have hB : 0 < 2 ^ B := Nat.two_pow_pos B
  have h2 : (powBounds u B m).hi ≤ 2 * (powBounds u B m).lo := by
    apply Nat.le_of_mul_le_mul_right _ hB
    calc (powBounds u B m).hi * 2 ^ B ≤ (powBounds u B m).lo * (2 ^ B + 8 * 4 ^ m) := hhi
      _ ≤ (powBounds u B m).lo * (2 ^ B + 2 ^ B) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (powBounds u B m).lo * 2 ^ B := by ring
  have hlo0 : (powBounds u B m).lo ≠ 0 := by omega
  have hhi0 : (powBounds u B m).hi ≠ 0 := by
    have := (Nat.mul_le_mul_right (2 ^ (powBounds u B m).s) hlo).trans
      ((powInv_powBounds (u := u) B m).1.trans (powInv_powBounds (u := u) B m).2.le)
    intro h0
    rw [h0, Nat.zero_mul] at this
    have := Nat.mul_pos hB (Nat.two_pow_pos (powBounds u B m).s)
    omega
  have hlt : (powBounds u B m).hi < 2 ^ (Nat.log2 (powBounds u B m).lo + 2) := by
    have := (Nat.lt_log2_self (n := (powBounds u B m).lo))
    rw [pow_succ]
    omega
  have hl : Nat.log2 (powBounds u B m).hi < Nat.log2 (powBounds u B m).lo + 2 :=
    (Nat.log2_lt hhi0).mpr hlt
  unfold log2Hi log2Lo
  omega

/-! ### The walk and the A003586 program -/

/-- The fixed-point bounds bracket log2 3 at 2^m. -/
theorem log2Bracket_pow3 (B m : ℕ) : Log2Bracket (2 ^ m) (log2Lo 3 B m) (log2Hi 3 B m) :=
  log2Bracket_pow (by decide) B m

/-- The certified walk towards log2 3 at K = 2^m with B bits, fuel 2^(m + 1). -/
def log2Walk (B m : ℕ) : SBNode :=
  sbCert (2 ^ m) (log2Lo 3 B m) (log2Hi 3 B m) (2 ^ (m + 1)) sbRoot

/-- `log2Walk` ends at a node of the walk towards log2 3. -/
theorem exists_log2Walk (B m : ℕ) : ∃ k, log2Walk B m = sbWalk k :=
  exists_sbCert (log2Bracket_pow3 B m) Nat.one_le_two_pow _

/-- The walk at m with B = 2m + 3. -/
def walkAt (m : ℕ) : SBNode := log2Walk (2 * m + 3) m

/-- The fraction of `walkAt m` with the larger numerator, when that is at least 2, is a
    record fraction. -/
theorem recordFrac_walkAt {m : ℕ} (h : 2 ≤ (sbBig (walkAt m)).1) :
    RecordFrac (sbBig (walkAt m)).1 (sbBig (walkAt m)).2 := by
  obtain ⟨k, hk⟩ := exists_log2Walk (2 * m + 3) m
  unfold walkAt at h ⊢
  rw [hk] at h ⊢
  exact recordFrac_sbBig h

/-- For every N, the larger numerator of `walkAt m` exceeds N for every large m. -/
theorem exists_lt_walkAt (N : ℕ) : ∃ m0, ∀ m, m0 ≤ m → N < (sbBig (walkAt m)).1 := by
  let need (j : ℕ) : ℕ := 2 * ((sbWalk j).loDen + (sbWalk j).hiDen) *
    (2 ^ ((sbWalk j).loNum + (sbWalk j).hiNum) + 3 ^ ((sbWalk j).loDen + (sbWalk j).hiDen))
  let k0 := 2 * N + 2
  let C := ∑ j ∈ Finset.range k0, need j
  refine ⟨C + k0, fun m hm => ?_⟩
  have hK : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hmK : m < 2 ^ m := Nat.lt_two_pow_self
  have hbr := log2Bracket_pow3 (2 * m + 3) m
  have hab : log2Hi 3 (2 * m + 3) m ≤ log2Lo 3 (2 * m + 3) m + 2 := by
    apply log2Hi_le (by decide)
    rw [pow_add, pow_mul]
    norm_num
    omega
  have hdec : ∀ i, i < k0 →
      (sbCertStep (2 ^ m) (log2Lo 3 (2 * m + 3) m) (log2Hi 3 (2 * m + 3) m)
        (sbWalk (0 + i))).isSome := by
    intro i hi
    rw [Nat.zero_add]
    have hn : 1 ≤ (sbWalk i).loDen + (sbWalk i).hiDen := by
      have := one_le_sbWalkQ_loDen 3 i
      change 1 ≤ (sbWalk i).loDen at this
      omega
    have hle : need i ≤ C := Finset.single_le_sum (fun j _ => Nat.zero_le (need j))
      (Finset.mem_range.mpr hi)
    exact sbCertStep_isSome hbr hab hn (hle.trans (by omega))
  have hreach := sbCert_reach hbr hK k0 0 hdec
  have hfuel : k0 ≤ 2 ^ (m + 1) := by
    have : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨j, hj⟩ := sbCert_sbWalk hbr hK (2 ^ (m + 1) - k0) k0
  have hw : walkAt m = sbWalk (k0 + j) := by
    unfold walkAt log2Walk
    have he : 2 ^ (m + 1) = k0 + (2 ^ (m + 1) - k0) := by omega
    rw [he, sbCert_add]
    change sbCert (2 ^ m) _ _ _ (sbCert (2 ^ m) _ _ k0 (sbWalk 0)) = _
    rw [hreach, Nat.zero_add, hj]
  rw [hw]
  have hs := (sbWalk_num (k0 + j)).2.2
  unfold sbBig
  by_cases h : (sbWalk (k0 + j)).loNum ≤ (sbWalk (k0 + j)).hiNum
  · rw [ite_eq_left h]
    omega
  · rw [ite_eq_right h]
    omega

/-- The least m at which the larger numerator of the walk exceeds 2h. -/
def smoothM (n : ℕ) : ℕ :=
  Nat.find (p := fun m => 2 * smoothBound n < (sbBig (walkAt m)).1)
    (let ⟨m0, h⟩ := exists_lt_walkAt (2 * smoothBound n)
     ⟨m0, h m0 le_rfl⟩)

/-- The A003586 program with the fraction of the walk at m = `smoothM n`. -/
def smoothJIFind (n : ℕ) : ℕ × ℕ :=
  smoothJI (sbBig (walkAt (smoothM n))).1 (sbBig (walkAt (smoothM n))).2 n

/-- For every n ≥ 1 the program returns the exponents of the n-th 3-smooth number. -/
theorem latticeOrd_smoothJIFind {n : ℕ} (hn : 1 ≤ n) :
    latticeOrd 2 3 (2 ^ (smoothJIFind n).1 * 3 ^ (smoothJIFind n).2) + 1 = n := by
  have hP : 2 * smoothBound n < (sbBig (walkAt (smoothM n))).1 := by
    unfold smoothM
    exact Nat.find_spec (p := fun m => 2 * smoothBound n < (sbBig (walkAt m)).1) _
  have h2 : 2 ≤ (sbBig (walkAt (smoothM n))).1 := by
    have : 0 < smoothBound n := by
      unfold smoothBound
      rw [Nat.shiftLeft_eq]
      exact Nat.mul_pos (by decide) (Nat.two_pow_pos _)
    omega
  exact latticeOrd_smoothJI (recordFrac_walkAt h2) hn hP

set_option linter.hashCommand false in
#guard walkAt 12 = sbWalk 11

set_option linter.hashCommand false in
#guard smoothJIFind 4095 = (73, 25)

set_option linter.hashCommand false in
#guard smoothM 4095 = 15 && smoothM (10 ^ 100) = 339

end AcceleratedCollatz
