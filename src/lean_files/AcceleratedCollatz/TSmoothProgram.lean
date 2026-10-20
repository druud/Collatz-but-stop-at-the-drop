-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBisect
import AcceleratedCollatz.TRecordWalk
import AcceleratedCollatz.TSmoothRank

/-!
  The A003586 program in integers (`smoothJI`): the exponents (j, i) of the n-th 3-smooth
  number 2^j 3^i, from a record fraction P/Q (`RecordFrac`) with P > 2h,
  h = 4 · 2^⌊log2(n)/2⌋. The PARI program takes P/Q from `bestappr` (`conv_log`: a convergent
  of log 3 / log 2, so a record fraction; it errors out when P ≤ 2h) or from the integer
  Stern-Brocot walk (`conv_rat`, TSternBrocotCert). Its steps:
  S(k) = k + floorsum(k + 1, P, Q, 0) counts the 3-smooth numbers below 2^k (`smoothCount_eq`,
  with `div_record_swap_add_one`); a bisection gives the number B of binary digits; N, the
  number of 3-smooth numbers of B digits, is S(B) - S(B - 1); the walk gives the last
  record Orders u, v below N (`recordWalk_spec`); a second bisection over
  g(k) = k + floorsum(k, u + v, u, 0) - floorsum(k, u + v, u, u + v - N) (`classCount_eq`)
  gives the least K with r ≤ g(K), and i = (K - 1) u mod (u + v); and
  j = B - 1 - ⌊i P/Q⌋ = B - p2(i) (`div_record_add_one`).
  `smoothJI_spec`: exactly n - 1 of the 3-smooth numbers lie below 2^j 3^i, so 2^j 3^i is
  the n-th one (`latticeOrd_smoothJI`).
-/

namespace AcceleratedCollatz

open Finset

/-- S(k) = k + fs(k + 1, P, Q, 0). -/
def smoothCount (P Q k : ℕ) : ℕ := k + floorSum (k + 1) P Q 0

/-- The bound h = 4 · 2^⌊log2(n)/2⌋ of the first bisection. -/
def smoothBound (n : ℕ) : ℕ := 4 <<< (Nat.log 2 n / 2)

/-- The number of binary digits of the n-th 3-smooth number: the first bisection. -/
def smoothDigits (P Q n : ℕ) : ℕ := bisect (smoothCount P Q) n 0 (smoothBound n)

/-- The exponent i of the r-th 3-smooth number of a class of N > 1: the walk and the
    second bisection. -/
def smoothClassIndex (P Q N r : ℕ) : ℕ :=
  let w := recordWalk N 1 1 (P - Q) (2 * Q - P)
  (bisect (classCount (w.1 + w.2) w.1 N) r (r - 1) (w.1 + w.2) - 1) * w.1 % (w.1 + w.2)

/-- The exponents (j, i) of the n-th 3-smooth number 2^j 3^i, as in the PARI program. -/
def smoothJI (P Q n : ℕ) : ℕ × ℕ :=
  let B := smoothDigits P Q n
  let r := n - smoothCount P Q (B - 1)
  let N := smoothCount P Q B - smoothCount P Q (B - 1)
  let i := if 1 < N then smoothClassIndex P Q N r else 0
  (B - 1 - i * P / Q, i)

set_option linter.hashCommand false in
#guard smoothJI 485 306 4095 = (73, 25)

/-- For a record fraction P/Q and k < P, S(k) is the number of 3-smooth numbers below 2^k. -/
theorem smoothCount_eq {P Q k : ℕ} (hPQ : RecordFrac P Q) (hkP : k < P) :
    smoothCount P Q k = (smoothBelow k).card := by
  have hP : 0 < P := by omega
  rw [smoothCount, floorSum_eq hP, card_smoothBelow, sum_range_succ', sum_range_succ']
  have hterm : ∀ t ∈ range k, (Q * (t + 1) + 0) / P + 1 = Nat.clog 3 (2 ^ (t + 1)) := by
    intro t ht
    rw [mem_range] at ht
    rw [Nat.add_zero, Nat.mul_comm]
    exact div_record_swap_add_one hPQ (by omega) (by omega)
  rw [← sum_congr rfl hterm, sum_add_distrib, sum_const, card_range, Nat.nsmul_eq_mul,
    Nat.mul_one]
  simp only [Nat.zero_add, Nat.mul_zero, Nat.zero_div, pow_zero, Nat.clog_one_right]
  omega

/-- (t + 1)/2 ≤ the number of powers of 3 below 2^t. -/
theorem half_succ_le_clog (t : ℕ) : (t + 1) / 2 ≤ Nat.clog 3 (2 ^ t) := by
  rcases Nat.eq_zero_or_pos t with h0 | ht
  · subst h0
    simp
  · have hlt : 3 ^ ((t - 1) / 2) < 2 ^ t := by
      calc 3 ^ ((t - 1) / 2) ≤ 4 ^ ((t - 1) / 2) := Nat.pow_le_pow_left (by norm_num) _
        _ = 2 ^ (2 * ((t - 1) / 2)) := by
          rw [pow_mul]
          norm_num
        _ ≤ 2 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 2 ^ t := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlt
    omega

/-- ∑_{t ≤ 2m} (t + 1)/2 = m (m + 1). -/
theorem sum_half_succ (m : ℕ) : ∑ t ∈ range (2 * m + 1), (t + 1) / 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    rw [h2, sum_range_succ, sum_range_succ, ih]
    have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have e2 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
    rw [e1, e2]
    ring

/-- At least n 3-smooth numbers lie below 2^h, h = 4 · 2^⌊log2(n)/2⌋. -/
theorem le_card_smoothBelow_bound (n : ℕ) :
    n ≤ (smoothBelow (smoothBound n)).card := by
  set a := 2 ^ (Nat.log 2 n / 2) with ha
  have hh : smoothBound n = 2 * (2 * a) := by
    rw [smoothBound, Nat.shiftLeft_eq]
    ring
  rw [hh, card_smoothBelow]
  have hsum : (2 * a) * (2 * a + 1) ≤
      ∑ k ∈ range (2 * (2 * a) + 1), Nat.clog 3 (2 ^ k) := by
    rw [← sum_half_succ]
    exact sum_le_sum (fun t _ => half_succ_le_clog t)
  have hn2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have ha2 : 2 ^ (Nat.log 2 n + 1) ≤ (2 * a) * (2 * a) := by
    have : (2 * a) * (2 * a) = 2 ^ (2 * (Nat.log 2 n / 2) + 2) := by
      rw [pow_add, pow_mul', ← ha]
      ring
    rw [this]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : (2 * a) * (2 * a) ≤ (2 * a) * (2 * a + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- p2(Q) ≤ 2 Q for Q ≥ 1. -/
theorem p2_of_le_two_mul' {Q : ℕ} (hQ : 1 ≤ Q) : p2_of Q ≤ 2 * Q := by
  unfold p2_of
  have h34 : 3 ^ Q < 2 ^ (2 * Q) := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  have := Nat.log_lt_of_lt_pow (b := 2) (by positivity) h34
  omega

/-- The program's result: exactly n - 1 of the 3-smooth numbers lie below 2^j 3^i, for a
    record fraction P/Q with P > 2h. -/
theorem smoothJI_spec {P Q n : ℕ} (hPQ : RecordFrac P Q) (hn : 1 ≤ n)
    (hP : 2 * smoothBound n < P) :
    (smoothBelowAt (smoothJI P Q n).1 (smoothJI P Q n).2).card + 1 = n := by
  have hbP := recordFrac_bounds hPQ
  have hQ2 := p2_of_le_two_mul' hPQ.1
  have hhQ : smoothBound n < Q := by omega
  have hh0 : 0 < smoothBound n := by
    rw [smoothBound, Nat.shiftLeft_eq]
    positivity
  have hS : ∀ k, k ≤ smoothBound n → smoothCount P Q k = (smoothBelow k).card :=
    fun k hk => smoothCount_eq hPQ (by omega)
  have hS0 : smoothCount P Q 0 = 0 := by
    rw [hS 0 (Nat.zero_le _), card_smoothBelow]
    simp
  have hSh : n ≤ smoothCount P Q (smoothBound n) := by
    rw [hS _ le_rfl]
    exact le_card_smoothBelow_bound n
  obtain ⟨hB0, hBh, hnB, hB1⟩ :=
    bisect_spec (smoothCount P Q) n 0 (smoothBound n) hh0 (by omega) hSh
  set B := smoothDigits P Q n with hBdef
  change 0 < B at hB0
  change B ≤ smoothBound n at hBh
  change n ≤ smoothCount P Q B at hnB
  change smoothCount P Q (B - 1) < n at hB1
  have hBsucc : B - 1 + 1 = B := by omega
  have hNeq : smoothCount P Q B - smoothCount P Q (B - 1) = Nat.clog 3 (2 ^ B) := by
    rw [hS B hBh, hS (B - 1) (by omega), card_smoothBelow, card_smoothBelow, hBsucc,
      sum_range_succ]
    omega
  set N := Nat.clog 3 (2 ^ B) with hN
  set r := n - smoothCount P Q (B - 1) with hr
  have hr1 : 1 ≤ r := by omega
  have hrN : r ≤ N := by omega
  have hNB : N ≤ B := Nat.clog_le_of_le_pow (Nat.pow_le_pow_left (by norm_num) B)
  have hcard : (smoothBelow (B - 1)).card = smoothCount P Q (B - 1) := (hS (B - 1) (by omega)).symm
  -- the class index and its count of smaller block factors
  have key : ∀ i, i < N → ((range N).filter (fun i' => blockFactor i' < blockFactor i)).card =
      r - 1 → (smoothBelowAt (B - 1 - i * P / Q) i).card + 1 = n := by
    intro i hiN hcnt
    have hpi : p2_of i ≤ B := (p2_of_le_iff_lt_clog i B).mpr hiN
    have hj : B - 1 - i * P / Q = B - p2_of i := by
      rcases Nat.eq_zero_or_pos i with h0 | hi1
      · subst h0
        have : p2_of 0 = 1 := by
          unfold p2_of
          simp
        rw [this, Nat.zero_mul, Nat.zero_div, Nat.sub_zero]
      · have := div_record_add_one hPQ hi1 (by omega)
        omega
    rw [hj, card_smoothBelowAt_class (by omega) hpi, ← hN, hcnt, hcard]
    omega
  change (smoothBelowAt (B - 1 - (if 1 < smoothCount P Q B - smoothCount P Q (B - 1) then
      smoothClassIndex P Q (smoothCount P Q B - smoothCount P Q (B - 1)) r else 0) * P / Q)
      (if 1 < smoothCount P Q B - smoothCount P Q (B - 1) then
      smoothClassIndex P Q (smoothCount P Q B - smoothCount P Q (B - 1)) r else 0)).card + 1 = n
  rw [hNeq]
  by_cases hN1 : 1 < N
  · simp only [hN1, ↓reduceIte]
    -- the walk
    have h11 : LastRecords 1 1 (1 + 1) := lastRecords_two
    have hp1 : p2_of 1 = 2 := p2_of_one
    have hd1 : P - Q = 1 * P - (p2_of 1 - 1) * Q := by
      rw [hp1]
      omega
    have he1 : 2 * Q - P = p2_of 1 * Q - 1 * P := by
      rw [hp1]
      omega
    have hW := recordWalk_spec hPQ (by omega) 1 1 (P - Q) (2 * Q - P) h11 hN1 hN1 hd1 he1
    set u := (recordWalk N 1 1 (P - Q) (2 * Q - P)).1 with hu
    set v := (recordWalk N 1 1 (P - Q) (2 * Q - P)).2 with hv
    have hNM : N ≤ u + v := le_add_of_lastRecords hW
    have hM0 : 0 < u + v := by omega
    have hcc : ∀ k, classCount (u + v) u N k =
        ((range k).filter (fun k' => k' * u % (u + v) < N)).card :=
      classCount_eq hM0 hNM
    have hlo : classCount (u + v) u N (r - 1) < r := by
      rw [hcc]
      have := card_filter_le (range (r - 1)) (fun k' => k' * u % (u + v) < N)
      rw [card_range] at this
      omega
    have hhi : r ≤ classCount (u + v) u N (u + v) := by
      rw [hcc, card_mul_mod_lt hW hNM]
      exact hrN
    obtain ⟨hk0, hkM, hkr, hkr1⟩ :=
      bisect_spec (classCount (u + v) u N) r (r - 1) (u + v) (by omega) hlo hhi
    set K := bisect (classCount (u + v) u N) r (r - 1) (u + v) with hK
    have hKs : K - 1 + 1 = K := by omega
    rw [hcc] at hkr hkr1
    rw [← hKs, range_add_one, filter_insert] at hkr
    have hmem : K - 1 ∉ (range (K - 1)).filter (fun k' => k' * u % (u + v) < N) := by
      simp
    have hiN : (K - 1) * u % (u + v) < N := by
      by_contra hc
      simp only [hc, ↓reduceIte] at hkr
      omega
    simp only [hiN, ↓reduceIte] at hkr
    rw [card_insert_of_notMem hmem] at hkr
    have hcnt : ((range (K - 1)).filter (fun k' => k' * u % (u + v) < N)).card = r - 1 := by
      omega
    change (smoothBelowAt (B - 1 - (K - 1) * u % (u + v) * P / Q)
      ((K - 1) * u % (u + v))).card + 1 = n
    apply key _ hiN
    rw [card_blockFactor_lt_eq hW hNM (by omega), hcnt]
  · simp only [hN1, ↓reduceIte]
    have hN0 : 1 ≤ N := by omega
    apply key 0 (by omega)
    have : (range N).filter (fun i' => blockFactor i' < blockFactor 0) = ∅ := by
      rw [filter_eq_empty_iff]
      intro x hx
      rw [mem_range] at hx
      have : x = 0 := by omega
      rw [this]
      exact lt_irrefl _
    rw [this, card_empty]
    omega

/-- The program's result 2^j 3^i is the n-th 3-smooth number: its place, counted from 0,
    is n - 1. -/
theorem latticeOrd_smoothJI {P Q n : ℕ} (hPQ : RecordFrac P Q) (hn : 1 ≤ n)
    (hP : 2 * smoothBound n < P) :
    latticeOrd 2 3 (2 ^ (smoothJI P Q n).1 * 3 ^ (smoothJI P Q n).2) + 1 = n := by
  rw [latticeOrd_two_three]
  exact smoothJI_spec hPQ hn hP

end AcceleratedCollatz
