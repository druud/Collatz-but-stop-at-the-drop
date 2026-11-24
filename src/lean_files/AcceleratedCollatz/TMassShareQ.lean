-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCycleCountQ

/-!
  The shares of the mass identity (C107 (d)), for odd q ≥ 3 and any p in a field: the algebra
  behind the rate of the drop zeta draft (Theorem 5.10, M. Winkler). With L = p2Q q n,
  N(m) = |admSetQ q m| and

    P_n(m) = N(m) C(L - p2(m), n - m)/C(L, n),
    w(m) = N(m) p^m (1 - p)^(p2(m) - m),   Q(j) = C(p2(j), j) p^j (1 - p)^(p2(j) - j),

  * 1 - L N(n)/C(L, n) = Σ_{m split} P_n(m) (`one_sub_mass_eq_sum_shareQ`),
  * P_n(m) = w(m) Q(n - m)/Q(n) for every split Order m, p ≠ 0, 1 (`shareQ_eq`),
  * p2(m) w(m) ≤ Q(m) for 0 ≤ p ≤ 1 (`p2Q_mul_wQ_le`).

  The identities hold for every p ≠ 0, 1; the paper takes p = 1/log2 q.
-/

namespace AcceleratedCollatz

variable {q : ℕ} {K : Type*}

/-- An admissible word of Order j is longer than j. -/
theorem lt_p2Q (hq : 3 ≤ q) (j : ℕ) : j < p2Q q j :=
  (Nat.pow_lt_pow_iff_right (by norm_num)).mp
    (lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) j) (p2Q_spec hq j))

/-- P_n(m) = N(m) C(L - p2(m), n - m)/C(L, n). -/
def shareQ [Field K] (q n m : ℕ) : K :=
  ((admSetQ q m).card * (p2Q q n - p2Q q m).choose (n - m) : ℕ) / ((p2Q q n).choose n : ℕ)

/-- w(m) = N(m) p^m (1 - p)^(p2(m) - m). -/
def wQ [Field K] (q : ℕ) (p : K) (m : ℕ) : K :=
  ((admSetQ q m).card : K) * p ^ m * (1 - p) ^ (p2Q q m - m)

/-- Q(j) = C(p2(j), j) p^j (1 - p)^(p2(j) - j). -/
def QQ [Field K] (q : ℕ) (p : K) (j : ℕ) : K :=
  ((p2Q q j).choose j : K) * p ^ j * (1 - p) ^ (p2Q q j - j)

/-- 1 - L N(n)/C(L, n) is the sum of the shares of the split Orders. -/
theorem one_sub_mass_eq_sum_shareQ [Field K] [CharZero K] (hodd : Odd q) (hq : 3 ≤ q)
    (n : ℕ) :
    1 - ((p2Q q n * (admSetQ q n).card : ℕ) : K) / ((p2Q q n).choose n : ℕ) =
      ∑ m ∈ splitOrdersQ q n, (shareQ q n m : K) := by
  have hC : (((p2Q q n).choose n : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.choose_pos (lt_p2Q hq n).le).ne'
  have h := choose_p2Q_eq_split hodd hq n
  have hsum : ∑ m ∈ splitOrdersQ q n, (shareQ q n m : K) =
      ((∑ m ∈ splitOrdersQ q n, (admSetQ q m).card * (p2Q q (n - m)).choose (n - m) : ℕ) : K) /
        ((p2Q q n).choose n : ℕ) := by
    rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' := (Finset.mem_filter.1 hm).2
    rw [shareQ, show p2Q q n - p2Q q m = p2Q q (n - m) by omega, div_eq_mul_inv]
  rw [hsum, eq_div_iff hC, sub_mul, one_mul, div_mul_cancel₀ _ hC, sub_eq_iff_eq_add,
    ← Nat.cast_add]
  exact congrArg _ (h.trans (add_comm _ _))

/-- The product form of `shareQ_eq`: Q(n) N(m) C(p2(n - m), n - m) = w(m) Q(n - m) C(L, n). -/
theorem QQ_mul_eq [Field K] (hq : 3 ≤ q) (p : K) {n m : ℕ} (hm : m ∈ splitOrdersQ q n) :
    QQ q p n * ((admSetQ q m).card * (p2Q q (n - m)).choose (n - m) : ℕ) =
      wQ q p m * QQ q p (n - m) * ((p2Q q n).choose n : ℕ) := by
  simp only [splitOrdersQ, Finset.mem_filter, Finset.mem_Ico] at hm
  have h1 := lt_p2Q hq m
  have h2 := lt_p2Q hq (n - m)
  have hp : p ^ n = p ^ m * p ^ (n - m) := by rw [← pow_add]; congr 1; omega
  have hr : (1 - p) ^ (p2Q q n - n) =
      (1 - p) ^ (p2Q q m - m) * (1 - p) ^ (p2Q q (n - m) - (n - m)) := by
    rw [← pow_add]; congr 1; omega
  simp only [QQ, wQ, hp, hr]
  push_cast
  ring

/-- P_n(m) = w(m) Q(n - m)/Q(n) for every split Order m (p ≠ 0, 1). -/
theorem shareQ_eq [Field K] [CharZero K] (hq : 3 ≤ q) {p : K} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    {n m : ℕ} (hm : m ∈ splitOrdersQ q n) :
    (shareQ q n m : K) = wQ q p m * QQ q p (n - m) / QQ q p n := by
  have hC : (((p2Q q n).choose n : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.choose_pos (lt_p2Q hq n).le).ne'
  have hQ : QQ q p n ≠ 0 := by
    unfold QQ
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hp0)) (pow_ne_zero _ (sub_ne_zero.2 hp1.symm))
    exact_mod_cast hC
  have hm' := (Finset.mem_filter.1 hm).2
  rw [shareQ, show p2Q q n - p2Q q m = p2Q q (n - m) by omega, div_eq_div_iff hC hQ, mul_comm,
    QQ_mul_eq hq p hm]

/-- p2(m) w(m) ≤ Q(m) for 0 ≤ p ≤ 1, from p2(m) N(m) ≤ C(p2(m), m). -/
theorem p2Q_mul_wQ_le [Field K] [LinearOrder K] [IsStrictOrderedRing K] (hodd : Odd q)
    (hq : 3 ≤ q) {p : K} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    (p2Q q m : K) * wQ q p m ≤ QQ q p m := by
  have hN : p2Q q m * (admSetQ q m).card ≤ (p2Q q m).choose m := by
    rw [choose_p2Q_eq_split hodd hq m]; exact Nat.le_add_right _ _
  have hNK : (p2Q q m : K) * (admSetQ q m).card ≤ ((p2Q q m).choose m : K) := by
    exact_mod_cast hN
  have hpos : 0 ≤ p ^ m * (1 - p) ^ (p2Q q m - m) :=
    mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  have := mul_le_mul_of_nonneg_right hNK hpos
  unfold wQ QQ
  calc (p2Q q m : K) * ((admSetQ q m).card * p ^ m * (1 - p) ^ (p2Q q m - m))
      = (p2Q q m : K) * (admSetQ q m).card * (p ^ m * (1 - p) ^ (p2Q q m - m)) := by ring
    _ ≤ ((p2Q q m).choose m : K) * (p ^ m * (1 - p) ^ (p2Q q m - m)) := this
    _ = ((p2Q q m).choose m : K) * p ^ m * (1 - p) ^ (p2Q q m - m) := by ring

end AcceleratedCollatz
