-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TPrefixBlock
import AcceleratedCollatz.TFiniteCheck

/-!
  E at the first block for the family B = 1^n 0^m (`oneRun n m`; A17, 1 Nov 2026), with
  3^n < 2^(n+m). With c = c(1B): c + 1 = 2^(n+1) k and 3 d k + 1 = 2^m j for a positive
  integer j. If j >= 2 then c d > rho; if j = 1 then T(c) d = rho, so T(c) is an integer
  fixed point of T^(n+m) with word B (`prefixBlockBound_oneRun_or`). So E can fail on the
  family only at an integer cycle with word B, which the drop of B's class excludes
  (`prefixBlockBound_oneRun_of_classDrop`), and so does the range check for every Order
  up to 10781273 (`prefixBlockBound_oneRun_le_10781273`).
-/

namespace AcceleratedCollatz

/-- The word 1^n 0^m. -/
def oneRun (n m : ℕ) : List Bool := List.replicate n true ++ List.replicate m false

theorem length_oneRun (n m : ℕ) : (oneRun n m).length = n + m := by
  simp [oneRun]

theorem order_oneRun (n m : ℕ) : order (oneRun n m) = n := by
  induction n with
  | zero =>
    induction m with
    | zero => simp [oneRun, order]
    | succ m ih =>
      simpa [oneRun, List.replicate_succ, order_cons] using ih
  | succ n ih =>
    simpa [oneRun, List.replicate_succ, order_cons] using ih

/-- The scaled value of 1^n 0^m, without subtraction. -/
theorem affineNum_oneRun (n m j N : ℕ) :
    affineNum (oneRun n m) j N + 2 ^ j * 2 ^ n = 3 ^ n * N + 2 ^ j * 3 ^ n := by
  induction n generalizing j N with
  | zero =>
    have hz : ∀ (m j N : ℕ), affineNum (List.replicate m false) j N = N := by
      intro m
      induction m with
      | zero => intro j N; simp [affineNum]
      | succ m ih => intro j N; simp [List.replicate_succ, affineNum, ih]
    simp [oneRun, hz]
  | succ n ih =>
    have h := ih (j + 1) (3 * N + 2 ^ j)
    have hs : affineNum (oneRun (n + 1) m) j N
        = affineNum (oneRun n m) (j + 1) (3 * N + 2 ^ j) := by
      simp [oneRun, List.replicate_succ, affineNum]
    rw [hs]
    have e1 : 2 ^ (j + 1) * 2 ^ n = 2 ^ j * 2 ^ (n + 1) := by ring
    have e2 : 3 ^ n * (3 * N + 2 ^ j) + 2 ^ (j + 1) * 3 ^ n
        = 3 ^ (n + 1) * N + 2 ^ j * 3 ^ (n + 1) := by ring
    omega

/-- E on the family, or T(c(1B)) is the integer cycle point of B. -/
theorem prefixBlockBound_oneRun_or {n m : ℕ} (h : 3 ^ n < 2 ^ (n + m)) :
    PrefixBlockBound (oneRun n m) ∨
      d_23 (oneRun n m) * tStep (classId (true :: oneRun n m)) = rho (oneRun n m) := by
  set B := oneRun n m with hB
  set c := classId (true :: B) with hc
  have hL : B.length = n + m := length_oneRun n m
  have hO : order B = n := order_oneRun n m
  have hd : d_23 B = 2 ^ (n + m) - 3 ^ n := by simp only [d_23, hL, hO]
  obtain ⟨d, hdd⟩ : ∃ d, d = d_23 B := ⟨_, rfl⟩
  have hPM : 2 ^ n * 2 ^ m = 3 ^ n + d := by
    rw [← pow_add]; omega
  have hr0 : rho B + 2 ^ n = 3 ^ n := by
    have := affineNum_oneRun n m 0 0
    simpa [rho, hB] using this
  have hA : affineNum B 1 1 + 2 * 2 ^ n = 3 * 3 ^ n := by
    have := affineNum_oneRun n m 1 1
    simp only [pow_one, mul_one] at this
    rw [← hB] at this
    omega
  -- the divisibility of the word 1B
  have hdvd : 2 ^ (true :: B).length ∣ 3 ^ order (true :: B) * c + rho (true :: B) :=
    (tBits_eq_iff (true :: B) c).mp (tBits_classId (true :: B))
  have hrho1 : rho (true :: B) = affineNum B 1 1 := by simp [rho, affineNum]
  have hO1 : order (true :: B) = n + 1 := by rw [order_cons, hO]; simp
  rw [hrho1, hO1, List.length_cons, hL] at hdvd
  obtain ⟨z, hz⟩ := hdvd
  have hP0 : 0 < 2 ^ n := by positivity
  have hM0 : 0 < 2 ^ m := by positivity
  -- 2^(n+m+1) z + 2^(n+1) = 3^(n+1) (c + 1)
  have h1 : 2 * (2 ^ n * 2 ^ m) * z + 2 * 2 ^ n = 3 * 3 ^ n * (c + 1) := by
    have e : 2 ^ (n + m + 1) = 2 * (2 ^ n * 2 ^ m) := by ring
    have e' : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
    rw [e, e'] at hz
    linarith
  -- so 2^(n+1) divides c + 1
  have hdiv : 2 ^ (n + 1) ∣ c + 1 := by
    have h2 : 2 ^ (n + 1) ∣ 3 ^ (n + 1) * (c + 1) := by
      refine ⟨2 ^ m * z + 1, ?_⟩
      have e' : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
      have e'' : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [e', e'', ← h1]
      ring
    exact (Nat.Coprime.pow (n + 1) (n + 1) (by decide)).dvd_of_dvd_mul_left h2
  obtain ⟨k, hk⟩ := hdiv
  have hP2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [hP2] at hk
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · simp [h0] at hk
    · exact h0
  -- 2^m z + 1 = 3^(n+1) k
  have h2 : 2 ^ m * z + 1 = 3 * 3 ^ n * k := by
    have : 2 * 2 ^ n * (2 ^ m * z + 1) = 2 * 2 ^ n * (3 * 3 ^ n * k) := by
      rw [hk] at h1
      linarith
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  -- T(c) = 3 2^n k - 1
  have hy : tStep c + 1 = 3 * 2 ^ n * k := by
    have hodd : c % 2 = 1 := by
      have : c + 1 = 2 * (2 ^ n * k) := by rw [hk]; ring
      omega
    rw [tStep_odd _ hodd]
    have : 3 * c + 1 = 2 * (3 * 2 ^ n * k - 1) := by
      have h3 : 1 ≤ 3 * 2 ^ n * k := by
        have : 0 < 3 * 2 ^ n * k := by positivity
        omega
      have : 3 * (c + 1) = 2 * (3 * 2 ^ n * k) := by rw [hk]; ring
      omega
    have h3 : 1 ≤ 3 * 2 ^ n * k := by
      have : 0 < 3 * 2 ^ n * k := by positivity
      omega
    omega
  -- in integers: 3 d k + 1 = 2^m j
  obtain ⟨P, hPdef⟩ : ∃ P : ℤ, P = 2 ^ n := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℤ, M = 2 ^ m := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℤ, Q = 3 ^ n := ⟨_, rfl⟩
  have hPz : P * M = Q + (d : ℤ) := by
    rw [hPdef, hMdef, hQdef]; exact_mod_cast hPM
  have hrz : (rho B : ℤ) + P = Q := by
    rw [hPdef, hQdef]; exact_mod_cast hr0
  have hkz : (c : ℤ) + 1 = 2 * P * k := by
    rw [hPdef]; exact_mod_cast hk
  have h2z : M * z + 1 = 3 * Q * k := by
    rw [hMdef, hQdef]; exact_mod_cast h2
  have hyz : (tStep c : ℤ) + 1 = 3 * P * k := by
    rw [hPdef]; exact_mod_cast hy
  have hP0z : 0 < P := by rw [hPdef]; positivity
  have hM0z : 0 < M := by rw [hMdef]; positivity
  have hQ0z : 0 < Q := by rw [hQdef]; positivity
  have hd0z : (0 : ℤ) ≤ d := by positivity
  have hk0z : (0 : ℤ) < k := by exact_mod_cast hk0
  have hj : 3 * (d : ℤ) * k + 1 = M * (3 * P * k - z) := by
    have hQe : Q = P * M - d := by linarith
    rw [hQe] at h2z
    have e1 : M * (3 * P * k - z) = 3 * (P * M * k) - M * z := by ring
    have e2 : 3 * (P * M - d) * k = 3 * (P * M * k) - 3 * d * k := by ring
    rw [e1]
    rw [e2] at h2z
    linarith
  have hjpos : 0 < 3 * P * k - (z : ℤ) := by
    have h3 : 0 < M * (3 * P * k - z) := by rw [← hj]; positivity
    by_contra hn
    have hn' := not_lt.mp hn
    have h4 : M * (3 * P * k - z) ≤ M * 0 := mul_le_mul_of_nonneg_left hn' hM0z.le
    linarith
  rcases eq_or_lt_of_le (Int.add_one_le_iff.mpr hjpos) with hj1 | hj2
  · -- j = 1: the cycle
    right
    have hjj : 3 * P * k - (z : ℤ) = 1 := by linarith
    rw [hjj, mul_one] at hj
    rw [← hdd]
    have : (d : ℤ) * tStep c = rho B := by
      have e : (tStep c : ℤ) = 3 * P * k - 1 := by linarith
      rw [e]
      have : (d : ℤ) * (3 * P * k - 1) = P * (3 * d * k) - d := by ring
      rw [this]
      have : 3 * (d : ℤ) * k = M - 1 := by linarith
      rw [this]
      linarith
    exact_mod_cast this
  · -- j >= 2
    left
    rw [PrefixBlockBound, ← hdd]
    have hj2' : 2 ≤ 3 * P * k - (z : ℤ) := by linarith
    have hge : 2 * M ≤ 3 * (d : ℤ) * k + 1 := by
      rw [hj]
      have := mul_le_mul_of_nonneg_left hj2' hM0z.le
      linarith
    have hmul : P * (2 * M) ≤ P * (3 * (d : ℤ) * k + 1) :=
      mul_le_mul_of_nonneg_left hge hP0z.le
    have hgoal : (rho B : ℤ) < d * c := by
      have e : (c : ℤ) = 2 * P * k - 1 := by linarith
      rw [e]
      have e3 : P * (3 * (d : ℤ) * k + 1) = 3 * (P * d * k) + P := by ring
      have e4 : (d : ℤ) * (2 * P * k - 1) = 2 * (P * d * k) - d := by ring
      rw [e4]
      rw [e3] at hmul
      have e5 : P * (2 * M) = 2 * (P * M) := by ring
      rw [e5] at hmul
      linarith
    exact_mod_cast hgoal

/-- The drop of B's class gives E on the family: no integer cycle with word B. -/
theorem prefixBlockBound_oneRun_of_classDrop {n m : ℕ} (h : 3 ^ n < 2 ^ (n + m))
    (hdrop : rho (oneRun n m) < d_23 (oneRun n m) * classId (oneRun n m)) :
    PrefixBlockBound (oneRun n m) := by
  rcases prefixBlockBound_oneRun_or h with hE | hc
  · exact hE
  · exfalso
    have hb := tBits_classId (true :: oneRun n m)
    simp only [List.length_cons, tBits, List.cons.injEq] at hb
    have hc1 : classId (true :: oneRun n m) % 2 = 1 := by simpa using hb.1
    have hy0 : 0 < tStep (classId (true :: oneRun n m)) := by
      rw [tStep_odd _ hc1]; omega
    have hle := classId_le_of (oneRun n m) _ hy0 hb.2
    have := Nat.mul_le_mul_left (d_23 (oneRun n m)) hle
    omega

/-- E on the family for every Order up to 10781273, from the range check. -/
theorem prefixBlockBound_oneRun_le_10781273
    (hX : ∀ x, 1 < x → x ≤ 984572779224 → ∀ m, Admissible (tBits x m) → tStep^[m] x < x)
    {n m : ℕ} (hn : n ≤ 10781273) (hA : Admissible (oneRun n m))
    (h3 : 3 ^ n < 2 ^ (n + m)) (h1 : 1 < classId (oneRun n m)) :
    PrefixBlockBound (oneRun n m) :=
  prefixBlockBound_oneRun_of_classDrop h3
    (classDropsAt_le_10781273 hX n hn _ hA (order_oneRun n m) h1)

end AcceleratedCollatz
