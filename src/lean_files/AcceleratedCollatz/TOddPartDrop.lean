-- SPDX-License-Identifier: MIT
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic

/-!
  B108, B110: the odd part at the drop. A class of Order n has drop values
  3^n i + c. As 3^n is odd, the drop value has exactly e trailing zeros on one
  class of i modulo 2^(e+1) (`exists_trailing_class`). And 2 has order 2 3^n
  modulo 3^(n+1) (`orderOf_two_zmod_three_pow`, from 4^(3^j) = 1 + 3^(j+1) u
  with 3 ∤ u, `four_pow_three_pow`): 2 is a primitive root modulo every power
  of 3, so o 2^e = 3^n i + c is solvable in e for every o coprime to 6.
-/

namespace AcceleratedCollatz

/-- 4^(3^j) = 1 + 3^(j+1) u with u not divisible by 3. -/
theorem four_pow_three_pow (j : ℕ) : ∃ u, u % 3 ≠ 0 ∧ 4 ^ 3 ^ j = 1 + 3 ^ (j + 1) * u := by
  induction j with
  | zero => exact ⟨1, by norm_num, by norm_num⟩
  | succ j ih =>
    obtain ⟨u, hu, h⟩ := ih
    refine ⟨u + 3 ^ (j + 1) * u ^ 2 + 3 ^ (2 * j + 1) * u ^ 3, ?_, ?_⟩
    · have h1 : 3 ^ (j + 1) * u ^ 2 % 3 = 0 :=
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _)
      have h2 : 3 ^ (2 * j + 1) * u ^ 3 % 3 = 0 :=
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _)
      omega
    · rw [pow_succ, pow_mul, h]
      ring

theorem two_pow_odd_ne_one_mod_three_pow (n : ℕ) (k : ℕ) (hk : k % 2 = 1) :
    2 ^ k % 3 ^ (n + 1) ≠ 1 % 3 ^ (n + 1) := by
  intro h
  have h3 : 2 ^ k % 3 = 1 % 3 := by
    have := congrArg (· % 3) h
    simp only [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (Nat.succ_ne_zero n))] at this
    exact this
  obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t + 1 := ⟨k / 2, by omega⟩
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at h3
  norm_num at h3

theorem two_pow_eq_one_iff (n k : ℕ) :
    (2 : ZMod (3 ^ (n + 1))) ^ k = 1 ↔ 2 ^ k % 3 ^ (n + 1) = 1 % 3 ^ (n + 1) := by
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast
  rfl

/-- 2 is a primitive root modulo 3^(n+1): its order is 2 3^n. -/
theorem orderOf_two_zmod_three_pow (n : ℕ) :
    orderOf (2 : ZMod (3 ^ (n + 1))) = 2 * 3 ^ n := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by positivity)
  · rw [two_pow_eq_one_iff]
    obtain ⟨u, -, h⟩ := four_pow_three_pow n
    rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, h]
    simp [Nat.add_mod]
  · intro p hp hpn
    rcases (Nat.Prime.dvd_mul hp).mp hpn with h2 | h3
    · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      subst this
      rw [show 2 * 3 ^ n / 2 = 3 ^ n by omega, Ne, two_pow_eq_one_iff]
      exact two_pow_odd_ne_one_mod_three_pow n _ (Nat.odd_iff.mp (Odd.pow (by decide)))
    · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h3)
      subst this
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        rcases n with _ | m
        · simp at h3
        · exact ⟨m, rfl⟩
      rw [show 2 * 3 ^ (m + 1) / 3 = 2 * 3 ^ m by rw [pow_succ]; omega, Ne,
        two_pow_eq_one_iff]
      obtain ⟨u, hu, h⟩ := four_pow_three_pow m
      rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, h]
      intro hmod
      have hd : 3 ^ (m + 1 + 1) ∣ 3 ^ (m + 1) * u := by
        have := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
        simpa [Nat.add_sub_cancel_left] using this
      rw [pow_succ] at hd
      have := Nat.dvd_of_mul_dvd_mul_left (by positivity) hd
      omega

/-- For odd a, a i + c has exactly e trailing zeros on one class of i mod 2^(e+1). -/
theorem exists_trailing_class (a c e : ℕ) (ha : a % 2 = 1) :
    ∃ i0 < 2 ^ (e + 1), ∀ i,
      (2 ^ e ∣ a * i + c ∧ ¬ 2 ^ (e + 1) ∣ a * i + c) ↔ i % 2 ^ (e + 1) = i0 := by
  have hcop : Nat.Coprime a (2 ^ (e + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr ha)))
  set q := 2 ^ (e + 1) with hq
  have hq0 : 0 < q := by positivity
  have : NeZero q := ⟨hq0.ne'⟩
  let u := ZMod.unitOfCoprime a hcop
  let z : ZMod q := (u⁻¹ : (ZMod q)ˣ) * ((2 ^ e : ℕ) - (c : ZMod q))
  refine ⟨z.val, ZMod.val_lt z, fun i => ?_⟩
  have key : (2 ^ e ∣ a * i + c ∧ ¬ 2 ^ (e + 1) ∣ a * i + c) ↔
      (a * i + c) % q = 2 ^ e := by
    rw [hq, pow_succ]
    constructor
    · rintro ⟨⟨t, ht⟩, hn⟩
      rw [ht] at hn ⊢
      have : t % 2 = 1 := by
        by_contra h0
        exact hn (Nat.mul_dvd_mul_left _ (Nat.dvd_of_mod_eq_zero (by omega)))
      rw [Nat.mul_mod_mul_left, this, mul_one]
    · intro h
      have h1 := Nat.div_add_mod (a * i + c) (2 ^ e * 2)
      rw [h] at h1
      refine ⟨⟨2 * ((a * i + c) / (2 ^ e * 2)) + 1, by linarith⟩, ?_⟩
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      rw [h] at this
      exact absurd this (by positivity)
  rw [key]
  have hval : ∀ x : ℕ, x % q = (x : ZMod q).val := fun x => (ZMod.val_natCast (n := q) x).symm
  have h2e : 2 ^ e < q := by rw [hq, pow_succ]; omega
  constructor
  · intro h
    have hz : ((a * i + c : ℕ) : ZMod q) = ((2 ^ e : ℕ) : ZMod q) := by
      rw [ZMod.natCast_eq_natCast_iff', h, Nat.mod_eq_of_lt h2e]
    have : (i : ZMod q) = z := by
      push_cast at hz
      have hu : (u : ZMod q) = a := ZMod.coe_unitOfCoprime a hcop
      simp only [z]
      push_cast
      rw [← hu] at hz
      have : (u : ZMod q) * i = (2 ^ e : ZMod q) - c := by rw [← hz]; ring
      rw [← this, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hval, this]
  · intro h
    have hi : (i : ZMod q) = z := by
      rw [← ZMod.natCast_zmod_val z, ZMod.natCast_eq_natCast_iff', ← h,
        Nat.mod_mod_of_dvd _ dvd_rfl]
    have hu : (u : ZMod q) = a := ZMod.coe_unitOfCoprime a hcop
    have : ((a * i + c : ℕ) : ZMod q) = ((2 ^ e : ℕ) : ZMod q) := by
      push_cast
      rw [hi, ← hu]
      simp only [z]
      rw [← mul_assoc, Units.mul_inv, one_mul]
      push_cast
      ring
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h2e] at this
    exact this

theorem coprime_three_pow (n c : ℕ) (hc : c % 3 ≠ 0) : Nat.Coprime c (3 ^ (n + 1)) :=
  Nat.Coprime.pow_right _ (Nat.coprime_comm.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (fun h => hc (Nat.mod_eq_zero_of_dvd h))))

/-- 2 generates the units modulo 3^(n+1). -/
theorem exists_two_pow_eq_unit (n : ℕ) (x : (ZMod (3 ^ (n + 1)))ˣ) :
    ∃ k : ℕ, (ZMod.unitOfCoprime 2 (coprime_three_pow n 2 (by norm_num))) ^ k = x := by
  set g := ZMod.unitOfCoprime 2 (coprime_three_pow n 2 (by norm_num))
  have hord : orderOf g = 2 * 3 ^ n := by
    rw [← orderOf_units]
    have : ((g : (ZMod (3 ^ (n + 1)))ˣ) : ZMod (3 ^ (n + 1))) = 2 := by
      simp [g, ZMod.coe_unitOfCoprime]
    rw [this, orderOf_two_zmod_three_pow]
  have hcard : Nat.card (ZMod (3 ^ (n + 1)))ˣ = 2 * 3 ^ n := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ Nat.prime_three]
    ring
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
  have hx : x ∈ Submonoid.powers g :=
    mem_powers_iff_mem_zpowers.mpr (htop ▸ Subgroup.mem_top x)
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, hk⟩

/-- B110: for c and o coprime to 3 (c the constant of a drop value 3^(n+1) i + c,
  o an odd part), o 2^e = 3^(n+1) i + c has solutions with e as large as wanted. -/
theorem exists_odd_part_at_drop (n c o N : ℕ) (hc : c % 3 ≠ 0) (ho : o % 3 ≠ 0) :
    ∃ e ≥ N, ∃ i, o * 2 ^ e = 3 ^ (n + 1) * i + c := by
  set q := 3 ^ (n + 1)
  set g := ZMod.unitOfCoprime 2 (coprime_three_pow n 2 (by norm_num))
  set uc := ZMod.unitOfCoprime c (coprime_three_pow n c hc)
  set uo := ZMod.unitOfCoprime o (coprime_three_pow n o ho)
  obtain ⟨k, hk⟩ := exists_two_pow_eq_unit n (uc * uo⁻¹)
  have hord : orderOf g = 2 * 3 ^ n := by
    rw [← orderOf_units]
    have : ((g : (ZMod q)ˣ) : ZMod q) = 2 := by simp [g, ZMod.coe_unitOfCoprime]
    rw [this, orderOf_two_zmod_three_pow]
  set e := k + (N + c) * (2 * 3 ^ n)
  have h3 : 1 ≤ 3 ^ n := Nat.one_le_pow n 3 (by norm_num)
  have he : e = k + orderOf g * (N + c) := by rw [hord]; simp only [e]; ring
  have hge : g ^ e = g ^ k := by
    rw [he, pow_add g, pow_mul g, pow_orderOf_eq_one, one_pow, mul_one]
  have hz : ((o * 2 ^ e : ℕ) : ZMod q) = ((c : ℕ) : ZMod q) := by
    have h1 : g ^ e * uo = uc := by rw [hge, hk, inv_mul_cancel_right]
    have h2 := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) h1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, g, uo, uc,
      ZMod.coe_unitOfCoprime] at h2
    push_cast at h2 ⊢
    rw [← h2]
    ring
  have hce : c ≤ o * 2 ^ e := by
    have hc1 : c ≤ e := by simp only [e]; nlinarith
    have h1 : c < 2 ^ e := lt_of_le_of_lt hc1 Nat.lt_two_pow_self
    have ho1 : 1 ≤ o := by omega
    nlinarith
  have hNe : N ≤ e := by simp only [e]; nlinarith
  refine ⟨e, hNe, (o * 2 ^ e - c) / q, ?_⟩
  rw [ZMod.natCast_eq_natCast_iff'] at hz
  have hd : q ∣ o * 2 ^ e - c := (Nat.modEq_iff_dvd' hce).mp hz.symm
  rw [Nat.mul_div_cancel' hd]
  omega

end AcceleratedCollatz
