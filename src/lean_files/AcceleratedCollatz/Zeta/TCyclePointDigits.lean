-- SPDX-License-Identifier: MIT
import Mathlib

/-!
  The cycle point read off its binary digits (C159, C163; zeta paper, Section "The cycle point").

  For an odd `d > 0` the binary (2-adic) digits of the rational `a/d` come from the state map
  `digitStep d a = (a - (a % 2) d)/2`: the digit is `a % 2`, and
  `a/d = digit + 2 (digitStep d a)/d`.
  The expansion is purely periodic from a state `a` exactly when `-d ≤ a ≤ 0`
  (`periodic_iff`), that is when `a/d` lies in `[-1, 0]`.

  For a word of length `L` with class id `c` (`0 ≤ c < 2^L`), cycle numerator `ρ ≥ 0`,
  `d = 2^L - 3^n` and end value `t` (`2^L t = 3^n c + ρ`, that is `ρ = 2^L (t - c) + d c`), the
  state after `L` digits of `x* = ρ/d` is `t - c` (`iterate_eq_sub`), and so

    the digits of x* past the first L are purely periodic  ↔  t ≤ c   (`tail_periodic_iff`),

  `t < c` the drop at the end of the word, `t = c` only at a cycle (`x* = c`, the bottom 1).
-/

namespace AcceleratedCollatz

/-- One step of the binary expansion of `a/d`: drop the digit `a % 2`. -/
def digitStep (d a : ℤ) : ℤ := (a - (a % 2) * d) / 2

theorem two_mul_digitStep {d : ℤ} (hd : Odd d) (a : ℤ) :
    2 * digitStep d a + (a % 2) * d = a := by
  obtain ⟨k, rfl⟩ := hd
  unfold digitStep
  rcases Int.emod_two_eq_zero_or_one a with h | h
  · rw [h]; omega
  · rw [h]; omega

theorem digitStep_lt {d : ℤ} (hd : Odd d) (hd0 : 0 < d) {a b : ℤ} (ha : 0 < a) (hb : b < a) :
    digitStep d b < a := by
  have h := two_mul_digitStep hd b
  rcases Int.emod_two_eq_zero_or_one b with h2 | h2 <;> rw [h2] at h <;> omega

theorem lt_digitStep {d : ℤ} (hd : Odd d) (hd0 : 0 < d) {a b : ℤ} (ha : a < -d) (hb : a < b) :
    a < digitStep d b := by
  have h := two_mul_digitStep hd b
  rcases Int.emod_two_eq_zero_or_one b with h2 | h2 <;> rw [h2] at h <;> omega

theorem lt_digitStep_self {d : ℤ} (hd : Odd d) (hd0 : 0 < d) {a : ℤ} (ha : a < -d) :
    a < digitStep d a := by
  have h := two_mul_digitStep hd a
  rcases Int.emod_two_eq_zero_or_one a with h2 | h2 <;> rw [h2] at h <;> omega

theorem digitStep_lt_self {d : ℤ} (hd : Odd d) (hd0 : 0 < d) {a : ℤ} (ha : 0 < a) :
    digitStep d a < a := by
  have h := two_mul_digitStep hd a
  rcases Int.emod_two_eq_zero_or_one a with h2 | h2 <;> rw [h2] at h <;> omega

theorem digitStep_mem {d : ℤ} (hd : Odd d) {a : ℤ} (h1 : -d ≤ a) (h2 : a ≤ 0) :
    -d ≤ digitStep d a ∧ digitStep d a ≤ 0 := by
  have h := two_mul_digitStep hd a
  rcases Int.emod_two_eq_zero_or_one a with h3 | h3 <;> rw [h3] at h <;> omega

theorem digitStep_injOn {d : ℤ} (hd : Odd d) {a b : ℤ} (ha1 : -d ≤ a) (ha2 : a ≤ 0)
    (hb1 : -d ≤ b) (hb2 : b ≤ 0) (h : digitStep d a = digitStep d b) : a = b := by
  have h1 := two_mul_digitStep hd a
  have h2 := two_mul_digitStep hd b
  obtain ⟨k, hk⟩ := hd
  rcases Int.emod_two_eq_zero_or_one a with h3 | h3 <;>
    rcases Int.emod_two_eq_zero_or_one b with h4 | h4 <;>
    rw [h3] at h1 <;> rw [h4] at h2 <;> omega

/-- The expansion is purely periodic from the state `a` iff `-d ≤ a ≤ 0`. -/
theorem periodic_iff {d : ℤ} (hd : Odd d) (hd0 : 0 < d) (a : ℤ) :
    (∃ k, 0 < k ∧ (digitStep d)^[k] a = a) ↔ (-d ≤ a ∧ a ≤ 0) := by
  constructor
  · rintro ⟨k, hk, hka⟩
    by_contra hn
    rcases not_and_or.mp hn with h | h
    · -- below -d: the states rise above a and stay there
      have key : ∀ j, a < (digitStep d)^[j + 1] a := by
        intro j
        induction j with
        | zero => exact lt_digitStep_self hd hd0 (by omega)
        | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact lt_digitStep hd hd0 (by omega) ih
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have := key j; omega
    · -- above 0: the states fall below a and stay there
      have key : ∀ j, (digitStep d)^[j + 1] a < a := by
        intro j
        induction j with
        | zero => exact digitStep_lt_self hd hd0 (by omega)
        | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact digitStep_lt hd hd0 (by omega) ih
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have := key j; omega
  · rintro ⟨h1, h2⟩
    -- the step permutes the finite set [-d, 0]
    let S := {x : ℤ // -d ≤ x ∧ x ≤ 0}
    have : Finite S := (Set.finite_Icc (-d) 0).to_subtype
    let g : S → S := fun x => ⟨digitStep d x.1, digitStep_mem hd x.2.1 x.2.2⟩
    have hg : Function.Injective g := fun x y hxy =>
      Subtype.ext (digitStep_injOn hd x.2.1 x.2.2 y.2.1 y.2.2 (congrArg Subtype.val hxy))
    have hgi : ∀ j (x : S), ((g^[j]) x).1 = (digitStep d)^[j] x.1 := by
      intro j; induction j with
      | zero => intro x; rfl
      | succ j ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun m : ℕ => g^[m] ⟨a, h1, h2⟩)
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm he.symm (by omega)
    refine ⟨j - i, by omega, ?_⟩
    have hinj := hg.iterate i
    have : g^[i] (g^[j - i] ⟨a, h1, h2⟩) = g^[i] ⟨a, h1, h2⟩ := by
      rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]; exact he.symm
    have := congrArg Subtype.val (hinj this)
    rwa [hgi] at this

/-- After `k` steps: `a = 2^k · state + d · (the first k digits as a number below 2^k)`. -/
theorem iterate_decomp {d : ℤ} (hd : Odd d) (a : ℤ) (k : ℕ) :
    ∃ c : ℤ, 0 ≤ c ∧ c < 2 ^ k ∧ a = 2 ^ k * (digitStep d)^[k] a + d * c := by
  induction k generalizing a with
  | zero => exact ⟨0, le_rfl, by norm_num, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc0, hc1, hc⟩ := ih (digitStep d a)
    have h := two_mul_digitStep hd a
    have hb : 0 ≤ a % 2 ∧ a % 2 < 2 :=
      ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    refine ⟨a % 2 + 2 * c, by omega, ?_, ?_⟩
    · rw [pow_succ]; omega
    · rw [Function.iterate_succ_apply, pow_succ]
      calc a = 2 * digitStep d a + a % 2 * d := h.symm
        _ = 2 * (2 ^ k * (digitStep d)^[k] (digitStep d a) + d * c) + a % 2 * d := by rw [← hc]
        _ = 2 ^ k * 2 * (digitStep d)^[k] (digitStep d a) + d * (a % 2 + 2 * c) := by ring

/-- The state after `L` digits of `ρ/d` is `t - c`, when `ρ = 2^L (t - c) + d c`, `0 ≤ c < 2^L`. -/
theorem iterate_eq_sub {d : ℤ} (hd : Odd d) {L : ℕ} {ρ c t : ℤ} (hc0 : 0 ≤ c) (hc1 : c < 2 ^ L)
    (hρ : ρ = 2 ^ L * (t - c) + d * c) : (digitStep d)^[L] ρ = t - c := by
  obtain ⟨c', hc0', hc1', hc'⟩ := iterate_decomp hd ρ L
  have hpos : (0 : ℤ) < 2 ^ L := by positivity
  -- d (c - c') ≡ 0 mod 2^L with d odd and |c - c'| < 2^L forces c = c'
  have hdvd : (2 : ℤ) ^ L ∣ d * (c - c') := ⟨(digitStep d)^[L] ρ - (t - c), by linarith⟩
  have hcop : IsCoprime ((2 : ℤ) ^ L) d := by
    apply IsCoprime.pow_left
    obtain ⟨m, rfl⟩ := hd
    exact ⟨-m, 1, by ring⟩
  have h2 : (2 : ℤ) ^ L ∣ c - c' := hcop.dvd_of_dvd_mul_left hdvd
  have hcc : c = c' := by
    obtain ⟨q, hq⟩ := h2
    have : q = 0 := by
      by_contra hq0
      rcases lt_or_gt_of_ne hq0 with h | h
      · nlinarith
      · nlinarith
    subst this; linarith
  subst hcc
  have : (2 : ℤ) ^ L * ((digitStep d)^[L] ρ - (t - c)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hpos.ne'
  · linarith

/-- The digits of `x* = ρ/d` past the first `L` are purely periodic iff `t ≤ c`. -/
theorem tail_periodic_iff {d : ℤ} (hd : Odd d) (hd0 : 0 < d) {L : ℕ} {ρ c t : ℤ}
    (hρ0 : 0 ≤ ρ) (hc0 : 0 ≤ c) (hc1 : c < 2 ^ L) (hρ : ρ = 2 ^ L * (t - c) + d * c) :
    (∃ k, 0 < k ∧ (digitStep d)^[k] ((digitStep d)^[L] ρ) = (digitStep d)^[L] ρ) ↔ t ≤ c := by
  rw [periodic_iff hd hd0, iterate_eq_sub hd hc0 hc1 hρ]
  constructor
  · rintro ⟨_, h⟩; linarith
  · intro h
    refine ⟨?_, by linarith⟩
    -- 2^L (t - c) = ρ - d c ≥ -d c > -d 2^L
    by_contra hlt
    have : (2 : ℤ) ^ L * (t - c) < 2 ^ L * (-d) := by
      apply mul_lt_mul_of_pos_left (by linarith) (by positivity)
    nlinarith

/-- The word 11010 (n = 3, L = 5, d = 5, ρ = 23, class id 11, T^5(11) = 10): after its 5 digits
the state of x* = 23/5 is 10 - 11 = -1, a periodic state. -/
example : (digitStep 5)^[5] 23 = -1 := by decide

end AcceleratedCollatz
