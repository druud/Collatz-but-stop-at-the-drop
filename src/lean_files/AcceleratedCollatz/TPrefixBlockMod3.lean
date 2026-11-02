-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TPrefixBlockRun
import AcceleratedCollatz.TRhoLower

/-!
  E at the first block by residues mod 3 (A21, 2 Nov 2026). With c = c(1B) and L = |B|, T(c)
  is the first of c(B), c(B) + 2^L, c(B) + 2^(L+1) that is 2 (mod 3)
  (`tStep_classId_cons_eq`). When it is not c(B), then c > 2^(L+1)/3, and E follows from
  3 rho(B) <= 2^(L+1) d(B) (`prefixBlockBound_of_lt`), so for an admissible B from
  n <= 2 d(B) (`prefixBlockBound_of_lt_admissible`). What E leaves is T(c) = c(B), that is
  c(B) = 2 (mod 3); there E reads (2 c(B) - 1) d(B) > 3 rho(B), more than B's class drop, and
  fails at the word of 47 (`TPrefixBlockFail`).
  Also, A18: 1^n 0^m has the least rho of the words of Order n (`rho_oneRun_le`), so the
  least cycle point among those of its length.
-/

namespace AcceleratedCollatz

/-- rho of 1^n 0^m. -/
theorem rho_oneRun (n m : ℕ) : rho (oneRun n m) + 2 ^ n = 3 ^ n := by
  simpa [rho] using affineNum_oneRun n m 0 0

/-- 1^n 0^m has the least rho among the words of Order n. -/
theorem rho_oneRun_le (s : List Bool) (m : ℕ) : rho (oneRun (order s) m) ≤ rho s := by
  have h1 := rho_oneRun (order s) m
  have h2 := three_pow_le_rho_add s
  omega

theorem classId_cons_odd (B : List Bool) : classId (true :: B) % 2 = 1 := by
  have hb := tBits_classId (true :: B)
  simp only [List.length_cons, tBits, List.cons.injEq, decide_eq_true_eq] at hb
  exact hb.1

theorem tBits_tStep_classId_cons (B : List Bool) :
    tBits (tStep (classId (true :: B))) B.length = B := by
  have hb := tBits_classId (true :: B)
  simp only [List.length_cons, tBits, List.cons.injEq] at hb
  exact hb.2

theorem tStep_classId_cons_mod_three (B : List Bool) :
    tStep (classId (true :: B)) % 3 = 2 := by
  have h := classId_cons_odd B
  rw [tStep_odd _ h]
  omega

/-- T(c(1B)) is the least number 2 (mod 3) with word B. -/
theorem tStep_classId_cons_le {B : List Bool} {u : ℕ} (h3 : u % 3 = 2)
    (hu : tBits u B.length = B) : tStep (classId (true :: B)) ≤ u := by
  obtain ⟨x, hx⟩ : ∃ x, 3 * x + 1 = 2 * u := ⟨(2 * u - 1) / 3, by omega⟩
  have hodd : x % 2 = 1 := by omega
  have hT : tStep x = u := by
    rw [tStep_odd _ hodd]
    omega
  have hb : tBits x (true :: B).length = true :: B := by
    have hT' : (3 * x + 1) / 2 = u := by omega
    simp [tBits, hodd, hT', hu]
  have hle := classId_le_of (true :: B) x (by omega) hb
  have hc := classId_cons_odd B
  rw [tStep_odd _ hc]
  omega

theorem two_pow_mod_three_ne (L : ℕ) : 2 ^ L % 3 ≠ 0 := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [pow_succ]
    omega

theorem three_residues {a p : ℕ} (hp : p % 3 ≠ 0) (h0 : a % 3 ≠ 2) (h1 : (a + p) % 3 ≠ 2)
    (h2 : (a + 2 * p) % 3 ≠ 2) : False := by
  have hp' : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have ha : a % 3 = 0 ∨ a % 3 = 1 := by omega
  rcases hp' with hp' | hp' <;> rcases ha with ha | ha <;> omega

/-- T(c(1B)) is the first of c(B), c(B) + 2^L, c(B) + 2^(L+1) that is 2 (mod 3). -/
theorem tStep_classId_cons_eq (B : List Bool) :
    ∃ t, t ≤ 2 ∧ tStep (classId (true :: B)) = classId B + t * 2 ^ B.length ∧
      ∀ s, s < t → (classId B + s * 2 ^ B.length) % 3 ≠ 2 := by
  have hy := tBits_tStep_classId_cons B
  have hy3 := tStep_classId_cons_mod_three B
  have hc := classId_cons_odd B
  have hy0 : 0 < tStep (classId (true :: B)) := by
    rw [tStep_odd _ hc]
    omega
  have hle := classId_le_of B _ hy0 hy
  have hm := modEq_of_tBits_eq _ _ B.length (hy.trans (tBits_classId B).symm)
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hm.symm
  have hyt : tStep (classId (true :: B)) = classId B + t * 2 ^ B.length := by
    rw [mul_comm]
    omega
  have hs : ∀ s, s < t → (classId B + s * 2 ^ B.length) % 3 ≠ 2 := by
    intro s hst h3
    have hu : tBits (classId B + s * 2 ^ B.length) B.length = B := by
      rw [tBits_congr _ (classId B) _ (by simp [Nat.ModEq]), tBits_classId]
    have h := tStep_classId_cons_le h3 hu
    rw [hyt] at h
    have hp : 0 < 2 ^ B.length := by positivity
    have := Nat.mul_lt_mul_of_pos_right hst hp
    omega
  refine ⟨t, ?_, hyt, hs⟩
  by_contra hn
  have h0 := hs 0 (by omega)
  have h1 := hs 1 (by omega)
  have h2 := hs 2 (by omega)
  have hp := two_pow_mod_three_ne B.length
  rw [zero_mul, add_zero] at h0
  rw [one_mul] at h1
  exact three_residues hp h0 h1 h2

/-- When T(c(1B)) is not c(B), the size of c(1B) alone gives E. -/
theorem prefixBlockBound_of_lt {B : List Bool}
    (hlt : classId B < tStep (classId (true :: B))) (hd : 0 < d_23 B)
    (hb : 3 * rho B ≤ 2 ^ (B.length + 1) * d_23 B) : PrefixBlockBound B := by
  obtain ⟨t, -, hyt, -⟩ := tStep_classId_cons_eq B
  have hc := classId_cons_odd B
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · simp [h0] at hyt
      omega
    · exact h0
  have hge : 2 ^ B.length ≤ t * 2 ^ B.length := Nat.le_mul_of_pos_left _ ht
  have hpos := classId_pos B
  rw [tStep_odd _ hc] at hyt
  have h3c : 2 ^ (B.length + 1) + 1 ≤ 3 * classId (true :: B) := by
    rw [pow_succ]
    omega
  have hm := Nat.mul_le_mul_left (d_23 B) h3c
  rw [PrefixBlockBound]
  have e1 : d_23 B * (3 * classId (true :: B)) = 3 * (d_23 B * classId (true :: B)) := by ring
  have e2 : d_23 B * (2 ^ (B.length + 1) + 1) = 2 ^ (B.length + 1) * d_23 B + d_23 B := by ring
  rw [e1, e2] at hm
  omega

/-- For admissible B, n <= 2 d(B) is enough. -/
theorem prefixBlockBound_of_lt_admissible {B : List Bool} (hA : Admissible B)
    (hlt : classId B < tStep (classId (true :: B))) (hd : 0 < d_23 B)
    (hn : order B ≤ 2 * d_23 B) : PrefixBlockBound B := by
  refine prefixBlockBound_of_lt hlt hd ?_
  have hr := rho_le_of_admissible B hA
  have h3 : 3 ^ order B ≤ 2 ^ B.length := (Nat.lt_of_sub_pos hd).le
  have e := three_mul_mul_pow_pred (order B)
  have hm : order B * 3 ^ order B ≤ (2 * d_23 B) * 2 ^ B.length := Nat.mul_le_mul hn h3
  have e2 : 2 ^ (B.length + 1) * d_23 B = (2 * d_23 B) * 2 ^ B.length := by ring
  rw [e2]
  omega

end AcceleratedCollatz
