-- SPDX-License-Identifier: MIT
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

/-!
  The upper record Orders (A41, 4 Nov 2026; paper 3 on A398772). With L(n) = p_2(n), the
  least L with 2^L > 3^n, the quotient (2^L - 3^n)/2^L has its new lows, for n from 1 to 971,
  exactly at n = 1, 3, 5, 17, 29, 41, 94, 147, 200, 253, 306, 971 (`upperRecord_iff`), and
  p_2(n + 53) = p_2(n) + 84 for n < 306, but p_2(359) = p_2(306) + 85 (`pT_add_53`,
  `pT_359`): the steps of 53 from 41 end at 306. In rationals throughout.
-/

namespace AcceleratedCollatz

/-- p_2(n): the least L with 2^L > 3^n. -/
def pT (n : ℕ) : ℕ := Nat.log2 (3 ^ n) + 1

/-- 2^(p_2 n) - 3^n. -/
def dT (n : ℕ) : ℕ := 2 ^ pT n - 3 ^ n

/-- (2^L - 3^n)/2^L. -/
def qT (n : ℕ) : ℚ := (dT n : ℚ) / 2 ^ pT n

/-- qT n < qT m, cross-multiplied in ℕ. -/
def lowB (n m : ℕ) : Bool := dT n * 2 ^ pT m < dT m * 2 ^ pT n

theorem qT_lt_iff (n m : ℕ) : qT n < qT m ↔ lowB n m = true := by
  unfold qT lowB
  rw [div_lt_div_iff₀ (by positivity) (by positivity), decide_eq_true_iff]
  exact_mod_cast Iff.rfl

/-- n is a new low: below every earlier Order from 1 on. -/
def NewLow (n : ℕ) : Prop := ∀ m, 1 ≤ m → m < n → qT n < qT m

/-- The scan over the Orders 1 to k + 1: the first Order of the least quotient so far, and the
  new lows in order. -/
def scanT : ℕ → ℕ × List ℕ
  | 0 => (1, [1])
  | k + 1 =>
    match scanT k with
    | (b, R) => if lowB (k + 2) b then (k + 2, R ++ [k + 2]) else (b, R)

theorem scanT_spec (k : ℕ) :
    1 ≤ (scanT k).1 ∧ (scanT k).1 ≤ k + 1 ∧
    (∀ m, 1 ≤ m → m ≤ k + 1 → qT (scanT k).1 ≤ qT m) ∧
    (∀ n, n ∈ (scanT k).2 ↔ 1 ≤ n ∧ n ≤ k + 1 ∧ NewLow n) := by
  induction k with
  | zero =>
    refine ⟨le_rfl, le_rfl, fun m h1 h2 => by rw [show m = 1 by omega]; exact le_rfl, fun n => ?_⟩
    simp only [scanT, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨le_rfl, le_rfl, fun m h1 h2 => by omega⟩
    · rintro ⟨h1, h2, -⟩; omega
  | succ k ih =>
    obtain ⟨hb1, hb2, hmin, hR⟩ := ih
    have hs : scanT (k + 1) = if lowB (k + 2) (scanT k).1 then (k + 2, (scanT k).2 ++ [k + 2])
        else (scanT k) := by
      simp only [scanT]
    by_cases hl : lowB (k + 2) (scanT k).1 = true
    · have hq := (qT_lt_iff _ _).mpr hl
      rw [hs, ite_eq_left_iff.mpr (fun h => absurd hl h)]
      have hnew : NewLow (k + 2) := fun m h1 h2 => lt_of_lt_of_le hq (hmin m h1 (by omega))
      refine ⟨by omega, le_rfl, fun m h1 h2 => ?_, fun n => ?_⟩
      · rcases Nat.lt_or_ge m (k + 2) with h | h
        · exact (lt_of_lt_of_le hq (hmin m h1 (by omega))).le
        · rw [show m = k + 2 by omega]
      · rw [List.mem_append, hR, List.mem_singleton]
        constructor
        · rintro (⟨h1, h2, h3⟩ | rfl)
          · exact ⟨h1, by omega, h3⟩
          · exact ⟨by omega, le_rfl, hnew⟩
        · rintro ⟨h1, h2, h3⟩
          rcases Nat.lt_or_ge n (k + 2) with h | h
          · exact Or.inl ⟨h1, by omega, h3⟩
          · exact Or.inr (by omega)
    · have hq : qT (scanT k).1 ≤ qT (k + 2) := not_lt.mp (fun h => hl ((qT_lt_iff _ _).mp h))
      rw [hs, ite_eq_right_iff.mpr (fun h => absurd h hl)]
      refine ⟨hb1, by omega, fun m h1 h2 => ?_, fun n => ?_⟩
      · rcases Nat.lt_or_ge m (k + 2) with h | h
        · exact hmin m h1 (by omega)
        · rw [show m = k + 2 by omega]; exact hq
      · rw [hR]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, ?_, h3⟩
          by_contra h
          have := h3 (scanT k).1 hb1 (by omega)
          rw [show n = k + 2 by omega] at this
          exact absurd hq (not_le.mpr this)

theorem scanT_970 : (scanT 970).2 = [1, 3, 5, 17, 29, 41, 94, 147, 200, 253, 306, 971] := by
  decide +kernel

/-- The upper record Orders up to 971: the new lows of (2^L - 3^n)/2^L. -/
theorem upperRecord_iff (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 971) :
    NewLow n ↔ n ∈ [1, 3, 5, 17, 29, 41, 94, 147, 200, 253, 306, 971] := by
  rw [← scanT_970, ((scanT_spec 970).2.2.2 n)]
  exact ⟨fun h => ⟨h1, h2, h⟩, fun h => h.2.2⟩

theorem pT_add_53_table :
    (List.range 306).all (fun n => pT (n + 53) == pT n + 84) = true := by
  decide +kernel

/-- p_2(n + 53) = p_2(n) + 84 for n < 306. -/
theorem pT_add_53 (n : ℕ) (h : n < 306) : pT (n + 53) = pT n + 84 := by
  simpa using List.all_eq_true.mp pT_add_53_table n (List.mem_range.mpr h)

/-- At 306 the step of 53 adds 85, so the steps of 53 from 41 end there. -/
theorem pT_359 : pT 359 = pT 306 + 85 := by
  decide +kernel

end AcceleratedCollatz
