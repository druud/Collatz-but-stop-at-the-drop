-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.DescendToMinimum
import AcceleratedCollatz.TSieve

/-!
  conj:covering in T-form: every x > 1 has an admissible parity prefix
  (finite coefficient stopping time). With Drop := every x > 1 eventually
  drops under T:
  Covering ∧ WidthIdentity → Drop (`drops_of_covering_width`) and
  Drop → Covering (`covering_of_drops`). Under WidthIdentity, Drop ↔ Covering.
-/

namespace AcceleratedCollatz

open DescendToMinimum

/-- conj:covering: every x > 1 has an admissible prefix of its T-parity bits. -/
def Covering : Prop :=
  ∀ x, 1 < x → ∃ n, Admissible (tBits x n)

/-- 2^m ≠ 3^a for m ≥ 1. -/
theorem two_pow_ne_three_pow (m a : ℕ) (hm : 1 ≤ m) : 2 ^ m ≠ 3 ^ a := by
  intro h
  have hodd : (3 ^ a) % 2 = 1 := Nat.odd_iff.mp ((by decide : Odd 3).pow)
  have heven : (2 ^ m) % 2 = 0 := by
    obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ]
    simp
  omega

/-- The empty word is not admissible. -/
theorem not_admissible_nil : ¬ Admissible [] := by
  intro h
  have h2 := h.2
  simp [seqProduct] at h2

theorem drops_of_covering_width (hC : Covering) (hW : WidthIdentity) :
    DropsToward tStep 1 := by
  intro x hx
  obtain ⟨n, hA⟩ := hC x hx
  refine ⟨n, ?_, hW x n hx hA⟩
  by_contra h0
  have hn : n = 0 := by omega
  rw [hn] at hA
  exact not_admissible_nil hA

/-- A coefficient below 1 at step k gives an admissible prefix of length ≤ k. -/
theorem exists_admissible_of_pow_lt (x k : ℕ) (hk1 : 1 ≤ k)
    (hk : 3 ^ order (tBits x k) < 2 ^ k) :
    ∃ n, n ≤ k ∧ Admissible (tBits x n) := by
  have hex : ∃ m, 1 ≤ m ∧ 3 ^ order (tBits x m) < 2 ^ m := ⟨k, hk1, hk⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ⟨hk1, hk⟩, ?_⟩
  obtain ⟨_, hPn⟩ := Nat.find_spec hex
  rw [admissible_iff_pow, length_tBits]
  refine ⟨?_, hPn⟩
  intro m hm hm1
  rw [tBits_take x _ m hm.le]
  have hmin := Nat.find_min hex hm
  push Not at hmin
  have hle := hmin hm1
  have hne := two_pow_ne_three_pow m (order (tBits x m)) hm1
  omega

theorem covering_of_drops (hD : DropsToward tStep 1) : Covering := by
  intro x hx
  obtain ⟨k, hk1, hk⟩ := hD x hx
  have hN := tStep_iterate_nForm k x
  have hPk : 3 ^ order (tBits x k) < 2 ^ k := by
    have h1 : 2 ^ k * tStep^[k] x < 2 ^ k * x := Nat.mul_lt_mul_of_pos_left hk (by positivity)
    rw [hN] at h1
    have h2 : 3 ^ order (tBits x k) * x < 2 ^ k * x := by
      omega
    exact Nat.lt_of_mul_lt_mul_right h2
  obtain ⟨n, -, hA⟩ := exists_admissible_of_pow_lt x k hk1 hPk
  exact ⟨n, hA⟩

/-- Under the Width Identity, Drop is equivalent to Covering. -/
theorem drops_iff_covering (hW : WidthIdentity) : DropsToward tStep 1 ↔ Covering :=
  ⟨covering_of_drops, fun hC => drops_of_covering_width hC hW⟩

end AcceleratedCollatz
