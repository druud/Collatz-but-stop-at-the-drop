-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCovering
import AcceleratedCollatz.TWidth

/-!
  Terras implication: WidthIdentity excludes nontrivial T-cycles. The least
  value y > 2 of a cycle of length m has 3^o < 2^m for its cycle word, so a
  coefficient first passage n ≤ m exists; WidthIdentity puts a value below y
  on the cycle.
-/

namespace AcceleratedCollatz

/-- On a cycle of length m, the iterates repeat with period m. -/
theorem iterate_mod_of_cycle (x m : ℕ) (hc : tStep^[m] x = x) (j : ℕ) :
    tStep^[j] x = tStep^[j % m] x := by
  conv_lhs => rw [← Nat.mod_add_div j m]
  induction j / m with
  | zero =>
    simp
  | succ q ih =>
    rw [Nat.mul_succ, ← add_assoc, Function.iterate_add_apply, hc, ih]

/-- Values ≤ 2 stay ≤ 2 under T. -/
theorem iterate_le_two (y j : ℕ) (hy : y ≤ 2) : tStep^[j] y ≤ 2 := by
  induction j generalizing y with
  | zero =>
    simpa using hy
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    interval_cases y
    · decide
    · decide
    · decide

/-- WidthIdentity: every T-cycle lies in {0, 1, 2}. -/
theorem no_cycle_of_widthIdentity (hW : WidthIdentity) (x m : ℕ) (hm : 0 < m)
    (hc : tStep^[m] x = x) : x ≤ 2 := by
  set S := (Finset.range m).image (fun i => tStep^[i] x) with hS
  have hne : S.Nonempty := ⟨x, Finset.mem_image.mpr ⟨0, by simp [hm], rfl⟩⟩
  obtain ⟨y, hyS, hmin⟩ : ∃ y ∈ S, ∀ z ∈ S, y ≤ z :=
    ⟨S.min' hne, S.min'_mem hne, fun z hz => S.min'_le z hz⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hyS
  have hle : ∀ j, tStep^[i] x ≤ tStep^[j] (tStep^[i] x) := by
    intro j
    rw [← Function.iterate_add_apply, iterate_mod_of_cycle x m hc (j + i)]
    exact hmin _ (Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.mod_lt _ hm), rfl⟩)
  have hxy : tStep^[m - i] (tStep^[i] x) = x := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Finset.mem_range.mp hi).le, hc]
  set y := tStep^[i] x with hy
  by_contra hx
  have hy2 : 2 < y := by
    by_contra h
    have := iterate_le_two y (m - i) (by omega)
    omega
  have hcy : tStep^[m] y = y := by
    rw [hy, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hc]
  have hN := tStep_iterate_nForm m y
  rw [hcy] at hN
  have hle3 : 3 ^ order (tBits y m) ≤ 2 ^ m :=
    Nat.le_of_mul_le_mul_right (by omega : 3 ^ order (tBits y m) * y ≤ 2 ^ m * y) (by omega)
  have hlt : 3 ^ order (tBits y m) < 2 ^ m :=
    lt_of_le_of_ne hle3 (two_pow_ne_three_pow m _ hm).symm
  obtain ⟨n, -, hA⟩ := exists_admissible_of_pow_lt y m hm hlt
  have := hW y n (by omega) hA
  have := hle n
  omega

end AcceleratedCollatz
