-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TActive
import AcceleratedCollatz.TTerras

/-!
  The residues mod 2^k that have not dropped after k steps of T (OEIS A076227). A residue
  r < 2^k survives when its first k parity bits form a persistent word: 2^m < 3^o at every
  step m ≤ k, o the odd steps so far (`survives_iff`). Then every x > 0 of the class stays
  above itself for k steps (`lt_tStep_iterate_of_survives`); otherwise one step m ≤ k has
  3^o < 2^m, and every x of the class above 6^m drops at that step
  (`tStep_iterate_lt_of_not_survives`). The survivors are the persistent words of length k
  (`card_survivorSet`), counted by A076227. For k = 3: 8i + 3 and 8i + 7
  (`survivorSet_three`).
-/

namespace AcceleratedCollatz

open Finset

/-- The residues below 2^k whose first k parity bits are persistent. -/
def survivorSet (k : ℕ) : Finset ℕ :=
  (range (2 ^ k)).filter (fun r => Persistent (tBits r k))

theorem mem_survivorSet (k r : ℕ) :
    r ∈ survivorSet k ↔ r < 2 ^ k ∧ Persistent (tBits r k) := by
  simp [survivorSet]

/-- Persistent first k bits: 2^m < 3^o at every step m from 1 to k. -/
theorem survives_iff (x k : ℕ) :
    Persistent (tBits x k) ↔ ∀ m, 1 ≤ m → m ≤ k → 2 ^ m < 3 ^ order (tBits x m) := by
  unfold Persistent
  rw [length_tBits]
  refine forall_congr' fun m => imp_congr_right fun _ => forall_congr' fun hm => ?_
  rw [tBits_take x k m hm, one_lt_seqProduct_iff, length_tBits]

/-- A coefficient above 1 at step k keeps every x > 0 above itself. -/
theorem lt_tStep_iterate_of_pow_lt {x k : ℕ} (hx : 0 < x)
    (h : 2 ^ k < 3 ^ order (tBits x k)) : x < tStep^[k] x := by
  have hN := tStep_iterate_nForm k x
  have h1 : 2 ^ k * x + x ≤ 3 ^ order (tBits x k) * x := by
    have := Nat.mul_le_mul_right x (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this
    exact this
  have h2 : 2 ^ k * x < 2 ^ k * tStep^[k] x := by omega
  exact Nat.lt_of_mul_lt_mul_left h2

/-- A survivor class stays above its start for k steps. -/
theorem lt_tStep_iterate_of_survives {x k : ℕ} (hx : 0 < x) (h : Persistent (tBits x k))
    {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k) : x < tStep^[m] x :=
  lt_tStep_iterate_of_pow_lt hx ((survives_iff x k).mp h m hm1 hmk)

/-- A class that does not survive k steps drops at one step m ≤ k above 6^m. -/
theorem tStep_iterate_lt_of_not_survives {r k : ℕ} (h : ¬ Persistent (tBits r k)) :
    ∃ m, 1 ≤ m ∧ m ≤ k ∧ ∀ x, x % 2 ^ k = r % 2 ^ k → 6 ^ m < x → tStep^[m] x < x := by
  rw [survives_iff] at h
  push Not at h
  obtain ⟨m, hm1, hmk, hle⟩ := h
  have hlt : 3 ^ order (tBits r m) < 2 ^ m :=
    lt_of_le_of_ne hle (two_pow_ne_three_pow m _ hm1).symm
  refine ⟨m, hm1, hmk, fun x hxr hx => tStep_iterate_lt x m ?_ hx⟩
  have hb : tBits x k = tBits r k := by
    rw [← tBits_mod x k, hxr, tBits_mod]
  rw [← tBits_take x k m hmk, hb, tBits_take r k m hmk]
  exact hlt

/-- The survivors mod 2^k are the persistent words of length k (A076227). -/
theorem card_survivorSet (k : ℕ) : (survivorSet k).card = (activeSet k).card := by
  refine card_bij (fun r _ => tBits r k) ?_ ?_ ?_
  · intro r hr
    rw [mem_survivorSet] at hr
    rw [mem_activeSet]
    exact ⟨length_tBits r k, hr.2⟩
  · intro r hr r' hr' h
    rw [mem_survivorSet] at hr hr'
    exact eq_of_tBits_eq r r' k hr.1 hr'.1 h
  · intro s hs
    rw [mem_activeSet] at hs
    obtain ⟨x, hx, hxs⟩ := exists_tBits_eq s
    rw [hs.1] at hx hxs
    refine ⟨x, ?_, hxs⟩
    rw [mem_survivorSet, hxs]
    exact ⟨hx, hs.2⟩

/-- Mod 8: the classes 8i + 3 and 8i + 7 have not dropped after 3 steps. -/
theorem survivorSet_three : survivorSet 3 = {3, 7} := by
  decide +kernel

-- The first counts, as A076227: 1, 1, 1, 2, 3, 4, 8, 13, 19.
set_option linter.hashCommand false in
#guard (List.range 9).map (fun k => (survivorSet k).card) = [1, 1, 1, 2, 3, 4, 8, 13, 19]

end AcceleratedCollatz
