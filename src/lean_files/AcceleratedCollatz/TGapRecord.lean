-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TGapRatio
import AcceleratedCollatz.TRhoLower
import AcceleratedCollatz.TFiniteCheck
import AcceleratedCollatz.TFiniteCheckNext

/-!
  A gap-ratio record is the class id of its word (A47, 4 Nov 2026; OEIS A398772). Let x drop
  at |s|, s its admissible T-parity word of Order > 0, and let no smaller start with the word
  s that drops at |s| have a smaller gap ratio g = (x - y)/x. If the class id of s is > 1 and
  drops (ClassDrops at the Order of s), then x is the class id (`eq_classId_of_gapRecord`).
  Up to Order 10781273 this needs only the range check below 984572779224
  (`eq_classId_of_gapRecord_le_10781273`). An even x drops at step 1, an x = 4i + 1 at step 2
  (to 3i + 1); for a record x == 3 (mod 4) both conditions on s hold
  (`eq_classId_of_gapRecord_mod4_of_classDrops`, `eq_classId_of_gapRecord_mod4`). With the
  range check below 294401822513350 (A20) the same holds up to Order 64497106
  (`eq_classId_of_gapRecord_le_64497106`, `eq_classId_of_gapRecord_mod4_le_64497106`).
-/

namespace AcceleratedCollatz

/-- x drops at |s| and no smaller start x' with the same word that drops at |s| has a
  smaller gap ratio, cross-multiplied: (x - y) x' <= (x' - y') x. -/
def GapRecordAt (s : List Bool) (x : ℕ) : Prop :=
  tBits x s.length = s ∧ tStep^[s.length] x < x ∧
    ∀ x', 0 < x' → x' < x → tBits x' s.length = s → tStep^[s.length] x' < x' →
      (x - tStep^[s.length] x) * x' ≤ (x' - tStep^[s.length] x') * x

/-- A gap-ratio record with an admissible word s of Order > 0 is the class id of s, if the
  class id is > 1 and ClassDrops holds at the Order of s. -/
theorem eq_classId_of_gapRecord (s : List Bool) (x : ℕ) (hA : Admissible s)
    (ho : 0 < order s) (hc : 1 < classId s) (hCD : ClassDropsAt (order s))
    (hR : GapRecordAt s x) : x = classId s := by
  obtain ⟨hs, hy, hrec⟩ := hR
  have hx0 : 0 < x := by omega
  have hle := classId_le_of s x hx0 hs
  by_contra hne
  have hlt : classId s < x := lt_of_le_of_ne hle (Ne.symm hne)
  have hρ : 0 < rho s := (rho_pos_iff s).mpr ho
  have hcs := tBits_classId s
  have hcy : tStep^[s.length] (classId s) < classId s :=
    (drop_iff_rho s (classId s) hA hcs).mpr (hCD s hA rfl hc)
  have h1 := gap_mul_lt_of_lt s x (classId s) hA hρ hs hcs hlt hcy
  have h2 := hrec (classId s) (classId_pos s) hlt hcs hcy
  omega

/-- Up to Order 10781273: a gap-ratio record is the class id of its word, from the range check
  up to 984572779224 alone. -/
theorem eq_classId_of_gapRecord_le_10781273
    (hX : ∀ x, 1 < x → x ≤ 984572779224 → ∀ m, Admissible (tBits x m) → tStep^[m] x < x)
    (s : List Bool) (x : ℕ) (hA : Admissible s) (ho : 0 < order s)
    (hn : order s ≤ 10781273) (hc : 1 < classId s) (hR : GapRecordAt s x) :
    x = classId s :=
  eq_classId_of_gapRecord s x hA ho hc (classDropsAt_le_10781273 hX _ hn) hR

/-- Up to Order 64497106: a gap-ratio record is the class id of its word, from the range check
  up to 294401822513350 alone. -/
theorem eq_classId_of_gapRecord_le_64497106
    (hX : ∀ x, 1 < x → x ≤ 294401822513350 → ∀ m, Admissible (tBits x m) → tStep^[m] x < x)
    (s : List Bool) (x : ℕ) (hA : Admissible s) (ho : 0 < order s)
    (hn : order s ≤ 64497106) (hc : 1 < classId s) (hR : GapRecordAt s x) :
    x = classId s :=
  eq_classId_of_gapRecord s x hA ho hc (classDropsAt_le_64497106 hX _ hn) hR

/-- A start x == 3 (mod 4) with an admissible word s has |s| >= 2: an x == 1 (mod 4) drops at
  step 2, to 3i + 1 for x = 4i + 1, and an even x at step 1. -/
theorem two_le_length_of_mod4 (s : List Bool) (x : ℕ) (hA : Admissible s)
    (hs : tBits x s.length = s) (h3 : x % 4 = 3) : 2 ≤ s.length := by
  have hlen := admissible_length s hA
  by_contra hlt
  have h1 : s.length = 1 := by
    have : 1 ≤ p2_of (order s) := by unfold p2_of; omega
    omega
  have hodd : x % 2 = 1 := by omega
  have hsv : s = [true] := by
    rw [← hs, h1]
    simp [tBits, hodd]
  rw [hsv] at hlen
  simp [order, p2_of_one] at hlen

/-- A gap-ratio record x == 3 (mod 4) is the class id of its word, if ClassDrops holds at the
  Order of the word: the class id is > 1 and the Order is > 0. -/
theorem eq_classId_of_gapRecord_mod4_of_classDrops
    (s : List Bool) (x : ℕ) (hA : Admissible s) (h3 : x % 4 = 3)
    (hCD : ClassDropsAt (order s)) (hR : GapRecordAt s x) : x = classId s := by
  have h2 := two_le_length_of_mod4 s x hA hR.1 h3
  have hm : x ≡ classId s [MOD 2 ^ 2] :=
    Nat.ModEq.of_dvd (pow_dvd_pow 2 h2)
      (modEq_of_tBits_eq x (classId s) s.length (by rw [hR.1, tBits_classId]))
  have hc : 1 < classId s := by
    unfold Nat.ModEq at hm
    norm_num at hm
    omega
  have ho : 0 < order s := by
    by_contra h0
    have hlen := admissible_length s hA
    rw [show order s = 0 by omega, p2_of_zero] at hlen
    omega
  exact eq_classId_of_gapRecord s x hA ho hc hCD hR

/-- From 3 (mod 4) on, up to Order 10781273: a gap-ratio record x == 3 (mod 4) is the class id
  of its word, from the range check up to 984572779224 alone. -/
theorem eq_classId_of_gapRecord_mod4
    (hX : ∀ x, 1 < x → x ≤ 984572779224 → ∀ m, Admissible (tBits x m) → tStep^[m] x < x)
    (s : List Bool) (x : ℕ) (hA : Admissible s) (hn : order s ≤ 10781273) (h3 : x % 4 = 3)
    (hR : GapRecordAt s x) : x = classId s :=
  eq_classId_of_gapRecord_mod4_of_classDrops s x hA h3 (classDropsAt_le_10781273 hX _ hn) hR

/-- From 3 (mod 4) on, up to Order 64497106: a gap-ratio record x == 3 (mod 4) is the class id
  of its word, from the range check up to 294401822513350 alone. -/
theorem eq_classId_of_gapRecord_mod4_le_64497106
    (hX : ∀ x, 1 < x → x ≤ 294401822513350 → ∀ m, Admissible (tBits x m) → tStep^[m] x < x)
    (s : List Bool) (x : ℕ) (hA : Admissible s) (hn : order s ≤ 64497106) (h3 : x % 4 = 3)
    (hR : GapRecordAt s x) : x = classId s :=
  eq_classId_of_gapRecord_mod4_of_classDrops s x hA h3 (classDropsAt_le_64497106 hX _ hn) hR

end AcceleratedCollatz
