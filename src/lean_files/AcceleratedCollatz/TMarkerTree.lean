-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TMarkerPointHigh

/-!
  The trees of Yu-Ting (AYT) and of Hanna, Czyz and Self (HCS) as defined in K. Ryde, Trees
  of Rationals: node n ≥ 1 is the product of L = [[1, 1], [0, 1]] (a digit 0, y ↦ y + 1) and
  R = [[0, 1], [1, 1]] (a digit 1, y ↦ 1/(y + 1)) over the binary digits of n below its top
  digit, applied to [1; 1] (`treePoint`); HCS takes these digits highest first
  (`hcsPoint`), AYT lowest first (`aytPoint`). The node 2^(B + 1) - 1 - x of a number x ≥ 1
  with B binary digits carries the point of x read from the lowest digit in AYT
  (`aytPoint_complement`, `markerPoint`) and read from the highest digit in HCS
  (`hcsPoint_complement`, `hiPoint`; also for x = 0).
-/

namespace AcceleratedCollatz

/-- Ryde's matrix R for a digit 1 (y ↦ 1/(y + 1)) and L for a digit 0 (y ↦ y + 1). -/
def treeStep (b : Bool) (y : ℚ) : ℚ :=
  if b then 1 / (y + 1) else y + 1

/-- The product of the matrices of a list of digits, the first one outermost, on [1; 1]. -/
def treePoint (v : List Bool) : ℚ :=
  v.foldr treeStep 1

/-- Node n of the HCS tree: the digits of n below its top digit, highest first. -/
def hcsPoint (n : ℕ) : ℚ :=
  treePoint (toBits n).dropLast.reverse

/-- Node n of the AYT tree: the digits of n below its top digit, lowest first. -/
def aytPoint (n : ℕ) : ℚ :=
  treePoint (toBits n).dropLast

/-- The tree maps on complemented digits are the maps of `digitPoint`. -/
theorem treePoint_map_not : ∀ ds : List Bool, treePoint (ds.map not) = digitPoint ds
  | [] => rfl
  | true :: ds => by
    change treePoint (ds.map not) + 1 = digitPoint ds + 1
    rw [treePoint_map_not ds]
  | false :: ds => by
    change 1 / (treePoint (ds.map not) + 1) = 1 / (digitPoint ds + 1)
    rw [treePoint_map_not ds]

/-! ### Numbers and their digits -/

theorem ofBits_toBits (n : ℕ) : ofBits (toBits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [toBits_zero]
      rfl
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hn : n = 2 * (n / 2) := by
          omega
        rw [hn, toBits_bit_zero (by omega)]
        change 2 * ofBits (toBits (n / 2)) = 2 * (n / 2)
        rw [ih (n / 2) (by omega)]
      · have hn : n = 2 * (n / 2) + 1 := by
          omega
        rw [hn, toBits_bit_one]
        change 2 * ofBits (toBits (n / 2)) + 1 = 2 * (n / 2) + 1
        rw [ih (n / 2) (by omega)]

theorem topTrue_toBits {n : ℕ} (hn : 1 ≤ n) : TopTrue (toBits n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have e : n = 2 * 0 + 1 := by
        omega
      rw [e, toBits_bit_one, toBits_zero]
      rfl
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hn : n = 2 * (n / 2) := by
          omega
        rw [hn, toBits_bit_zero (by omega)]
        exact topTrue_cons false (ih (n / 2) (by omega) (by omega))
      · have hn : n = 2 * (n / 2) + 1 := by
          omega
        rw [hn, toBits_bit_one]
        exact topTrue_cons true (ih (n / 2) (by omega) (by omega))

/-- A digit 1 on top adds 2^(number of digits). -/
theorem ofBits_append_true : ∀ ds : List Bool, ofBits (ds ++ [true]) = ofBits ds + 2 ^ ds.length
  | [] => rfl
  | true :: ds => by
    change 2 * ofBits (ds ++ [true]) + 1 = 2 * ofBits ds + 1 + 2 ^ (ds.length + 1)
    rw [ofBits_append_true ds, pow_succ]
    ring
  | false :: ds => by
    change 2 * ofBits (ds ++ [true]) = 2 * ofBits ds + 2 ^ (ds.length + 1)
    rw [ofBits_append_true ds, pow_succ]
    ring

/-- A list and its complement add up to all digits 1. -/
theorem ofBits_map_not_add : ∀ ds : List Bool, ofBits (ds.map not) + ofBits ds + 1 = 2 ^ ds.length
  | [] => rfl
  | true :: ds => by
    have ih := ofBits_map_not_add ds
    change 2 * ofBits (ds.map not) + (2 * ofBits ds + 1) + 1 = 2 ^ (ds.length + 1)
    rw [pow_succ]
    omega
  | false :: ds => by
    have ih := ofBits_map_not_add ds
    change 2 * ofBits (ds.map not) + 1 + 2 * ofBits ds + 1 = 2 ^ (ds.length + 1)
    rw [pow_succ]
    omega

/-- The node of the complemented digits with a digit 1 on top. -/
theorem ofBits_complement (ds : List Bool) :
    ofBits (ds.map not ++ [true]) = 2 ^ (ds.length + 1) - 1 - ofBits ds := by
  have h1 := ofBits_append_true (ds.map not)
  have h2 := ofBits_map_not_add ds
  rw [List.length_map] at h1
  rw [h1, pow_succ]
  omega

/-! ### The two trees -/

theorem aytPoint_ofBits {ds : List Bool} (h : TopTrue ds) :
    aytPoint (ofBits (ds.map not ++ [true])) = markerPoint (ofBits ds) := by
  have hT : TopTrue (ds.map not ++ [true]) := topTrue_append _ rfl
  rw [aytPoint, toBits_ofBits _ hT, List.dropLast_concat, treePoint_map_not,
    markerPoint_ofBits ds h]

theorem hcsPoint_ofBits (ds : List Bool) :
    hcsPoint (ofBits (ds.map not ++ [true])) = digitPoint ds.reverse := by
  have hT : TopTrue (ds.map not ++ [true]) := topTrue_append _ rfl
  have e : (ds.map not).reverse = ds.reverse.map not := by
    simp
  rw [hcsPoint, toBits_ofBits _ hT, List.dropLast_concat, e, treePoint_map_not]

/-- AYT at the complement of x ≥ 1 with one more digit on top is x read from the lowest
    digit. -/
theorem aytPoint_complement {x : ℕ} (hx : 1 ≤ x) :
    aytPoint (2 ^ ((toBits x).length + 1) - 1 - x) = markerPoint x := by
  have e := ofBits_complement (toBits x)
  rw [ofBits_toBits] at e
  rw [← e, aytPoint_ofBits (topTrue_toBits hx), ofBits_toBits]

/-- HCS at the complement of x with one more digit on top is x read from the highest
    digit. -/
theorem hcsPoint_complement (x : ℕ) :
    hcsPoint (2 ^ ((toBits x).length + 1) - 1 - x) = hiPoint x := by
  have e := ofBits_complement (toBits x)
  rw [ofBits_toBits] at e
  rw [← e, hcsPoint_ofBits]
  rfl

end AcceleratedCollatz
