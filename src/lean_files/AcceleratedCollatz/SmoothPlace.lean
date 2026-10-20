-- SPDX-License-Identifier: MIT
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# The place of p^a q^b among the numbers p^i q^j (Mintz 1981)

Self-contained extract of the AcceleratedCollatz Lean 4 project; depends on
Mathlib only.

D. J. Mintz, "2,3 sequence as binary mixture", Fibonacci Quart. 19 (1981),
351-360, counts the numbers 2^i 3^j below 2^a 3^b. Here the two bases are any
p, q > 1, and what is counted are the lattice points (i, j) with
p^i q^j < p^a q^b (`place`).

* Theorem 1 (`place_eq_add`): place(a, b) = a b + place(a, 0) + place(0, b).
* Theorem 2 (`place_left`): place(a, 0) is the sum over k ≤ a of the number of
  powers of q below p^k, which is `Nat.clog q (p ^ k)`
  (`Nat.lt_clog_iff_pow_lt`: m < clog q x exactly when q^m < x).
* Theorem 3 (`place_right`): the same with p and q exchanged.
* Theorems 4 and 7 (`place_eq`): the three together.
* For coprime p and q the lattice points are the numbers p^i q^j themselves
  (`pow_mul_pow_inj`), so `place` is the place of p^a q^b in their increasing
  list, counted from 0 (`ord_eq_place`, `ord_two_three`).
-/

namespace SmoothPlace

variable {p q : ℕ}

/-- The lattice points (i, j) with p^i q^j < p^a q^b. -/
def below (p q a b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (p ^ a * q ^ b) ×ˢ Finset.range (p ^ a * q ^ b)).filter
    (fun x => p ^ x.1 * q ^ x.2 < p ^ a * q ^ b)

/-- (i, j) is in `below p q a b` exactly when p^i q^j < p^a q^b. -/
theorem mem_below (hp : 1 < p) (hq : 1 < q) {a b : ℕ} {x : ℕ × ℕ} :
    x ∈ below p q a b ↔ p ^ x.1 * q ^ x.2 < p ^ a * q ^ b := by
  unfold below
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · have h1 : x.1 < p ^ x.1 := Nat.lt_pow_self hp
    have h2 : p ^ x.1 ≤ p ^ x.1 * q ^ x.2 := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    omega
  · have h1 : x.2 < q ^ x.2 := Nat.lt_pow_self hq
    have h2 : q ^ x.2 ≤ p ^ x.1 * q ^ x.2 := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
    omega

/-- The place of p^a q^b: the number of lattice points below (a, b). -/
def place (p q a b : ℕ) : ℕ := (below p q a b).card

/-- A shift of the lattice by (c, d) keeps the order of the values. -/
theorem shift_lt_iff (hp : 1 < p) (hq : 1 < q) (i j a b c d : ℕ) :
    p ^ (i + c) * q ^ (j + d) < p ^ (a + c) * q ^ (b + d) ↔ p ^ i * q ^ j < p ^ a * q ^ b := by
  have h : ∀ i j, p ^ (i + c) * q ^ (j + d) = p ^ i * q ^ j * (p ^ c * q ^ d) := by
    intro i j
    ring
  have hpos : 0 < p ^ c * q ^ d := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  rw [h, h, Nat.mul_lt_mul_right hpos]

/-- The points below (a + c, b + d) that lie at or beyond (c, d) are as many as the points
    below (a, b). -/
theorem card_filter_shift (hp : 1 < p) (hq : 1 < q) (a b c d : ℕ) :
    ((below p q (a + c) (b + d)).filter (fun x => c ≤ x.1 ∧ d ≤ x.2)).card = place p q a b := by
  apply Finset.card_nbij' (fun x => (x.1 - c, x.2 - d)) (fun x => (x.1 + c, x.2 + d))
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, mem_below hp hq] at hx
    rw [Finset.mem_coe, mem_below hp hq, ← shift_lt_iff hp hq _ _ a b c d]
    change p ^ (x.1 - c + c) * q ^ (x.2 - d + d) < p ^ (a + c) * q ^ (b + d)
    rw [Nat.sub_add_cancel hx.2.1, Nat.sub_add_cancel hx.2.2]
    exact hx.1
  · intro x hx
    rw [Finset.mem_coe, mem_below hp hq] at hx
    rw [Finset.mem_coe, Finset.mem_filter, mem_below hp hq]
    exact ⟨(shift_lt_iff hp hq _ _ a b c d).mpr hx, Nat.le_add_left _ _, Nat.le_add_left _ _⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    exact Prod.ext (Nat.sub_add_cancel hx.2.1) (Nat.sub_add_cancel hx.2.2)
  · intro x _
    exact Prod.ext (Nat.add_sub_cancel x.1 c) (Nat.add_sub_cancel x.2 d)

/-- Mintz, Theorem 1: the points below (a, b) are those of the a by b rectangle, those at
    or above row b, and those at or right of column a. -/
theorem place_eq_add (hp : 1 < p) (hq : 1 < q) (a b : ℕ) :
    place p q a b = a * b + place p q a 0 + place p q 0 b := by
  have hrect : (below p q a b).filter (fun x => x.1 < a ∧ x.2 < b) =
      Finset.range a ×ˢ Finset.range b := by
    ext x
    rw [Finset.mem_filter, mem_below hp hq, Finset.mem_product, Finset.mem_range,
      Finset.mem_range]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    have h1 : p ^ x.1 < p ^ a := Nat.pow_lt_pow_right hp h.1
    have h2 : q ^ x.2 < q ^ b := Nat.pow_lt_pow_right hq h.2
    exact Nat.mul_lt_mul'' h1 h2
  have hup := card_filter_shift hp hq a 0 0 b
  have hright := card_filter_shift hp hq 0 b a 0
  rw [Nat.add_zero, Nat.zero_add] at hup hright
  have hnot : ∀ x ∈ below p q a b, ¬ (a ≤ x.1 ∧ b ≤ x.2) := by
    intro x hx h
    rw [mem_below hp hq] at hx
    have h1 : p ^ a ≤ p ^ x.1 := Nat.pow_le_pow_right (by omega) h.1
    have h2 : q ^ b ≤ q ^ x.2 := Nat.pow_le_pow_right (by omega) h.2
    have h3 := Nat.mul_le_mul h1 h2
    omega
  have h1 := Finset.card_filter_add_card_filter_not (s := below p q a b)
    (fun x => x.1 < a ∧ x.2 < b)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (below p q a b).filter (fun x => ¬ (x.1 < a ∧ x.2 < b)))
    (fun x => 0 ≤ x.1 ∧ b ≤ x.2)
  have hU : (below p q a b).filter
      (fun x => ¬ (x.1 < a ∧ x.2 < b) ∧ (0 ≤ x.1 ∧ b ≤ x.2)) =
      (below p q a b).filter (fun x => 0 ≤ x.1 ∧ b ≤ x.2) := by
    apply Finset.filter_congr
    intro x _
    omega
  have hR : (below p q a b).filter
      (fun x => ¬ (x.1 < a ∧ x.2 < b) ∧ ¬ (0 ≤ x.1 ∧ b ≤ x.2)) =
      (below p q a b).filter (fun x => a ≤ x.1 ∧ 0 ≤ x.2) := by
    apply Finset.filter_congr
    intro x hx
    have h := hnot x hx
    omega
  rw [Finset.filter_filter, Finset.filter_filter, hU, hR, hup, hright] at h2
  rw [hrect, Finset.card_product, Finset.card_range, Finset.card_range] at h1
  unfold place at h2 ⊢
  omega

/-- No lattice point lies below (0, 0). -/
theorem place_zero_zero (hp : 1 < p) (hq : 1 < q) : place p q 0 0 = 0 := by
  unfold place
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_below hp hq, pow_zero, pow_zero, Nat.mul_one] at hx
  have h : 0 < p ^ x.1 * q ^ x.2 := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  omega

/-- One more column: the points below (a + 1, 0) are the points below (a, 0), moved one
    column to the right, and the powers of q below p^(a + 1) in column 0. -/
theorem place_succ_zero (hp : 1 < p) (hq : 1 < q) (a : ℕ) :
    place p q (a + 1) 0 = place p q a 0 + Nat.clog q (p ^ (a + 1)) := by
  have hshift : ((below p q (a + 1) 0).filter (fun x => 1 ≤ x.1 ∧ 0 ≤ x.2)).card =
      place p q a 0 := card_filter_shift hp hq a 0 1 0
  have hcol : (below p q (a + 1) 0).filter (fun x => ¬ (1 ≤ x.1 ∧ 0 ≤ x.2)) =
      (Finset.range (Nat.clog q (p ^ (a + 1)))).image (fun m => (0, m)) := by
    ext x
    rw [Finset.mem_filter, mem_below hp hq, Finset.mem_image]
    constructor
    · intro h
      have h0 : x.1 = 0 := by omega
      refine ⟨x.2, ?_, Prod.ext h0.symm rfl⟩
      rw [Finset.mem_range, Nat.lt_clog_iff_pow_lt hq]
      have h1 := h.1
      rw [h0, pow_zero, pow_zero, Nat.one_mul, Nat.mul_one] at h1
      exact h1
    · intro h
      obtain ⟨m, hm, hmx⟩ := h
      rw [Finset.mem_range, Nat.lt_clog_iff_pow_lt hq] at hm
      rw [← hmx]
      change p ^ 0 * q ^ m < p ^ (a + 1) * q ^ 0 ∧ ¬ (1 ≤ 0 ∧ 0 ≤ m)
      rw [pow_zero, pow_zero, Nat.one_mul, Nat.mul_one]
      exact ⟨hm, by omega⟩
  have hinj : Function.Injective (fun m : ℕ => ((0 : ℕ), m)) := by
    intro m n h
    exact (Prod.ext_iff.mp h).2
  have hsplit := Finset.card_filter_add_card_filter_not (s := below p q (a + 1) 0)
    (fun x => 1 ≤ x.1 ∧ 0 ≤ x.2)
  rw [hcol, Finset.card_image_of_injective _ hinj, Finset.card_range] at hsplit
  unfold place at hshift ⊢
  omega

/-- Mintz, Theorem 2: the place of p^a is the sum over k ≤ a of the number of powers of q
    below p^k. -/
theorem place_left (hp : 1 < p) (hq : 1 < q) (a : ℕ) :
    place p q a 0 = ∑ k ∈ Finset.range (a + 1), Nat.clog q (p ^ k) := by
  induction a with
  | zero =>
    rw [place_zero_zero hp hq, Finset.sum_range_one, pow_zero, Nat.clog_one_right]
  | succ a ih =>
    rw [place_succ_zero hp hq, ih, Finset.sum_range_succ _ (a + 1)]

/-- Exchanging the two bases mirrors the lattice. -/
theorem place_swap (hp : 1 < p) (hq : 1 < q) (a b : ℕ) : place p q a b = place q p b a := by
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro x hx
    rw [Finset.mem_coe, mem_below hp hq] at hx
    rw [Finset.mem_coe, mem_below hq hp, Prod.fst_swap, Prod.snd_swap, Nat.mul_comm,
      Nat.mul_comm (q ^ b)]
    exact hx
  · intro x hx
    rw [Finset.mem_coe, mem_below hq hp] at hx
    rw [Finset.mem_coe, mem_below hp hq, Prod.fst_swap, Prod.snd_swap, Nat.mul_comm,
      Nat.mul_comm (p ^ a)]
    exact hx
  · intro x _
    exact Prod.swap_swap x
  · intro x _
    exact Prod.swap_swap x

/-- Mintz, Theorem 3: the place of q^b is the sum over k ≤ b of the number of powers of p
    below q^k. -/
theorem place_right (hp : 1 < p) (hq : 1 < q) (b : ℕ) :
    place p q 0 b = ∑ k ∈ Finset.range (b + 1), Nat.clog p (q ^ k) := by
  rw [place_swap hp hq, place_left hq hp]

/-- Mintz, Theorems 4 and 7: the place of p^a q^b. -/
theorem place_eq (hp : 1 < p) (hq : 1 < q) (a b : ℕ) :
    place p q a b = a * b + ∑ k ∈ Finset.range (a + 1), Nat.clog q (p ^ k) +
      ∑ k ∈ Finset.range (b + 1), Nat.clog p (q ^ k) := by
  rw [place_eq_add hp hq, place_left hp hq, place_right hp hq]

/-- For coprime p and q, the number p^i q^j determines i and j. -/
theorem pow_mul_pow_inj (h : Nat.Coprime p q) (hp : 1 < p) (hq : 1 < q) {i j i' j' : ℕ}
    (heq : p ^ i * q ^ j = p ^ i' * q ^ j') : i = i' ∧ j = j' := by
  have h1 : p ^ i ∣ p ^ i' * q ^ j' := Dvd.intro _ heq
  have h2 : p ^ i' ∣ p ^ i * q ^ j := Dvd.intro _ heq.symm
  have h3 := (Nat.pow_dvd_pow_iff_le_right hp).mp ((h.pow i j').dvd_of_dvd_mul_right h1)
  have h4 := (Nat.pow_dvd_pow_iff_le_right hp).mp ((h.pow i' j).dvd_of_dvd_mul_right h2)
  have hi : i = i' := Nat.le_antisymm h3 h4
  rw [hi] at heq
  have h5 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) heq
  exact ⟨hi, Nat.pow_right_injective hq h5⟩

open Classical in
/-- Ord(n) with respect to the p, q sequence: the number of its members below n. -/
noncomputable def ord (p q n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun m => ∃ i j, m = p ^ i * q ^ j)).card

/-- For coprime p and q, the place of p^a q^b in the increasing list of the numbers
    p^i q^j, counted from 0, is the number of lattice points below (a, b). -/
theorem ord_eq_place (h : Nat.Coprime p q) (hp : 1 < p) (hq : 1 < q) (a b : ℕ) :
    ord p q (p ^ a * q ^ b) = place p q a b := by
  classical
  symm
  apply Finset.card_bij (fun x _ => p ^ x.1 * q ^ x.2)
  · intro x hx
    rw [mem_below hp hq] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hx, x.1, x.2, rfl⟩
  · intro x _ y _ hxy
    have hij := pow_mul_pow_inj h hp hq hxy
    exact Prod.ext hij.1 hij.2
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hlt, i, j, hij⟩ := hm
    rw [hij] at hlt
    exact ⟨(i, j), (mem_below hp hq).mpr hlt, hij.symm⟩

/-- Mintz, Theorems 4 and 7 for the 2,3 sequence: the place of 2^a 3^b, counted from 0. -/
theorem ord_two_three (a b : ℕ) :
    ord 2 3 (2 ^ a * 3 ^ b) = a * b + ∑ k ∈ Finset.range (a + 1), Nat.clog 3 (2 ^ k) +
      ∑ k ∈ Finset.range (b + 1), Nat.clog 2 (3 ^ k) := by
  rw [ord_eq_place (by decide) (by norm_num) (by norm_num),
    place_eq (by norm_num) (by norm_num)]

/-- Mintz's example: 2^5 3^4 = 2592 has place 50 = 5 * 4 + 12 + 18. -/
example : ord 2 3 (2 ^ 5 * 3 ^ 4) = 50 := by
  rw [ord_two_three]
  decide

end SmoothPlace
