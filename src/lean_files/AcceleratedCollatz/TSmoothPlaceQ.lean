-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSmoothClassQ

/-!
  The place of p^a q^b among the numbers p^i q^j, for any two bases p, q > 1, after
  D. J. Mintz, "2,3 sequence as binary mixture", Fibonacci Quart. 19 (1981), 351-360.
  `latticePlace p q a b` is the number of lattice points (i, j) with p^i q^j < p^a q^b.
  It is a b + latticePlace(a, 0) + latticePlace(0, b) (`latticePlace_eq_add`, his
  Theorem 1), and on the baselines the sum over k ≤ a of the number of powers of q below
  p^k (`latticePlace_left`, Theorem 2) and the mirror image (`latticePlace_right`,
  Theorem 3); together `latticePlace_eq` (Theorems 4 and 7). For coprime p and q the
  lattice points are the numbers themselves (`pow_mul_pow_inj`), so this is the place of
  p^a q^b in their increasing list, counted from 0 (`latticeOrd_eq_place`).
  For 2 and an odd q ≥ 3, in the letters of paper sec:sweeps: the number of powers of 2
  below q^k is p2Q(k) for k ≥ 1 (`clog_two_q_pow`), and below 2^j q^i there are
  i j + p2Q(1) + ... + p2Q(i) pairs, plus the sum over k ≤ j of the round-ups of
  k log 2 / log q (`card_smoothBelowAtQ`); for i = 0 these are the pairs of
  `smoothBelowQ` (`smoothBelowAtQ_zero`).
-/

namespace AcceleratedCollatz

variable {p q : ℕ}

/-! ### Two bases p, q > 1 -/

/-- The lattice points (i, j) with p^i q^j < p^a q^b. -/
def latticeBelow (p q a b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (p ^ a * q ^ b) ×ˢ Finset.range (p ^ a * q ^ b)).filter
    (fun x => p ^ x.1 * q ^ x.2 < p ^ a * q ^ b)

/-- (i, j) is in `latticeBelow p q a b` exactly when p^i q^j < p^a q^b. -/
theorem mem_latticeBelow (hp : 1 < p) (hq : 1 < q) {a b : ℕ} {x : ℕ × ℕ} :
    x ∈ latticeBelow p q a b ↔ p ^ x.1 * q ^ x.2 < p ^ a * q ^ b := by
  unfold latticeBelow
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · have h1 : x.1 < p ^ x.1 := Nat.lt_pow_self hp
    have h2 : p ^ x.1 ≤ p ^ x.1 * q ^ x.2 := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    omega
  · have h1 : x.2 < q ^ x.2 := Nat.lt_pow_self hq
    have h2 : q ^ x.2 ≤ p ^ x.1 * q ^ x.2 := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
    omega

/-- The place of p^a q^b: the number of lattice points below (a, b). -/
def latticePlace (p q a b : ℕ) : ℕ := (latticeBelow p q a b).card

/-- A shift of the lattice by (c, d) keeps the order of the values. -/
theorem lattice_shift_lt_iff (hp : 1 < p) (hq : 1 < q) (i j a b c d : ℕ) :
    p ^ (i + c) * q ^ (j + d) < p ^ (a + c) * q ^ (b + d) ↔ p ^ i * q ^ j < p ^ a * q ^ b := by
  have h : ∀ i j, p ^ (i + c) * q ^ (j + d) = p ^ i * q ^ j * (p ^ c * q ^ d) := by
    intro i j
    ring
  have hpos : 0 < p ^ c * q ^ d := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  rw [h, h, Nat.mul_lt_mul_right hpos]

/-- The points below (a + c, b + d) that lie at or beyond (c, d) are as many as the points
    below (a, b). -/
theorem card_latticeBelow_shift (hp : 1 < p) (hq : 1 < q) (a b c d : ℕ) :
    ((latticeBelow p q (a + c) (b + d)).filter (fun x => c ≤ x.1 ∧ d ≤ x.2)).card =
      latticePlace p q a b := by
  apply Finset.card_nbij' (fun x => (x.1 - c, x.2 - d)) (fun x => (x.1 + c, x.2 + d))
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, mem_latticeBelow hp hq] at hx
    rw [Finset.mem_coe, mem_latticeBelow hp hq, ← lattice_shift_lt_iff hp hq _ _ a b c d]
    change p ^ (x.1 - c + c) * q ^ (x.2 - d + d) < p ^ (a + c) * q ^ (b + d)
    rw [Nat.sub_add_cancel hx.2.1, Nat.sub_add_cancel hx.2.2]
    exact hx.1
  · intro x hx
    rw [Finset.mem_coe, mem_latticeBelow hp hq] at hx
    rw [Finset.mem_coe, Finset.mem_filter, mem_latticeBelow hp hq]
    have h := (lattice_shift_lt_iff hp hq _ _ a b c d).mpr hx
    exact ⟨h, Nat.le_add_left _ _, Nat.le_add_left _ _⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    exact Prod.ext (Nat.sub_add_cancel hx.2.1) (Nat.sub_add_cancel hx.2.2)
  · intro x _
    exact Prod.ext (Nat.add_sub_cancel x.1 c) (Nat.add_sub_cancel x.2 d)

/-- Mintz, Theorem 1: the points below (a, b) are those of the a by b rectangle, those at
    or above row b, and those at or right of column a. -/
theorem latticePlace_eq_add (hp : 1 < p) (hq : 1 < q) (a b : ℕ) :
    latticePlace p q a b = a * b + latticePlace p q a 0 + latticePlace p q 0 b := by
  have hrect : (latticeBelow p q a b).filter (fun x => x.1 < a ∧ x.2 < b) =
      Finset.range a ×ˢ Finset.range b := by
    ext x
    rw [Finset.mem_filter, mem_latticeBelow hp hq, Finset.mem_product, Finset.mem_range,
      Finset.mem_range]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    have h1 : p ^ x.1 < p ^ a := Nat.pow_lt_pow_right hp h.1
    have h2 : q ^ x.2 < q ^ b := Nat.pow_lt_pow_right hq h.2
    exact Nat.mul_lt_mul'' h1 h2
  have hup := card_latticeBelow_shift hp hq a 0 0 b
  have hright := card_latticeBelow_shift hp hq 0 b a 0
  rw [Nat.add_zero, Nat.zero_add] at hup hright
  have hnot : ∀ x ∈ latticeBelow p q a b, ¬ (a ≤ x.1 ∧ b ≤ x.2) := by
    intro x hx h
    rw [mem_latticeBelow hp hq] at hx
    have h1 : p ^ a ≤ p ^ x.1 := Nat.pow_le_pow_right (by omega) h.1
    have h2 : q ^ b ≤ q ^ x.2 := Nat.pow_le_pow_right (by omega) h.2
    have h3 := Nat.mul_le_mul h1 h2
    omega
  have h1 := Finset.card_filter_add_card_filter_not (s := latticeBelow p q a b)
    (fun x => x.1 < a ∧ x.2 < b)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (latticeBelow p q a b).filter (fun x => ¬ (x.1 < a ∧ x.2 < b)))
    (fun x => 0 ≤ x.1 ∧ b ≤ x.2)
  have hU : (latticeBelow p q a b).filter
      (fun x => ¬ (x.1 < a ∧ x.2 < b) ∧ (0 ≤ x.1 ∧ b ≤ x.2)) =
      (latticeBelow p q a b).filter (fun x => 0 ≤ x.1 ∧ b ≤ x.2) := by
    apply Finset.filter_congr
    intro x _
    omega
  have hR : (latticeBelow p q a b).filter
      (fun x => ¬ (x.1 < a ∧ x.2 < b) ∧ ¬ (0 ≤ x.1 ∧ b ≤ x.2)) =
      (latticeBelow p q a b).filter (fun x => a ≤ x.1 ∧ 0 ≤ x.2) := by
    apply Finset.filter_congr
    intro x hx
    have h := hnot x hx
    omega
  rw [Finset.filter_filter, Finset.filter_filter, hU, hR, hup, hright] at h2
  rw [hrect, Finset.card_product, Finset.card_range, Finset.card_range] at h1
  unfold latticePlace at h2 ⊢
  omega

/-- No lattice point lies below (0, 0). -/
theorem latticePlace_zero_zero (hp : 1 < p) (hq : 1 < q) : latticePlace p q 0 0 = 0 := by
  unfold latticePlace
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_latticeBelow hp hq, pow_zero, pow_zero, Nat.mul_one] at hx
  have h : 0 < p ^ x.1 * q ^ x.2 := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  omega

/-- One more column: the points below (a + 1, 0) are the points below (a, 0), moved one
    column to the right, and the powers of q below p^(a + 1) in column 0. -/
theorem latticePlace_succ_zero (hp : 1 < p) (hq : 1 < q) (a : ℕ) :
    latticePlace p q (a + 1) 0 = latticePlace p q a 0 + Nat.clog q (p ^ (a + 1)) := by
  have hshift : ((latticeBelow p q (a + 1) 0).filter (fun x => 1 ≤ x.1 ∧ 0 ≤ x.2)).card =
      latticePlace p q a 0 := card_latticeBelow_shift hp hq a 0 1 0
  have hcol : (latticeBelow p q (a + 1) 0).filter (fun x => ¬ (1 ≤ x.1 ∧ 0 ≤ x.2)) =
      (Finset.range (Nat.clog q (p ^ (a + 1)))).image (fun m => (0, m)) := by
    ext x
    rw [Finset.mem_filter, mem_latticeBelow hp hq, Finset.mem_image]
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
  have hsplit := Finset.card_filter_add_card_filter_not (s := latticeBelow p q (a + 1) 0)
    (fun x => 1 ≤ x.1 ∧ 0 ≤ x.2)
  rw [hcol, Finset.card_image_of_injective _ hinj, Finset.card_range] at hsplit
  unfold latticePlace at hshift ⊢
  omega

/-- Mintz, Theorem 2: the place of p^a is the sum over k ≤ a of the number of powers of q
    below p^k. -/
theorem latticePlace_left (hp : 1 < p) (hq : 1 < q) (a : ℕ) :
    latticePlace p q a 0 = ∑ k ∈ Finset.range (a + 1), Nat.clog q (p ^ k) := by
  induction a with
  | zero =>
    rw [latticePlace_zero_zero hp hq, Finset.sum_range_one, pow_zero, Nat.clog_one_right]
  | succ a ih =>
    rw [latticePlace_succ_zero hp hq, ih, Finset.sum_range_succ _ (a + 1)]

/-- Exchanging the two bases mirrors the lattice. -/
theorem latticePlace_swap (hp : 1 < p) (hq : 1 < q) (a b : ℕ) :
    latticePlace p q a b = latticePlace q p b a := by
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro x hx
    rw [Finset.mem_coe, mem_latticeBelow hp hq] at hx
    rw [Finset.mem_coe, mem_latticeBelow hq hp, Prod.fst_swap, Prod.snd_swap, Nat.mul_comm,
      Nat.mul_comm (q ^ b)]
    exact hx
  · intro x hx
    rw [Finset.mem_coe, mem_latticeBelow hq hp] at hx
    rw [Finset.mem_coe, mem_latticeBelow hp hq, Prod.fst_swap, Prod.snd_swap, Nat.mul_comm,
      Nat.mul_comm (p ^ a)]
    exact hx
  · intro x _
    exact Prod.swap_swap x
  · intro x _
    exact Prod.swap_swap x

/-- Mintz, Theorem 3: the place of q^b is the sum over k ≤ b of the number of powers of p
    below q^k. -/
theorem latticePlace_right (hp : 1 < p) (hq : 1 < q) (b : ℕ) :
    latticePlace p q 0 b = ∑ k ∈ Finset.range (b + 1), Nat.clog p (q ^ k) := by
  rw [latticePlace_swap hp hq, latticePlace_left hq hp]

/-- Mintz, Theorems 4 and 7: the place of p^a q^b. -/
theorem latticePlace_eq (hp : 1 < p) (hq : 1 < q) (a b : ℕ) :
    latticePlace p q a b = a * b + ∑ k ∈ Finset.range (a + 1), Nat.clog q (p ^ k) +
      ∑ k ∈ Finset.range (b + 1), Nat.clog p (q ^ k) := by
  rw [latticePlace_eq_add hp hq, latticePlace_left hp hq, latticePlace_right hp hq]

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
noncomputable def latticeOrd (p q n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun m => ∃ i j, m = p ^ i * q ^ j)).card

/-- For coprime p and q, the place of p^a q^b in the increasing list of the numbers
    p^i q^j, counted from 0, is the number of lattice points below (a, b). -/
theorem latticeOrd_eq_place (h : Nat.Coprime p q) (hp : 1 < p) (hq : 1 < q) (a b : ℕ) :
    latticeOrd p q (p ^ a * q ^ b) = latticePlace p q a b := by
  classical
  symm
  apply Finset.card_bij (fun x _ => p ^ x.1 * q ^ x.2)
  · intro x hx
    rw [mem_latticeBelow hp hq] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hx, x.1, x.2, rfl⟩
  · intro x _ y _ hxy
    have hij := pow_mul_pow_inj h hp hq hxy
    exact Prod.ext hij.1 hij.2
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hlt, i, j, hij⟩ := hm
    rw [hij] at hlt
    exact ⟨(i, j), (mem_latticeBelow hp hq).mpr hlt, hij.symm⟩

/-! ### The q-family: the numbers 2^j q^i -/

/-- The number of powers of 2 below q^i is p2Q(i), for odd q ≥ 3 and i ≥ 1. -/
theorem clog_two_q_pow (hodd : Odd q) (hq : 3 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    Nat.clog 2 (q ^ i) = p2Q q i := by
  apply Nat.le_antisymm
  · exact Nat.clog_le_of_le_pow (p2Q_spec hq i).le
  · rw [← Nat.not_lt, ← two_pow_lt_q_pow_iff hodd hq hi, Nat.not_lt]
    exact Nat.le_pow_clog (by norm_num) _

/-- The pairs (j', i') with 2^j' q^i' < 2^j q^i. -/
def smoothBelowAtQ (q j i : ℕ) : Finset (ℕ × ℕ) := latticeBelow 2 q j i

/-- (j', i') is in `smoothBelowAtQ q j i` exactly when 2^j' q^i' < 2^j q^i. -/
theorem mem_smoothBelowAtQ (hq : 3 ≤ q) {j i : ℕ} {x : ℕ × ℕ} :
    x ∈ smoothBelowAtQ q j i ↔ 2 ^ x.1 * q ^ x.2 < 2 ^ j * q ^ i :=
  mem_latticeBelow (by norm_num) (by omega)

/-- For i = 0 these are the pairs of `smoothBelowQ`. -/
theorem smoothBelowAtQ_zero (hq : 3 ≤ q) (B : ℕ) : smoothBelowAtQ q B 0 = smoothBelowQ q B := by
  ext x
  rw [mem_smoothBelowAtQ hq, mem_smoothBelowQ hq, pow_zero, Nat.mul_one]

/-- The number of pairs (j', i') with 2^j' q^i' < 2^j q^i is i j, plus the sum of p2Q(k)
    over 1 ≤ k ≤ i, plus the sum over k ≤ j of the round-ups of k log 2 / log q. -/
theorem card_smoothBelowAtQ (hodd : Odd q) (hq : 3 ≤ q) (j i : ℕ) :
    (smoothBelowAtQ q j i).card = i * j + ∑ k ∈ Finset.range i, p2Q q (k + 1) +
      ∑ k ∈ Finset.range (j + 1), Nat.clog q (2 ^ k) := by
  have h := latticePlace_eq (p := 2) (q := q) (by norm_num) (by omega) j i
  have hsum : ∑ k ∈ Finset.range (i + 1), Nat.clog 2 (q ^ k) =
      ∑ k ∈ Finset.range i, p2Q q (k + 1) := by
    rw [Finset.sum_range_succ', pow_zero, Nat.clog_one_right, Nat.add_zero]
    apply Finset.sum_congr rfl
    intro k _
    exact clog_two_q_pow hodd hq (by omega)
  rw [hsum, Nat.mul_comm] at h
  unfold smoothBelowAtQ
  unfold latticePlace at h
  omega

end AcceleratedCollatz
