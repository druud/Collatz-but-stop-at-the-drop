-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketQ
import AcceleratedCollatz.TBracketDrop

/-!
  Level brackets and value brackets on a trajectory of the map qx + 1 (q ≥ 1), the q-form of
  `TBracketDrop`. `tStepQ q` is (q x + 1)/2 on odd x and x/2 on even x, `tBitsQ q x n` the
  first n parity bits of x. On the word tBitsQ q x n the level ratio lvlQ j / lvlQ i is the
  level of the start y = T^i x after j - i steps (`lvlQ_tBitsQ_eq`), and
  2^k T^k(y) ≥ q^(odd steps) y (`pow_order_mul_le`), so a level at least 2^m lvlQ i keeps
  the value at least 2^m y (`two_pow_mul_le_of_lvlQ_le`). Bracket m of position i
  (`LvlDropQ`, threshold 2^m lvlQ i) and the first value below 2^m y (`ValueDropQ`): a
  value drop forces a level drop no later (`exists_lvlDropQ_le_of_valueDropQ`); with the
  width property of y for bracket m (`WidthAtQ`) the two coincide
  (`lvlDropQ_iff_valueDropQ`). For q = 3 and m = 0 this is `lvlDrop_iff_isFirstDrop`
  (`tStepQ_three`, `tBitsQ_three`, `valueDropQ_zero`, `lvlDropQ_three`). For q ≥ 5 the
  width property can fail: 13 lies on a cycle of 5x + 1 (`tStepQ_five_cycle`).
-/

namespace AcceleratedCollatz

variable {q x n i j m : ℕ}

/-- The map qx + 1: (q x + 1)/2 on odd x, x/2 on even x. -/
def tStepQ (q x : ℕ) : ℕ := if x % 2 = 1 then (q * x + 1) / 2 else x / 2

/-- First n parity bits of x under `tStepQ q` (true = odd). -/
def tBitsQ (q : ℕ) : ℕ → ℕ → List Bool
  | _, 0 => []
  | x, n + 1 => decide (x % 2 = 1) :: tBitsQ q (tStepQ q x) n

/-- The trajectory: T^i x. -/
def tTrajQ (q x i : ℕ) : ℕ := (tStepQ q)^[i] x

theorem tStepQ_three : tStepQ 3 = tStep := rfl

theorem tBitsQ_three : tBitsQ 3 = tBits := by
  funext x n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [tBitsQ, tBits, tStepQ_three, ih]

@[simp]
theorem length_tBitsQ (q x n : ℕ) : (tBitsQ q x n).length = n := by
  induction n generalizing x with
  | zero => simp [tBitsQ]
  | succ n ih => simp [tBitsQ, ih]

theorem tBitsQ_add (q x a b : ℕ) :
    tBitsQ q x (a + b) = tBitsQ q x a ++ tBitsQ q ((tStepQ q)^[a] x) b := by
  induction a generalizing x with
  | zero => simp [tBitsQ]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [tBitsQ, List.cons_append]
    rw [ih (tStepQ q x), Function.iterate_succ_apply]

theorem tBitsQ_take (q x : ℕ) (hm : m ≤ n) : (tBitsQ q x n).take m = tBitsQ q x m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [tBitsQ_add, List.take_left' (length_tBitsQ q x m)]

theorem tTrajQ_add (q x i m : ℕ) : tTrajQ q x (i + m) = (tStepQ q)^[m] (tTrajQ q x i) := by
  change (tStepQ q)^[i + m] x = (tStepQ q)^[m] ((tStepQ q)^[i] x)
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- 2^k T^k(y) is at least q^(odd steps) y. -/
theorem pow_order_mul_le (q : ℕ) : ∀ (k y : ℕ),
    q ^ order (tBitsQ q y k) * y ≤ 2 ^ k * (tStepQ q)^[k] y
  | 0, y => by simp [tBitsQ, order]
  | k + 1, y => by
    have ih := pow_order_mul_le q k (tStepQ q y)
    have hstep : q ^ (if decide (y % 2 = 1) then 1 else 0) * y ≤ 2 * tStepQ q y := by
      unfold tStepQ
      by_cases hy : y % 2 = 1
      · simp only [hy, decide_true, ↓reduceIte, pow_one]
        omega
      · simp only [hy, decide_false, Bool.false_eq_true, ↓reduceIte, pow_zero, one_mul]
        omega
    simp only [tBitsQ, order_cons, Function.iterate_succ_apply, pow_add]
    calc q ^ order (tBitsQ q (tStepQ q y) k) * q ^ (if decide (y % 2 = 1) then 1 else 0) * y
        = q ^ order (tBitsQ q (tStepQ q y) k) * (q ^ (if decide (y % 2 = 1) then 1 else 0) * y) :=
          by ring
      _ ≤ q ^ order (tBitsQ q (tStepQ q y) k) * (2 * tStepQ q y) := Nat.mul_le_mul_left _ hstep
      _ = 2 * (q ^ order (tBitsQ q (tStepQ q y) k) * tStepQ q y) := by ring
      _ ≤ 2 * (2 ^ k * (tStepQ q)^[k] (tStepQ q y)) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ k * 2 ^ 1 * (tStepQ q)^[k] (tStepQ q y) := by ring

/-- Level after j steps = level after i steps times the level of T^i x after j - i steps. -/
theorem lvlQ_tBitsQ_eq (hij : i ≤ j) (hjn : j ≤ n) :
    lvlQ q (tBitsQ q x n) j =
      lvlQ q (tBitsQ q x n) i * seqProductQ q (tBitsQ q (tTrajQ q x i) (j - i)) := by
  unfold lvlQ
  rw [tBitsQ_take q x hjn, tBitsQ_take q x (hij.trans hjn), ← seqProductQ_append]
  have h := tBitsQ_add q x i (j - i)
  rw [Nat.add_sub_cancel' hij] at h
  rw [h]
  rfl

/-- A level at least 2^m lvlQ i gives a value at least 2^m T^i x. -/
theorem two_pow_mul_le_of_lvlQ_le (hq : 0 < q) {k : ℕ} (hik : i ≤ k) (hkn : k ≤ n)
    (h : 2 ^ m * lvlQ q (tBitsQ q x n) i ≤ lvlQ q (tBitsQ q x n) k) :
    2 ^ m * tTrajQ q x i ≤ tTrajQ q x k := by
  set y := tTrajQ q x i
  set w := tBitsQ q y (k - i)
  rw [lvlQ_tBitsQ_eq hik hkn, mul_comm (2 ^ m : ℚ)] at h
  have h1 : (2 : ℚ) ^ m ≤ seqProductQ q w :=
    le_of_mul_le_mul_left h (lvlQ_pos hq _ _)
  have hpw : (2 : ℚ) ^ m * 2 ^ (k - i) ≤ (q : ℚ) ^ order w := by
    rw [← seqProductQ_mul_pow, length_tBitsQ]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hpn : 2 ^ m * 2 ^ (k - i) ≤ q ^ order w := by
    exact_mod_cast hpw
  have hN := pow_order_mul_le q (k - i) y
  have hk : tTrajQ q x k = (tStepQ q)^[k - i] y := by
    rw [← tTrajQ_add, Nat.add_sub_cancel' hik]
  rw [hk]
  have hle : 2 ^ (k - i) * (2 ^ m * y) ≤ 2 ^ (k - i) * (tStepQ q)^[k - i] y := by
    calc 2 ^ (k - i) * (2 ^ m * y) = 2 ^ m * 2 ^ (k - i) * y := by ring
      _ ≤ q ^ order w * y := Nat.mul_le_mul_right _ hpn
      _ ≤ _ := hN
  exact Nat.le_of_mul_le_mul_left hle (by positivity)

/-- A value below 2^m T^i x gives a level below 2^m lvlQ i. -/
theorem lvlQ_lt_of_tTrajQ_lt (hq : 0 < q) {k : ℕ} (hik : i ≤ k) (hkn : k ≤ n)
    (h : tTrajQ q x k < 2 ^ m * tTrajQ q x i) :
    lvlQ q (tBitsQ q x n) k < 2 ^ m * lvlQ q (tBitsQ q x n) i := by
  by_contra hle
  push Not at hle
  exact absurd (two_pow_mul_le_of_lvlQ_le hq hik hkn hle) (not_le.mpr h)

/-- j is the first index after i with a j < 2^m a i. -/
def ValueDropQ (a : ℕ → ℕ) (i m j : ℕ) : Prop :=
  i < j ∧ a j < 2 ^ m * a i ∧ ∀ k, i < k → k < j → 2 ^ m * a i ≤ a k

/-- For m = 0 a value drop is a first drop. -/
theorem valueDropQ_zero (a : ℕ → ℕ) : ValueDropQ a i 0 j ↔ IsFirstDrop a i j := by
  simp [ValueDropQ, IsFirstDrop]

/-- Any level below 2^m lvlQ i after i gives a close of bracket m no later. -/
theorem exists_lvlDropQ_le_of_lt {s : List Bool} (hij : i < j)
    (hj : lvlQ q s j < 2 ^ m * lvlQ q s i) : ∃ j', LvlDropQ q s i m j' ∧ j' ≤ j := by
  classical
  have hex : ∃ l, i < l ∧ lvlQ q s l < 2 ^ m * lvlQ q s i := ⟨j, hij, hj⟩
  refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩,
    Nat.find_min' hex ⟨hij, hj⟩⟩
  intro k hk hik
  by_contra hlt
  exact Nat.find_min hex hk ⟨hik, not_le.mp hlt⟩

/-- A value drop below 2^m T^i x at j ≤ n: a close of bracket m no later. -/
theorem exists_lvlDropQ_le_of_valueDropQ (hq : 0 < q) (h : ValueDropQ (tTrajQ q x) i m j)
    (hjn : j ≤ n) : ∃ j', LvlDropQ q (tBitsQ q x n) i m j' ∧ j' ≤ j :=
  exists_lvlDropQ_le_of_lt h.1 (lvlQ_lt_of_tTrajQ_lt hq h.1.le hjn h.2.1)

/-- Width property of y for bracket m: a word of y whose nonempty proper prefixes keep the
    level at least 2^m and whose whole level is below 2^m takes y below 2^m y. -/
def WidthAtQ (q m y : ℕ) : Prop :=
  ∀ k, 1 ≤ k → (∀ l, 1 ≤ l → l < k → (2 : ℚ) ^ m ≤ seqProductQ q (tBitsQ q y l)) →
    seqProductQ q (tBitsQ q y k) < 2 ^ m → (tStepQ q)^[k] y < 2 ^ m * y

/-- With the width property of T^i x for bracket m, a close of bracket m is a value drop. -/
theorem valueDropQ_of_lvlDropQ (hq : 0 < q) (hW : WidthAtQ q m (tTrajQ q x i))
    (h : LvlDropQ q (tBitsQ q x n) i m j) (hjn : j ≤ n) : ValueDropQ (tTrajQ q x) i m j := by
  obtain ⟨hij, hlt, hmin⟩ := h
  refine ⟨hij, ?_, fun k hik hkj => two_pow_mul_le_of_lvlQ_le hq hik.le (by omega)
    (hmin k hkj hik)⟩
  have hpos := lvlQ_pos hq (tBitsQ q x n) i
  have hpre : ∀ l, 1 ≤ l → l < j - i →
      (2 : ℚ) ^ m ≤ seqProductQ q (tBitsQ q (tTrajQ q x i) l) := by
    intro l hl1 hl
    have hge := hmin (i + l) (by omega) (by omega)
    rw [lvlQ_tBitsQ_eq (by omega : i ≤ i + l) (by omega), Nat.add_sub_cancel_left,
      mul_comm (2 ^ m : ℚ)] at hge
    exact le_of_mul_le_mul_left hge hpos
  have hend : seqProductQ q (tBitsQ q (tTrajQ q x i) (j - i)) < 2 ^ m := by
    rw [lvlQ_tBitsQ_eq hij.le hjn, mul_comm (2 ^ m : ℚ)] at hlt
    exact lt_of_mul_lt_mul_left hlt hpos.le
  have hd := hW (j - i) (by omega) hpre hend
  rw [← tTrajQ_add, Nat.add_sub_cancel' hij.le] at hd
  exact hd

/-- With the width property of T^i x for bracket m, the closes of bracket m of position i
    and the first values below 2^m T^i x coincide up to n. -/
theorem lvlDropQ_iff_valueDropQ (hq : 0 < q) (hW : WidthAtQ q m (tTrajQ q x i))
    (hjn : j ≤ n) : LvlDropQ q (tBitsQ q x n) i m j ↔ ValueDropQ (tTrajQ q x) i m j := by
  refine ⟨fun h => valueDropQ_of_lvlDropQ hq hW h hjn, ?_⟩
  rintro ⟨hij, hlt, hmin⟩
  refine ⟨hij, lvlQ_lt_of_tTrajQ_lt hq hij.le hjn hlt, ?_⟩
  intro k hkj hik
  by_contra hk
  push Not at hk
  obtain ⟨j', hj', hj'k⟩ := exists_lvlDropQ_le_of_lt hik hk
  have hv := valueDropQ_of_lvlDropQ hq hW hj' (by omega)
  exact absurd (hmin j' hv.1 (by omega)) (not_le.mpr hv.2.1)

/-- 13 lies on a cycle of 5x + 1 (13, 33, 83, 208, 104, 52, 26): its values never fall
    below 13, so the width property fails there for q = 5. -/
theorem tStepQ_five_cycle : (tStepQ 5)^[7] 13 = 13 := by
  decide

end AcceleratedCollatz
