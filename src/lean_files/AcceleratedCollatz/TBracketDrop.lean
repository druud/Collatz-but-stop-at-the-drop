-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracket
import AcceleratedCollatz.TCovering
import AcceleratedCollatz.TNest
import AcceleratedCollatz.TWidth

/-!
  Level brackets and value brackets on a trajectory. On the word tBits x n the
  level ratio lvl j / lvl i is the level of the start y = T^i x after j - i steps
  (`lvl_tBits_eq`). A level at least lvl i keeps the value at least y
  (`tTraj_le_of_lvl_le`), so a value drop from i forces a level drop no later
  (`exists_lvlDrop_le_of_isFirstDrop`). With the width identity at y (`WidthAt`)
  the first level drop and the first value drop from i coincide
  (`lvlDrop_iff_isFirstDrop`); under `WidthIdentity` for every start y > 1
  (`lvlDrop_iff_isFirstDrop_of_width`). Inside an admissible word tBits x n, x > 0,
  under `WidthIdentity`, every level close is the drop of its start, with
  drop(1) = 1 (`lvlDrop_iff_isTDrop`).
-/

namespace AcceleratedCollatz

variable {x n i j : ℕ}

/-- Width identity at y: y drops at its coefficient stopping time. -/
def WidthAt (y : ℕ) : Prop :=
  ∀ m, Admissible (tBits y m) → tStep^[m] y < y

theorem tTraj_add (x i m : ℕ) : tTraj x (i + m) = tStep^[m] (tTraj x i) := by
  change tStep^[i + m] x = tStep^[m] (tStep^[i] x)
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- Level after j steps = level after i steps times the level of T^i x after j - i
    steps. -/
theorem lvl_tBits_eq (hij : i ≤ j) (hjn : j ≤ n) :
    lvl (tBits x n) j = lvl (tBits x n) i * seqProduct (tBits (tTraj x i) (j - i)) := by
  unfold lvl
  rw [tBits_take x n j hjn, tBits_take x n i (hij.trans hjn), ← seqProduct_append]
  have h := tBits_add x i (j - i)
  rw [Nat.add_sub_cancel' hij] at h
  rw [h]

/-- A level at least lvl i gives a value at least T^i x. -/
theorem tTraj_le_of_lvl_le {k : ℕ} (hik : i ≤ k) (hkn : k ≤ n)
    (h : lvl (tBits x n) i ≤ lvl (tBits x n) k) : tTraj x i ≤ tTraj x k := by
  rw [lvl_tBits_eq hik hkn] at h
  have h1 : 1 ≤ seqProduct (tBits (tTraj x i) (k - i)) :=
    (le_mul_iff_one_le_right (lvl_pos _ _)).mp h
  have hpow : 2 ^ (k - i) ≤ 3 ^ order (tBits (tTraj x i) (k - i)) := by
    have hn := (seqProduct_lt_one_iff _).not.mp (not_lt.mpr h1)
    rw [length_tBits] at hn
    exact not_lt.mp hn
  have hN := tStep_iterate_nForm (k - i) (tTraj x i)
  have hle : 2 ^ (k - i) * tTraj x i ≤ 2 ^ (k - i) * tStep^[k - i] (tTraj x i) := by
    rw [hN]
    calc 2 ^ (k - i) * tTraj x i
        ≤ 3 ^ order (tBits (tTraj x i) (k - i)) * tTraj x i := Nat.mul_le_mul_right _ hpow
      _ ≤ _ := Nat.le_add_right _ _
  have hk : tTraj x k = tStep^[k - i] (tTraj x i) := by
    rw [← tTraj_add, Nat.add_sub_cancel' hik]
  rw [hk]
  exact Nat.le_of_mul_le_mul_left hle (by positivity)

/-- A value below T^i x gives a level below lvl i. -/
theorem lvl_lt_of_tTraj_lt {k : ℕ} (hik : i ≤ k) (hkn : k ≤ n)
    (h : tTraj x k < tTraj x i) : lvl (tBits x n) k < lvl (tBits x n) i := by
  by_contra hle
  push Not at hle
  exact absurd (tTraj_le_of_lvl_le hik hkn hle) (not_le.mpr h)

/-- Any level below lvl i after i gives a first level drop no later than it. -/
theorem exists_lvlDrop_le {s : List Bool} (hij : i < j) (hj : lvl s j < lvl s i) :
    ∃ j', LvlDrop s i j' ∧ j' ≤ j := by
  classical
  have hex : ∃ m, i < m ∧ lvl s m < lvl s i := ⟨j, hij, hj⟩
  refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩,
    Nat.find_min' hex ⟨hij, hj⟩⟩
  intro k hk hik
  by_contra hlt
  exact Nat.find_min hex hk ⟨hik, not_le.mp hlt⟩

/-- A first value drop from i at j ≤ n: a first level drop from i no later. -/
theorem exists_lvlDrop_le_of_isFirstDrop (h : IsFirstDrop (tTraj x) i j) (hjn : j ≤ n) :
    ∃ j', LvlDrop (tBits x n) i j' ∧ j' ≤ j :=
  exists_lvlDrop_le h.1 (lvl_lt_of_tTraj_lt h.1.le hjn h.2.1)

/-- The level of a nonempty word is not 1. -/
theorem seqProduct_tBits_ne_one (y m : ℕ) (hm : 1 ≤ m) : seqProduct (tBits y m) ≠ 1 := by
  intro heq
  have h1 := (one_lt_seqProduct_iff (tBits y m)).not.mp (by simp [heq])
  have h2 := (seqProduct_lt_one_iff (tBits y m)).not.mp (by simp [heq])
  rw [length_tBits] at h1 h2
  exact two_pow_ne_three_pow m (order (tBits y m)) hm (by omega)

/-- With the width identity at T^i x, a first level drop is a first value drop. -/
theorem isFirstDrop_of_lvlDrop (hW : WidthAt (tTraj x i)) (h : LvlDrop (tBits x n) i j)
    (hjn : j ≤ n) : IsFirstDrop (tTraj x) i j := by
  obtain ⟨hij, hlt, hmin⟩ := h
  refine ⟨hij, ?_, fun k hik hkj => tTraj_le_of_lvl_le hik.le (by omega) (hmin k hkj hik)⟩
  have hA : Admissible (tBits (tTraj x i) (j - i)) := by
    refine ⟨?_, ?_⟩
    · intro m hm1 hm
      rw [length_tBits] at hm
      rw [tBits_take _ _ _ hm.le]
      have hge : lvl (tBits x n) i ≤ lvl (tBits x n) (i + m) :=
        hmin (i + m) (by omega) (by omega)
      rw [lvl_tBits_eq (by omega : i ≤ i + m) (by omega), Nat.add_sub_cancel_left] at hge
      have h1 : 1 ≤ seqProduct (tBits (tTraj x i) m) :=
        (le_mul_iff_one_le_right (lvl_pos _ _)).mp hge
      exact lt_of_le_of_ne h1 (Ne.symm (seqProduct_tBits_ne_one _ m hm1))
    · rw [lvl_tBits_eq hij.le hjn] at hlt
      exact (mul_lt_iff_lt_one_right (lvl_pos _ _)).mp hlt
  have hd := hW _ hA
  rw [← tTraj_add, Nat.add_sub_cancel' hij.le] at hd
  exact hd

/-- With the width identity at T^i x, first level drops and first value drops from i
    coincide up to n. -/
theorem lvlDrop_iff_isFirstDrop (hW : WidthAt (tTraj x i)) (hjn : j ≤ n) :
    LvlDrop (tBits x n) i j ↔ IsFirstDrop (tTraj x) i j := by
  refine ⟨fun h => isFirstDrop_of_lvlDrop hW h hjn, ?_⟩
  rintro ⟨hij, hlt, hmin⟩
  refine ⟨hij, lvl_lt_of_tTraj_lt hij.le hjn hlt, ?_⟩
  intro k hkj hik
  by_contra hk
  push Not at hk
  obtain ⟨j', hj', hj'k⟩ := exists_lvlDrop_le hik hk
  have hv := isFirstDrop_of_lvlDrop hW hj' (by omega)
  exact absurd (hmin j' hv.1 (by omega)) (not_le.mpr hv.2.1)

/-- Under `WidthIdentity`, first level drops and first value drops coincide from every
    start T^i x > 1. -/
theorem lvlDrop_iff_isFirstDrop_of_width (hW : WidthIdentity) (hy : 1 < tTraj x i)
    (hjn : j ≤ n) : LvlDrop (tBits x n) i j ↔ IsFirstDrop (tTraj x) i j :=
  lvlDrop_iff_isFirstDrop (fun m hA => hW _ m hy hA) hjn

/-- A first drop from i is the first drop of T^i x from 0, shifted by i. -/
theorem isFirstDrop_tTraj_iff (hij : i < j) :
    IsFirstDrop (tTraj x) i j ↔ IsFirstDrop (tTraj (tTraj x i)) 0 (j - i) := by
  have h : ∀ m, tTraj (tTraj x i) m = tTraj x (i + m) := fun m => (tTraj_add x i m).symm
  have hj : tTraj (tTraj x i) (j - i) = tTraj x j := by
    rw [h, Nat.add_sub_cancel' hij.le]
  have h0 : tTraj (tTraj x i) 0 = tTraj x i := rfl
  unfold IsFirstDrop
  rw [hj, h0]
  constructor
  · rintro ⟨_, hlt, hmin⟩
    refine ⟨by omega, hlt, fun k hk hkj => ?_⟩
    rw [h]
    exact hmin (i + k) (by omega) (by omega)
  · rintro ⟨_, hlt, hmin⟩
    refine ⟨hij, hlt, fun k hik hkj => ?_⟩
    have hk := hmin (k - i) (by omega) (by omega)
    rw [h, Nat.add_sub_cancel' hik.le] at hk
    exact hk

/-- The admissible word of 1 is 10. -/
theorem eq_two_of_admissible_one (hA : Admissible (tBits 1 n)) : n = 2 := by
  have hn := hA.lt_one
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | rfl | h3
  · simp [tBits, seqProduct] at hn
  · have hb : tBits 1 1 = [true] := by
      decide
    rw [hb] at hn
    norm_num [seqProduct, factor] at hn
  · rfl
  · have hlen : 2 < (tBits 1 n).length := by
      rw [length_tBits]
      omega
    have hp := hA.prefix_gt 2 (by norm_num) hlen
    rw [tBits_take 1 n 2 (by omega)] at hp
    have hb : tBits 1 2 = [true, false] := by
      decide
    rw [hb] at hp
    norm_num [seqProduct, factor] at hp

theorem isTDrop_iff_of_ne_one {y m : ℕ} (hy : y ≠ 1) :
    IsTDrop y m ↔ IsFirstDrop (tTraj y) 0 m := by
  simp [IsTDrop, hy]

/-- Inside an admissible word of x > 0, under `WidthIdentity`, the level close of
    position i is the drop of T^i x (drop(1) = 1). -/
theorem lvlDrop_iff_isTDrop (hW : WidthIdentity) (hx : 0 < x) (hA : Admissible (tBits x n))
    (hi : i < n) (hjn : j ≤ n) :
    LvlDrop (tBits x n) i j ↔ i < j ∧ IsTDrop (tTraj x i) (j - i) := by
  rcases (by omega : x = 1 ∨ 1 < x) with rfl | hx1
  · have hn := eq_two_of_admissible_one hA
    subst hn
    have hb : tBits 1 2 = [true, false] := by
      decide
    rw [hb]
    have hT1 : tTraj 1 1 = 2 := tTraj_one.1
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · have hT0 : tTraj 1 0 = 1 := rfl
      rw [hT0]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · simp [LvlDrop]
      · norm_num [LvlDrop, IsTDrop, lvl, seqProduct, factor]
      · simp only [LvlDrop, IsTDrop, lvl, seqProduct]
        refine iff_of_true ⟨by norm_num, by norm_num [factor], fun k hk hk0 => ?_⟩
          ⟨by norm_num, by simp⟩
        interval_cases k
        norm_num [factor]
    · rw [hT1]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · simp [LvlDrop]
      · simp [LvlDrop]
      · have hT2 : tTraj 2 1 = 1 := by
          decide
        rw [isTDrop_iff_of_ne_one (by norm_num)]
        refine iff_of_true ⟨by norm_num, ?_, fun k hk hk1 => by omega⟩
          ⟨by norm_num, by norm_num, ?_, fun k hk hk0 => by omega⟩
        · norm_num [lvl, seqProduct, factor]
        · change tTraj 2 1 < 2
          rw [hT2]
          norm_num
  · have hy : 1 < tTraj x i := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact hx1
      · have hs : tBits x (tBits x n).length = tBits x n := by
          rw [length_tBits]
        have hlen : i < (tBits x n).length := by
          rw [length_tBits]
          exact hi
        have := no_drop_before _ x hA hs hx i hpos hlen
        change 1 < tStep^[i] x
        omega
    rw [lvlDrop_iff_isFirstDrop_of_width hW hy hjn, isTDrop_iff_of_ne_one (by omega)]
    constructor
    · intro h
      exact ⟨h.1, (isFirstDrop_tTraj_iff h.1).mp h⟩
    · rintro ⟨hij, h⟩
      exact (isFirstDrop_tTraj_iff hij).mpr h

end AcceleratedCollatz
