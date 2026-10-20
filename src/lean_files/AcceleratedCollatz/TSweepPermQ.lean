-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBinomial
import AcceleratedCollatz.TSweepQ
import AcceleratedCollatz.TSweepZ

/-!
  The sweep of the q-family as a permutation (odd q ≥ 3). Integer weights c, d with
  d (p2Q(a) - 1) < c a < d p2Q(a) for all 1 ≤ a ≤ n + 1 (`exists_weightsQ`) order the
  lattice points of Order n like the levels q^o / 2^j (`q_pow_lt_iff_weights`). With
  the weights c - d and -d, an admissible word of Order n without its final halving
  is a Dyck word (`dropLast_mem_dyckSetQ`), and its sweep is the integer sweep of that
  Dyck word followed by the final halving (`sweepQ_eq_sweepZ`). Under
  `SweepBijective` the sweep permutes `admSetQ q n` for every n (`sweepQ_bijOn`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Integer weights c, d strictly between (p2(a) - 1)/a and p2(a)/a for 1 ≤ a ≤ n + 1. -/
theorem exists_weightsQ (hq : 3 ≤ q) (n : ℕ) : ∃ c d : ℤ, 0 < d ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
    d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a := by
  have hS : (Finset.Icc 1 (n + 1)).Nonempty := ⟨1, by simp⟩
  set lo := (Finset.Icc 1 (n + 1)).sup' hS (fun a => ((p2Q q a : ℚ) - 1) / a) with hlo
  set hi := (Finset.Icc 1 (n + 1)).inf' hS (fun a => (p2Q q a : ℚ) / a) with hhi
  have hlohi : lo < hi := by
    rw [hlo, Finset.sup'_lt_iff]
    intro a ha
    rw [hhi, Finset.lt_inf'_iff]
    intro b hb
    simp only [Finset.mem_Icc] at ha hb
    have hapos : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
    have hbpos : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [div_lt_div_iff₀ hapos hbpos]
    have hn := p2Q_sub_one_mul_lt hq (b := b) (by omega : 1 ≤ a)
    have hp := one_le_p2Q q a
    have hq : (((p2Q q a - 1) * b : ℕ) : ℚ) < ((a * p2Q q b : ℕ) : ℚ) := by
      exact_mod_cast hn
    push_cast [Nat.cast_sub hp] at hq
    linarith
  set r := (lo + hi) / 2 with hr
  have hrlo : lo < r := by
    rw [hr]
    linarith
  have hrhi : r < hi := by
    rw [hr]
    linarith
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hrq : r = (r.num : ℚ) / r.den := (Rat.num_div_den r).symm
  refine ⟨r.num, r.den, by exact_mod_cast r.den_pos, fun a ha1 ha2 => ?_⟩
  have haS : a ∈ Finset.Icc 1 (n + 1) := by simp [ha1, ha2]
  have hapos : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  have hl : ((p2Q q a : ℚ) - 1) / a < r :=
    lt_of_le_of_lt (Finset.le_sup' (fun a => ((p2Q q a : ℚ) - 1) / a) haS) hrlo
  have hh : r < (p2Q q a : ℚ) / a :=
    lt_of_lt_of_le hrhi (Finset.inf'_le (fun a => (p2Q q a : ℚ) / a) haS)
  rw [div_lt_iff₀ hapos, hrq, div_mul_eq_mul_div, lt_div_iff₀ hden] at hl
  rw [lt_div_iff₀ hapos, hrq, div_mul_eq_mul_div, div_lt_iff₀ hden] at hh
  constructor
  · have hq : ((r.den * ((p2Q q a : ℤ) - 1) : ℤ) : ℚ) < ((r.num * a : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hq
  · have hq : ((r.num * a : ℤ) : ℚ) < ((r.den * p2Q q a : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hq

/-- The weights order the lattice points of Order n like the 3-smooth levels. -/
theorem q_pow_lt_iff_weights (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {o o' j j' : ℕ} (ho : o ≤ n) (ho' : o' ≤ n) :
    q ^ o * 2 ^ j' < q ^ o' * 2 ^ j ↔ c * o - d * j < c * o' - d * j' := by
  rcases le_or_gt o' o with hle | hlt
  · obtain ⟨a, rfl⟩ : ∃ a, o = o' + a := ⟨o - o', by omega⟩
    have hcancel : q ^ (o' + a) * 2 ^ j' < q ^ o' * 2 ^ j ↔ q ^ a * 2 ^ j' < 2 ^ j := by
      rw [pow_add, mul_assoc, Nat.mul_lt_mul_left (by positivity)]
    rw [hcancel]
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rw [ha0, pow_zero, one_mul, Nat.pow_lt_pow_iff_right (by norm_num)]
      push_cast
      constructor
      · intro h
        have : (j' : ℤ) < j := by exact_mod_cast h
        nlinarith
      · intro h
        by_contra hj
        push Not at hj
        have : (j : ℤ) ≤ j' := by exact_mod_cast hj
        nlinarith
    · rw [q_pow_mul_lt_iff hq]
      obtain ⟨h1, h2⟩ := hcd a (by omega) (by omega)
      push_cast
      constructor
      · intro h
        have hz : (p2Q q a : ℤ) ≤ (j : ℤ) - j' := by omega
        have := mul_le_mul_of_nonneg_left hz (le_of_lt hd)
        nlinarith
      · intro h
        by_contra hz
        have hz' : (j : ℤ) - j' ≤ (p2Q q a : ℤ) - 1 := by omega
        have := mul_le_mul_of_nonneg_left hz' (le_of_lt hd)
        nlinarith
  · obtain ⟨a, rfl⟩ : ∃ a, o' = o + a := ⟨o' - o, by omega⟩
    have hcancel : q ^ o * 2 ^ j' < q ^ (o + a) * 2 ^ j ↔ 2 ^ j' < q ^ a * 2 ^ j := by
      rw [pow_add, mul_assoc, Nat.mul_lt_mul_left (by positivity)]
    rw [hcancel, lt_q_pow_mul_iff hodd hq (by omega)]
    obtain ⟨h1, h2⟩ := hcd a (by omega) (by omega)
    push_cast
    constructor
    · intro h
      have hz : (j' : ℤ) - j ≤ (p2Q q a : ℤ) - 1 := by omega
      have := mul_le_mul_of_nonneg_left hz (le_of_lt hd)
      nlinarith
    · intro h
      by_contra hz
      have hz' : (p2Q q a : ℤ) ≤ (j' : ℤ) - j := by omega
      have := mul_le_mul_of_nonneg_left hz' (le_of_lt hd)
      nlinarith

/-- Levels of an admissible word of Order n compare like their integer levels. -/
theorem lvlQ_lt_iff_lvlZ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {s : List Bool} (hs : order s = n) {i k : ℕ} (hi : i ≤ s.length) (hk : k ≤ s.length) :
    lvlQ q s i < lvlQ q s k ↔ lvlZ (c - d) (-d) s i < lvlZ (c - d) (-d) s k := by
  rw [lvlZ_weights c d hi, lvlZ_weights c d hk]
  have hoi : order (s.take i) ≤ n := hs ▸ order_take_le s i
  have hok : order (s.take k) ≤ n := hs ▸ order_take_le s k
  rw [← q_pow_lt_iff_weights hodd hq hd hcd hoi hok]
  have h1 := lvlQ_mul_pow q hi
  have h2 := lvlQ_mul_pow q hk
  have hp1 : (0 : ℚ) < 2 ^ i := by positivity
  have hp2 : (0 : ℚ) < 2 ^ k := by positivity
  have hcast : (q ^ order (s.take i) * 2 ^ k < q ^ order (s.take k) * 2 ^ i) ↔
      ((q : ℚ) ^ order (s.take i) * 2 ^ k < q ^ order (s.take k) * 2 ^ i) := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  rw [hcast, ← h1, ← h2]
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h (mul_pos hp1 hp2)
    nlinarith
  · intro h
    by_contra hle
    push Not at hle
    have := mul_le_mul_of_nonneg_right hle (le_of_lt (mul_pos hp1 hp2))
    nlinarith

/-- An admissible word ends with its final halving. -/
theorem exists_eq_append_falseQ (hq : 3 ≤ q) {n : ℕ} {s : List Bool} (hs : s ∈ admSetQ q n) :
    ∃ w, s = w ++ [false] := by
  have hA := ((mem_admSetQ (by omega) _ s).mp hs).1
  have hne : s ≠ [] := by
    intro h
    have := hA.lt_one
    rw [h] at this
    simp [seqProductQ] at this
  refine ⟨s.dropLast, ?_⟩
  have h := (List.dropLast_append_getLast hne).symm
  rw [admissibleQ_last_false (by omega) hA hne] at h
  exact h

/-- Without its final halving, an admissible word has positive integer levels. -/
theorem lvlZ_posQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ w.length) : 0 < lvlZ (c - d) (-d) w m := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hlen : (w ++ [false]).length = w.length + 1 := by simp
  have hgt : 1 < lvlQ q (w ++ [false]) m := hA.prefix_gt m hm1 (by omega)
  have hlt : lvlQ q (w ++ [false]) 0 < lvlQ q (w ++ [false]) m := by
    rw [lvlQ_zero q]
    exact hgt
  rw [lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (by omega) (by omega), lvlZ_zero,
    lvlZ_append_false _ _ hm] at hlt
  exact hlt

/-- Without its final halving, an admissible word of Order n is a Dyck word. -/
theorem dropLast_mem_dyckSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    w ∈ dyckSet (c - d) (-d) n (w.length - n) := by
  have hord := ((mem_admSetQ (by omega) _ _).mp hs).2
  have htrue : w.count true = n := by
    rw [← hord, order_eq_count_true, List.count_append]
    simp
  refine ⟨htrue, ?_, ?_⟩
  · have h := count_true_add_count_false w
    omega
  · intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, lvlZ_zero]
    · exact le_of_lt (lvlZ_posQ hodd hq hd hcd hs hpos hm)

/-- The sweep of an admissible word sorts like the integer sweep of its Dyck part. -/
theorem sweepIdxQ_eq (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    sweepIdxQ q (w ++ [false]) = sweepIdxZ (c - d) (-d) w ++ [w.length] := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  set s := w ++ [false] with hsdef
  have hlen : s.length = w.length + 1 := by simp [hsdef]
  have hmemZ : ∀ {i}, i ∈ sweepIdxZ (c - d) (-d) w → i < w.length := by
    intro i hi
    rw [(sweepIdxZ_perm _ _ w).mem_iff, List.mem_range] at hi
    exact hi
  apply List.Perm.eq_of_pairwise (le := fun i k => lvlQ q s (k + 1) < lvlQ q s (i + 1))
  · intro a b _ _ hab hba
    exact (lt_asymm hab hba).elim
  · refine ((sweepIdxQ_pairwise q s).and (sweepIdxQ_nodup q s)).imp_of_mem ?_
    intro a b ha hb h
    have ha' := mem_sweepIdxQ.mp ha
    have hb' := mem_sweepIdxQ.mp hb
    exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
  · rw [List.pairwise_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · refine ((sweepIdxZ_pairwise _ _ w).and (sweepIdxZ_nodup _ _ w)).imp_of_mem ?_
      intro a b ha hb h
      have ha' := hmemZ ha
      have hb' := hmemZ hb
      have hpa := lvlZ_posQ hodd hq hd hcd hs (m := a + 1) (by omega) (by omega)
      have hpb := lvlZ_posQ hodd hq hd hcd hs (m := b + 1) (by omega) (by omega)
      have hkey := h.1
      unfold twKey at hkey
      have hfa : decide (lvlZ (c - d) (-d) w (a + 1) < 0) = false := by
        simp only [decide_eq_false_iff_not, not_lt]
        exact le_of_lt hpa
      have hfb : decide (lvlZ (c - d) (-d) w (b + 1) < 0) = false := by
        simp only [decide_eq_false_iff_not, not_lt]
        exact le_of_lt hpb
      rw [hfa, hfb, Prod.Lex.toLex_le_toLex] at hkey
      simp only [lt_self_iff_false, true_and, false_or] at hkey
      rw [Prod.Lex.toLex_le_toLex] at hkey
      have hiff := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := s) (i := b + 1) (k := a + 1)
        (by omega) (by omega)
      rw [lvlZ_append_false _ _ (by omega), lvlZ_append_false _ _ (by omega)] at hiff
      rcases hkey with hlt | ⟨heq, _⟩
      · exact hiff.mpr hlt
      · exfalso
        have hiff' := lvlQ_lt_iff_lvlZ hodd hq hd hcd hord (s := s) (i := a + 1) (k := b + 1)
          (by omega) (by omega)
        rw [lvlZ_append_false _ _ (by omega), lvlZ_append_false _ _ (by omega)] at hiff'
        have hne := lvlQ_ne_of_ne hodd (s := s) (i := a + 1) (k := b + 1) (by omega) (by omega)
          (by omega)
        rcases lt_or_gt_of_ne hne with h1 | h1
        · have := hiff'.mp h1
          omega
        · have := hiff.mp h1
          omega
    · intro a ha b hb
      rw [List.mem_singleton] at hb
      rw [hb]
      have ha' := hmemZ ha
      have hgt : 1 < lvlQ q s (a + 1) := hA.prefix_gt (a + 1) (by omega) (by omega)
      have hend : lvlQ q s (w.length + 1) < 1 := by
        rw [← hlen]
        unfold lvlQ
        rw [List.take_length]
        exact hA.lt_one
      linarith
  · have h := (sweepIdxZ_perm (c - d) (-d) w).append_right [w.length]
    have h2 := sweepIdxQ_perm q s
    rw [hlen, List.range_succ] at h2
    exact h2.trans h.symm

/-- The sweep of an admissible word is the integer sweep of its Dyck part, then the
    final halving. -/
theorem sweepQ_eq_sweepZ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} {c d : ℤ} (hd : 0 < d)
    (hcd : ∀ a : ℕ, 1 ≤ a → a ≤ n + 1 →
      d * ((p2Q q a : ℤ) - 1) < c * a ∧ c * a < d * p2Q q a)
    {w : List Bool} (hs : w ++ [false] ∈ admSetQ q n) :
    sweepQ q (w ++ [false]) = sweepZ (c - d) (-d) w ++ [false] := by
  unfold sweepQ sweepZ
  rw [sweepIdxQ_eq hodd hq hd hcd hs, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi' : i < w.length := by
      rw [(sweepIdxZ_perm _ _ w).mem_iff, List.mem_range] at hi
      exact hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
  · simp

/-- Under Thomas and Williams, Thm 6.3, the sweep permutes the admissible words of
    each Order. -/
theorem sweepQ_bijOn (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) (n : ℕ) :
    Set.BijOn (sweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) := by
  obtain ⟨c, d, hd, hcd⟩ := exists_weightsQ hq n
  have hmaps : Set.MapsTo (sweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) :=
    fun s hs => sweepQ_mem_admSetQ hodd (by omega) hs
  refine ((admSetQ q n).finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).mp ?_
  intro s hs s' hs' heq
  have hs1 : s ∈ admSetQ q n := hs
  have hs1' : s' ∈ admSetQ q n := hs'
  obtain ⟨w, rfl⟩ := exists_eq_append_falseQ hq hs1
  obtain ⟨w', rfl⟩ := exists_eq_append_falseQ hq hs1'
  rw [sweepQ_eq_sweepZ hodd hq hd hcd hs1, sweepQ_eq_sweepZ hodd hq hd hcd hs1'] at heq
  have hZ := List.append_cancel_right heq
  have hl1 := admissibleQ_length (by omega) ((mem_admSetQ (by omega) _ _).mp hs1).1
  have hl2 := admissibleQ_length (by omega) ((mem_admSetQ (by omega) _ _).mp hs1').1
  rw [((mem_admSetQ (by omega) _ _).mp hs1).2] at hl1
  rw [((mem_admSetQ (by omega) _ _).mp hs1').2] at hl2
  have hlen : w.length = w'.length := by
    simp only [List.length_append, List.length_singleton] at hl1 hl2
    omega
  have hw := dropLast_mem_dyckSetQ hodd hq hd hcd hs1
  have hw' := dropLast_mem_dyckSetQ hodd hq hd hcd hs1'
  rw [← hlen] at hw'
  have hcw := dyckSet_subset_contentSet _ _ _ _ hw
  have hcw' := dyckSet_subset_contentSet _ _ _ _ hw'
  rw [(hTW (c - d) (-d) n (w.length - n)).injOn hcw hcw' hZ]

end AcceleratedCollatz
