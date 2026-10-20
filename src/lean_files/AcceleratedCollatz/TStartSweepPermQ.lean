-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TStartSweepQ

/-!
  The start sweep of the q-family as a permutation (odd q ≥ 3). `peakFlip s k`
  reverses the two halves of s around the point k. When no later point lies below an
  earlier one by less than the level of the whole word, the start sweep of s is the
  sweep of `peakFlip s k` (`startSweepQ_eq_sweepQ_peakFlip`). At an upper record Order
  this holds for every admissible word (`lvlQ_lt_mul_of_upperRecordQ`), and the flip
  around the highest point is admissible again (`peakFlip_mem_admSetQ`). So the start
  sweep maps the admissible words of Order n to admissible words exactly at the upper
  record Orders (`mapsTo_startSweepQ_iff`), and under `SweepBijective` it permutes
  them there (`startSweepQ_bijOn`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-! ### The flip around a point -/

/-- The two halves of s around the point k, each reversed. -/
def peakFlip (s : List Bool) (k : ℕ) : List Bool := (s.take k).reverse ++ (s.drop k).reverse

/-- Step i of `peakFlip s k` is step `flipIdx s.length k i` of s. -/
def flipIdx (L k i : ℕ) : ℕ := if i < k then k - 1 - i else L + k - 1 - i

theorem flipIdx_lt {L k i : ℕ} (hk : k ≤ L) (hi : i < L) : flipIdx L k i < L := by
  unfold flipIdx
  split_ifs
  · omega
  · omega

theorem flipIdx_flipIdx {L k i : ℕ} (hi : i < L) :
    flipIdx L k (flipIdx L k i) = i := by
  unfold flipIdx
  split_ifs
  · omega
  · omega
  · omega
  · omega

theorem peakFlip_perm (s : List Bool) (k : ℕ) : (peakFlip s k).Perm s := by
  have h := ((s.take k).reverse_perm).append ((s.drop k).reverse_perm)
  rw [List.take_append_drop] at h
  exact h

theorem length_peakFlip (s : List Bool) (k : ℕ) : (peakFlip s k).length = s.length :=
  (peakFlip_perm s k).length_eq

theorem seqProductQ_perm (q : ℕ) {l l' : List Bool} (h : l.Perm l') :
    seqProductQ q l = seqProductQ q l' :=
  (h.map (factorQ q)).prod_eq

theorem order_perm {l l' : List Bool} (h : l.Perm l') : order l = order l' :=
  (h.filter id).length_eq

theorem getD_peakFlip {s : List Bool} {k i : ℕ} (hk : k ≤ s.length) (hi : i < s.length) :
    (peakFlip s k).getD i false = s.getD (flipIdx s.length k i) false := by
  unfold peakFlip flipIdx
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hlt : (s.take k).reverse.length = k := by
    simp [hk]
  have hl : (s.take k).length = k := by
    simp [hk]
  split_ifs with hik
  · have hlt' : k - 1 - i < k := by omega
    rw [List.getElem?_append_left (by omega), List.getElem?_reverse (by omega),
      List.getElem?_take, hl]
    simp only [hlt', ↓reduceIte]
  · have hid : i - k < (s.drop k).length := by
      rw [List.length_drop]
      omega
    rw [List.getElem?_append_right (by omega), hlt, List.getElem?_reverse hid,
      List.getElem?_drop, List.length_drop]
    congr 2
    omega

/-- The steps u ≤ i < v multiply the level at u to the level at v. -/
theorem lvlQ_mul_seqProductQ_drop (q : ℕ) (s : List Bool) {u v : ℕ} (huv : u ≤ v) :
    lvlQ q s u * seqProductQ q ((s.take v).drop u) = lvlQ q s v := by
  unfold lvlQ
  rw [← seqProductQ_append]
  have h : s.take u = (s.take v).take u := by
    rw [List.take_take, min_eq_left huv]
  rw [h, List.take_append_drop]

/-- After m ≤ k steps the flip is at the level of the point k over that of k - m. -/
theorem lvlQ_peakFlip_le {s : List Bool} {k m : ℕ} (hk : k ≤ s.length) (hm : m ≤ k) :
    lvlQ q (peakFlip s k) m * lvlQ q s (k - m) = lvlQ q s k := by
  have hl : (s.take k).length = k := by
    simp [hk]
  have htake : (peakFlip s k).take m = ((s.take k).drop (k - m)).reverse := by
    unfold peakFlip
    rw [List.take_append_of_le_length (by simp [hk, hm]), List.take_reverse, hl]
  have h := lvlQ_mul_seqProductQ_drop q s (Nat.sub_le k m)
  rw [← h, mul_comm]
  congr 1
  unfold lvlQ
  rw [htake]
  exact seqProductQ_perm q (List.reverse_perm _)

/-- After m ≥ k steps the flip is at the level of the point k times that of the whole
    word, over that of the point length + k - m. -/
theorem lvlQ_peakFlip_ge {s : List Bool} {k m : ℕ} (hk : k ≤ s.length) (hkm : k ≤ m)
    (hm : m ≤ s.length) :
    lvlQ q (peakFlip s k) m * lvlQ q s (s.length + k - m) =
      lvlQ q s k * lvlQ q s s.length := by
  have hl : (s.take k).reverse.length = k := by
    simp [hk]
  have htake : (peakFlip s k).take m =
      (s.take k).reverse ++ (s.drop (s.length + k - m)).reverse := by
    unfold peakFlip
    rw [List.take_append, List.take_of_length_le (by omega), hl, List.take_reverse,
      List.drop_drop, List.length_drop]
    congr 3
    omega
  have hsplit : lvlQ q s (s.length + k - m) * seqProductQ q (s.drop (s.length + k - m)) =
      lvlQ q s s.length := by
    unfold lvlQ
    rw [← seqProductQ_append, List.take_append_drop, List.take_length]
  have hfl : lvlQ q (peakFlip s k) m =
      lvlQ q s k * seqProductQ q (s.drop (s.length + k - m)) := by
    unfold lvlQ
    rw [htake, seqProductQ_append, seqProductQ_perm q (List.reverse_perm _),
      seqProductQ_perm q (List.reverse_perm (s.drop (s.length + k - m)))]
  rw [hfl, ← hsplit]
  ring

/-! ### The start sweep as the sweep of the flip -/

/-- From G Y = F X and G < F: X < Y. -/
theorem lt_of_mul_eq_mul {F G X Y : ℚ} (hG : 0 < G) (hX : 0 < X) (h : G * Y = F * X)
    (hlt : G < F) : X < Y := by
  by_contra hle
  push Not at hle
  have h1 : G * Y ≤ G * X := mul_le_mul_of_nonneg_left hle hG.le
  have h2 : G * X < F * X := mul_lt_mul_of_pos_right hlt hX
  linarith

theorem perm_map_flipIdx {L k : ℕ} (hk : k ≤ L) :
    ((List.range L).map (flipIdx L k)).Perm (List.range L) := by
  have hnd : ((List.range L).map (flipIdx L k)).Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro x hx y hy hxy
    rw [List.mem_range] at hx hy
    rw [← flipIdx_flipIdx (k := k) hx, ← flipIdx_flipIdx (k := k) hy, hxy]
  rw [List.perm_ext_iff_of_nodup hnd List.nodup_range]
  intro a
  rw [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact flipIdx_lt hk (List.mem_range.mp hi)
  · intro ha
    exact ⟨flipIdx L k a, List.mem_range.mpr (flipIdx_lt hk ha), flipIdx_flipIdx ha⟩

/-- The start sweep of s is the sweep of its flip around k, when across k the order of
    two levels does not change with a factor of the level of the whole word. -/
theorem startSweepQ_eq_sweepQ_peakFlip (hodd : Odd q) (hq0 : 0 < q) {s : List Bool} {k : ℕ}
    (hk : k ≤ s.length)
    (h1 : ∀ i j, i < k → k ≤ j → j < s.length →
      lvlQ q s i * lvlQ q s s.length < lvlQ q s j → lvlQ q s i < lvlQ q s j)
    (h2 : ∀ i j, i < k → k ≤ j → j < s.length →
      lvlQ q s j < lvlQ q s i * lvlQ q s s.length → lvlQ q s j < lvlQ q s i) :
    startSweepQ q s = sweepQ q (peakFlip s k) := by
  set fl := peakFlip s k with hfl
  have hlen : fl.length = s.length := length_peakFlip s k
  have hpos : ∀ (t : List Bool) (j : ℕ), 0 < lvlQ q t j := fun t j => lvlQ_pos hq0 t j
  have hend : ∀ i, i < s.length → lvlQ q fl (i + 1) * lvlQ q s (flipIdx s.length k i) =
      if i < k then lvlQ q s k else lvlQ q s k * lvlQ q s s.length := by
    intro i hi
    unfold flipIdx
    split_ifs with hik
    · have h := lvlQ_peakFlip_le (q := q) hk (m := i + 1) (by omega)
      have hsub : k - (i + 1) = k - 1 - i := by omega
      rw [hsub] at h
      exact h
    · have h := lvlQ_peakFlip_ge (q := q) hk (m := i + 1) (by omega) (by omega)
      have hsub : s.length + k - (i + 1) = s.length + k - 1 - i := by omega
      rw [hsub] at h
      exact h
  have hidx : startIdxQ q s = (sweepIdxQ q fl).map (flipIdx s.length k) := by
    apply List.Perm.eq_of_pairwise (le := fun i j => lvlQ q s i < lvlQ q s j)
    · intro a b _ _ hab hba
      exact (lt_asymm hab hba).elim
    · refine ((startIdxQ_pairwise q s).and (startIdxQ_nodup q s)).imp_of_mem ?_
      intro a b ha hb h
      have ha' := mem_startIdxQ.mp ha
      have hb' := mem_startIdxQ.mp hb
      exact lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) h.2)
    · rw [List.pairwise_map]
      refine ((sweepIdxQ_pairwise q fl).and (sweepIdxQ_nodup q fl)).imp_of_mem ?_
      intro a b ha hb h
      have ha' : a < s.length := hlen ▸ mem_sweepIdxQ.mp ha
      have hb' : b < s.length := hlen ▸ mem_sweepIdxQ.mp hb
      have hstrict : lvlQ q fl (b + 1) < lvlQ q fl (a + 1) :=
        lt_of_le_of_ne h.1 (lvlQ_ne_of_ne hodd (by omega) (by omega) (by omega))
      have hea := hend a ha'
      have heb := hend b hb'
      have hfa := flipIdx_lt hk ha'
      have hfb := flipIdx_lt hk hb'
      by_cases hak : a < k
      · by_cases hbk : b < k
        · simp only [hak, ↓reduceIte] at hea
          simp only [hbk, ↓reduceIte] at heb
          exact lt_of_mul_eq_mul (hpos _ _) (hpos _ _) (heb.trans hea.symm) hstrict
        · simp only [hak, ↓reduceIte] at hea
          simp only [hbk, ↓reduceIte] at heb
          have hfa' : flipIdx s.length k a < k := by
            unfold flipIdx
            simp only [hak, ↓reduceIte]
            omega
          have hfb' : k ≤ flipIdx s.length k b := by
            unfold flipIdx
            simp only [hbk, ↓reduceIte]
            omega
          have hX : lvlQ q s (flipIdx s.length k a) * lvlQ q s s.length <
              lvlQ q s (flipIdx s.length k b) := by
            apply lt_of_mul_eq_mul (hpos fl (b + 1)) (mul_pos (hpos _ _) (hpos _ _)) _ hstrict
            rw [heb, ← hea]
            ring
          exact h1 _ _ hfa' hfb' hfb hX
      · by_cases hbk : b < k
        · simp only [hak, ↓reduceIte] at hea
          simp only [hbk, ↓reduceIte] at heb
          have hfa' : k ≤ flipIdx s.length k a := by
            unfold flipIdx
            simp only [hak, ↓reduceIte]
            omega
          have hfb' : flipIdx s.length k b < k := by
            unfold flipIdx
            simp only [hbk, ↓reduceIte]
            omega
          have hX : lvlQ q s (flipIdx s.length k a) <
              lvlQ q s (flipIdx s.length k b) * lvlQ q s s.length := by
            apply lt_of_mul_eq_mul (hpos fl (b + 1)) (hpos _ _) _ hstrict
            rw [hea, ← heb]
            ring
          exact h2 _ _ hfb' hfa' hfa hX
        · simp only [hak, ↓reduceIte] at hea
          simp only [hbk, ↓reduceIte] at heb
          exact lt_of_mul_eq_mul (hpos _ _) (hpos _ _) (heb.trans hea.symm) hstrict
    · have hp1 := (sweepIdxQ_perm q fl).map (flipIdx s.length k)
      rw [hlen] at hp1
      exact (startIdxQ_perm q s).trans ((hp1.trans (perm_map_flipIdx hk)).symm)
  unfold startSweepQ sweepQ
  rw [hidx, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' : i < s.length := hlen ▸ mem_sweepIdxQ.mp hi
  exact (getD_peakFlip hk hi').symm

/-! ### Words that are rotations of each other -/

/-- Two flips that agree come from two words that are rotations of each other. -/
theorem exists_rotation_of_peakFlip_eq {s t : List Bool} {k m : ℕ}
    (h : peakFlip s k = peakFlip t m) : ∃ z u, s = z ++ u ∧ t = u ++ z := by
  have hrev := congrArg List.reverse h
  unfold peakFlip at hrev
  rw [List.reverse_append, List.reverse_reverse, List.reverse_reverse, List.reverse_append,
    List.reverse_reverse, List.reverse_reverse, List.append_eq_append_iff] at hrev
  rcases hrev with ⟨a, h1, h2⟩ | ⟨c, h1, h2⟩
  · refine ⟨a, t.take m ++ s.drop k, ?_, ?_⟩
    · rw [← List.append_assoc, ← h2, List.take_append_drop]
    · rw [List.append_assoc, ← h1, List.take_append_drop]
  · refine ⟨s.take k ++ t.drop m, c, ?_, ?_⟩
    · rw [List.append_assoc, ← h1, List.take_append_drop]
    · rw [← List.append_assoc, ← h2, List.take_append_drop]

/-- Two admissible words that are rotations of each other are equal. -/
theorem append_comm_of_admissibleQ {z u : List Bool} (h1 : AdmissibleQ q (z ++ u))
    (h2 : AdmissibleQ q (u ++ z)) : z ++ u = u ++ z := by
  rcases List.eq_nil_or_concat' z with hz | hz
  · rw [hz]
    simp
  rcases List.eq_nil_or_concat' u with hu | hu
  · rw [hu]
    simp
  exfalso
  have hzl : 1 ≤ z.length := by
    obtain ⟨_, _, rfl⟩ := hz
    simp
  have hul : 1 ≤ u.length := by
    obtain ⟨_, _, rfl⟩ := hu
    simp
  have hzL : z.length < (z ++ u).length := by
    rw [List.length_append]
    omega
  have huL : u.length < (u ++ z).length := by
    rw [List.length_append]
    omega
  have hz1 := h1.prefix_gt z.length hzl hzL
  have hu1 := h2.prefix_gt u.length hul huL
  rw [List.take_left] at hz1 hu1
  have hlt := h1.lt_one
  rw [seqProductQ_append] at hlt
  nlinarith

/-! ### Upper record Orders -/

theorem order_take_mono (s : List Bool) {i j : ℕ} (hij : i ≤ j) :
    order (s.take i) ≤ order (s.take j) := by
  have h := order_take_le (s.take j) i
  rwa [List.take_take, min_eq_left hij] at h

/-- lvl j < lvl i times the level of the whole word, as cross products. -/
theorem lvlQ_lt_mul_iff (q : ℕ) {s : List Bool} {i j : ℕ} (hi : i ≤ s.length)
    (hj : j ≤ s.length) :
    lvlQ q s j < lvlQ q s i * lvlQ q s s.length ↔
      q ^ order (s.take j) * 2 ^ i * 2 ^ s.length <
        q ^ order (s.take i) * q ^ order s * 2 ^ j := by
  have h1 := lvlQ_mul_pow q hi
  have h2 := lvlQ_mul_pow q hj
  have h3 := lvlQ_mul_pow q (s := s) (j := s.length) le_rfl
  rw [List.take_length] at h3
  have hp : (0 : ℚ) < 2 ^ i * 2 ^ j * 2 ^ s.length := by positivity
  have hcast : (q ^ order (s.take j) * 2 ^ i * 2 ^ s.length <
      q ^ order (s.take i) * q ^ order s * 2 ^ j) ↔
      ((q : ℚ) ^ order (s.take j) * 2 ^ i * 2 ^ s.length <
        q ^ order (s.take i) * q ^ order s * 2 ^ j) := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  have hL : lvlQ q s j * (2 ^ i * 2 ^ j * 2 ^ s.length) =
      (q : ℚ) ^ order (s.take j) * 2 ^ i * 2 ^ s.length := by
    rw [← h2]
    ring
  have hR : lvlQ q s i * lvlQ q s s.length * (2 ^ i * 2 ^ j * 2 ^ s.length) =
      (q : ℚ) ^ order (s.take i) * q ^ order s * 2 ^ j := by
    rw [← h1, ← h3]
    ring
  rw [hcast, ← hL, ← hR]
  exact (mul_lt_mul_iff_of_pos_right hp).symm

/-- At an upper record Order no point before the end of an admissible word lies below an
    earlier point by less than the level of the whole word. -/
theorem lvlQ_lt_mul_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : UpperRecordQ q n) {s : List Bool} (hs : s ∈ admSetQ q n) {i j : ℕ} (hij : i < j)
    (hj : j < s.length) (hlt : lvlQ q s j < lvlQ q s i) :
    lvlQ q s j < lvlQ q s i * lvlQ q s s.length := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hlen : s.length = p2Q q n := by
    rw [admissibleQ_length (by omega) hA, hord]
  have hq0 : 0 < q := by omega
  have hmono := order_take_mono s hij.le
  have hjn : order (s.take j) ≤ n := hord ▸ order_take_le s j
  obtain ⟨a, ha⟩ : ∃ a, order (s.take j) = order (s.take i) + a :=
    ⟨order (s.take j) - order (s.take i), by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hlt' := (lvlQ_lt_iff q (by omega) (by omega)).mp hlt
  rw [ha, pow_add, pow_add] at hlt'
  have hqa : q ^ a < 2 ^ d := by
    have hc : 0 < q ^ order (s.take i) * 2 ^ i := by positivity
    by_contra hge
    push Not at hge
    have := Nat.mul_le_mul_left (q ^ order (s.take i) * 2 ^ i) hge
    nlinarith
  rw [lvlQ_lt_mul_iff q (by omega) (by omega), ha, hord, hlen]
  have hkey : q ^ a * 2 ^ p2Q q n < q ^ n * 2 ^ d := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · have hn1 : 1 ≤ n := by
        by_contra h0
        have hn0 : n = 0 := by omega
        rw [hn0] at hlen
        simp [p2Q] at hlen
        omega
      rw [ha0, pow_zero, one_mul, lt_q_pow_mul_iff hodd hq hn1]
      omega
    · rcases Nat.lt_or_ge a n with han | han
      · have hbf := (upperRecordQ_iff_blockFactorQ hodd hq n).mp hR a hapos han
        rw [blockFactorQ_lt_iff] at hbf
        have hpa := (q_pow_lt_two_pow_iff hq).mp hqa
        have hpow : 2 ^ p2Q q a ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hpa
        calc q ^ a * 2 ^ p2Q q n < q ^ n * 2 ^ p2Q q a := hbf
          _ ≤ q ^ n * 2 ^ d := Nat.mul_le_mul_left _ hpow
      · exfalso
        have hi0 : order (s.take i) = 0 := by omega
        have hli := lvlQ_mul_pow q (s := s) (j := i) (by omega)
        rw [hi0, pow_zero] at hli
        have h2i : (1 : ℚ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        have hipos := lvlQ_pos hq0 s i
        have hle1 : lvlQ q s i ≤ 1 := by
          nlinarith
        have hgt : 1 < lvlQ q s (i + d) := hA.prefix_gt (i + d) (by omega) hj
        linarith
  calc q ^ (order (s.take i) + a) * 2 ^ i * 2 ^ p2Q q n
      = q ^ order (s.take i) * 2 ^ i * (q ^ a * 2 ^ p2Q q n) := by
        rw [pow_add]
        ring
    _ < q ^ order (s.take i) * 2 ^ i * (q ^ n * 2 ^ d) :=
        Nat.mul_lt_mul_of_pos_left hkey (by positivity)
    _ = q ^ order (s.take i) * q ^ n * 2 ^ (i + d) := by
        rw [pow_add]
        ring

/-- A word has a highest point. -/
theorem exists_peak (q : ℕ) (s : List Bool) :
    ∃ k, k ≤ s.length ∧ ∀ j, j ≤ s.length → lvlQ q s j ≤ lvlQ q s k := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range (s.length + 1)) (lvlQ q s)
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  rw [Finset.mem_range] at hk
  exact ⟨k, by omega, fun j hj => hmax j (Finset.mem_range.mpr (by omega))⟩

/-- At an upper record Order the flip of an admissible word around its highest point is
    admissible. -/
theorem peakFlip_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hR : UpperRecordQ q n)
    {s : List Bool} (hs : s ∈ admSetQ q n) {k : ℕ} (hk : k ≤ s.length)
    (hmax : ∀ j, j ≤ s.length → lvlQ q s j ≤ lvlQ q s k) : peakFlip s k ∈ admSetQ q n := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hq0 : 0 < q := by omega
  rw [mem_admSetQ (by omega)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m hm1 hmL
    rw [length_peakFlip] at hmL
    change 1 < lvlQ q (peakFlip s k) m
    rcases Nat.le_total m k with hmk | hkm
    · have h := lvlQ_peakFlip_le (q := q) hk hmk
      have hlt : lvlQ q s (k - m) < lvlQ q s k :=
        lt_of_le_of_ne (hmax _ (by omega)) (lvlQ_ne_of_ne hodd (by omega) hk (by omega))
      have hp := lvlQ_pos hq0 s (k - m)
      by_contra hle
      push Not at hle
      nlinarith
    · rcases Nat.eq_or_lt_of_le hkm with hkm' | hkm'
      · have h := lvlQ_peakFlip_le (q := q) hk (le_of_eq hkm'.symm)
        have hlt : lvlQ q s (k - m) < lvlQ q s k :=
          lt_of_le_of_ne (hmax _ (by omega)) (lvlQ_ne_of_ne hodd (by omega) hk (by omega))
        have hp := lvlQ_pos hq0 s (k - m)
        by_contra hle
        push Not at hle
        nlinarith
      · have h := lvlQ_peakFlip_ge (q := q) hk hkm hmL.le
        have hp1 : k < s.length + k - m := by omega
        have hp2 : s.length + k - m < s.length := by omega
        have hlt : lvlQ q s (s.length + k - m) < lvlQ q s k :=
          lt_of_le_of_ne (hmax _ hp2.le) (lvlQ_ne_of_ne hodd hp2.le hk (by omega))
        have hup := lvlQ_lt_mul_of_upperRecordQ hodd hq hR hs hp1 hp2 hlt
        have hp := lvlQ_pos hq0 s (s.length + k - m)
        by_contra hle
        push Not at hle
        nlinarith
  · rw [seqProductQ_perm q (peakFlip_perm s k)]
    exact hA.lt_one
  · rw [order_perm (peakFlip_perm s k), hord]

/-- At an upper record Order the start sweep of an admissible word is the sweep of its
    flip around any of its points. -/
theorem startSweepQ_eq_sweepQ_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : UpperRecordQ q n) {s : List Bool} (hs : s ∈ admSetQ q n) {k : ℕ} (hk : k ≤ s.length) :
    startSweepQ q s = sweepQ q (peakFlip s k) := by
  obtain ⟨hA, hord⟩ := (mem_admSetQ (by omega) _ _).mp hs
  have hq0 : 0 < q := by omega
  have hE : lvlQ q s s.length < 1 := by
    rw [lvlQ_length]
    exact hA.lt_one
  apply startSweepQ_eq_sweepQ_peakFlip hodd hq0 hk
  · intro i j hik hkj hj hlt
    by_contra hge
    push Not at hge
    have hne := lvlQ_ne_of_ne hodd (s := s) (i := j) (k := i) hj.le (by omega) (by omega)
    have hup := lvlQ_lt_mul_of_upperRecordQ hodd hq hR hs (by omega : i < j) hj
      (lt_of_le_of_ne hge hne)
    linarith
  · intro i j hik hkj hj hlt
    have hp := lvlQ_pos hq0 s i
    nlinarith

/-- At an upper record Order the start sweep maps admissible words to admissible words. -/
theorem startSweepQ_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hR : UpperRecordQ q n)
    {s : List Bool} (hs : s ∈ admSetQ q n) : startSweepQ q s ∈ admSetQ q n := by
  obtain ⟨k, hk, hmax⟩ := exists_peak q s
  rw [startSweepQ_eq_sweepQ_of_upperRecordQ hodd hq hR hs hk]
  exact sweepQ_mem_admSetQ hodd (by omega) (peakFlip_mem_admSetQ hodd hq hR hs hk hmax)

/-- The start sweep maps the admissible words of Order n to admissible words exactly at
    the upper record Orders. -/
theorem mapsTo_startSweepQ_iff (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    Set.MapsTo (startSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) ↔
      UpperRecordQ q n := by
  constructor
  · intro h
    by_contra hR
    exact startSweepQ_upDownQ_not_mem hodd hq hR (h (upDownQ_mem_admSetQ hodd hq n))
  · intro hR s hs
    exact startSweepQ_mem_admSetQ hodd hq hR hs

/-- Under Thomas and Williams, Thm 6.3, the start sweep permutes the admissible words of
    an upper record Order. -/
theorem startSweepQ_bijOn (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) {n : ℕ}
    (hR : UpperRecordQ q n) :
    Set.BijOn (startSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) := by
  have hmaps := (mapsTo_startSweepQ_iff hodd hq n).mpr hR
  refine ((admSetQ q n).finite_toSet.injOn_iff_bijOn_of_mapsTo hmaps).mp ?_
  intro s hs t ht heq
  have hs1 : s ∈ admSetQ q n := hs
  have ht1 : t ∈ admSetQ q n := ht
  obtain ⟨k, hk, hkmax⟩ := exists_peak q s
  obtain ⟨m, hm, hmmax⟩ := exists_peak q t
  rw [startSweepQ_eq_sweepQ_of_upperRecordQ hodd hq hR hs1 hk,
    startSweepQ_eq_sweepQ_of_upperRecordQ hodd hq hR ht1 hm] at heq
  have hfl := (sweepQ_bijOn hodd hq hTW n).injOn
    (peakFlip_mem_admSetQ hodd hq hR hs1 hk hkmax)
    (peakFlip_mem_admSetQ hodd hq hR ht1 hm hmmax) heq
  obtain ⟨z, u, rfl, rfl⟩ := exists_rotation_of_peakFlip_eq hfl
  exact append_comm_of_admissibleQ ((mem_admSetQ (by omega) _ _).mp hs1).1
    ((mem_admSetQ (by omega) _ _).mp ht1).1

/-- Under Thomas and Williams, Thm 6.3, the start sweep permutes the admissible words of
    Order n exactly at the upper record Orders. -/
theorem startSweepQ_bijOn_iff (hodd : Odd q) (hq : 3 ≤ q) (hTW : SweepBijective) (n : ℕ) :
    Set.BijOn (startSweepQ q) (admSetQ q n : Set (List Bool)) (admSetQ q n) ↔
      UpperRecordQ q n :=
  ⟨fun h => (mapsTo_startSweepQ_iff hodd hq n).mp h.mapsTo, startSweepQ_bijOn hodd hq hTW⟩

end AcceleratedCollatz
