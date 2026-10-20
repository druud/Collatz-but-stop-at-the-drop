-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecordQ

/-!
  Start sweep for the q-family (odd q ≥ 3): the steps of a word sorted by the level
  at which they start, lowest first (`startSweepQ`). A set of steps that start below
  all other steps is a prefix of the start sweep (`toFinset_take_startIdxQ`),
  and every prefix is such a set (`exists_startSweepQ_prefix_set`). The word of n odd steps
  followed by halvings is admissible (`upDownQ_mem_admSetQ`); at an Order that is no
  upper record its start sweep is not (`startSweepQ_upDownQ_not_mem`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Step indices of s, sorted by starting level, lowest first. -/
def startIdxQ (q : ℕ) (s : List Bool) : List ℕ :=
  (List.range s.length).mergeSort (fun i k => decide (lvlQ q s i ≤ lvlQ q s k))

/-- Start sweep: the steps of s in the order of `startIdxQ`. -/
def startSweepQ (q : ℕ) (s : List Bool) : List Bool :=
  (startIdxQ q s).map (fun i => s.getD i false)

theorem startIdxQ_perm (q : ℕ) (s : List Bool) : (startIdxQ q s).Perm (List.range s.length) :=
  List.mergeSort_perm _ _

theorem startIdxQ_nodup (q : ℕ) (s : List Bool) : (startIdxQ q s).Nodup :=
  (startIdxQ_perm q s).nodup_iff.mpr List.nodup_range

theorem mem_startIdxQ {s : List Bool} {i : ℕ} : i ∈ startIdxQ q s ↔ i < s.length := by
  rw [(startIdxQ_perm q s).mem_iff, List.mem_range]

theorem length_startIdxQ (q : ℕ) (s : List Bool) : (startIdxQ q s).length = s.length := by
  rw [(startIdxQ_perm q s).length_eq, List.length_range]

theorem startIdxQ_pairwise (q : ℕ) (s : List Bool) :
    (startIdxQ q s).Pairwise (fun i k => lvlQ q s i ≤ lvlQ q s k) := by
  have h := List.pairwise_mergeSort
    (le := fun i k => decide (lvlQ q s i ≤ lvlQ q s k))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc)
    (fun a b => by
      rcases le_total (lvlQ q s a) (lvlQ q s b) with h | h
      · simp [h]
      · simp [h])
    (List.range s.length)
  exact h.imp (fun hab => by simpa using hab)

/-- The start sweep permutes the steps. -/
theorem startSweepQ_perm (q : ℕ) (s : List Bool) : (startSweepQ q s).Perm s := by
  have h := (startIdxQ_perm q s).map (fun i => s.getD i false)
  rw [map_getD_range] at h
  exact h

theorem length_startSweepQ (q : ℕ) (s : List Bool) : (startSweepQ q s).length = s.length :=
  (startSweepQ_perm q s).length_eq

theorem seqProductQ_startSweepQ (q : ℕ) (s : List Bool) :
    seqProductQ q (startSweepQ q s) = seqProductQ q s :=
  ((startSweepQ_perm q s).map (factorQ q)).prod_eq

/-! ### Levels -/

/-- Levels compare like the cross products of their powers of q and 2. -/
theorem lvlQ_lt_iff (q : ℕ) {s : List Bool} {i j : ℕ} (hi : i ≤ s.length)
    (hj : j ≤ s.length) :
    lvlQ q s i < lvlQ q s j ↔
      q ^ order (s.take i) * 2 ^ j < q ^ order (s.take j) * 2 ^ i := by
  have h1 := lvlQ_mul_pow q hi
  have h2 := lvlQ_mul_pow q hj
  have hp1 : (0 : ℚ) < 2 ^ i := by positivity
  have hp2 : (0 : ℚ) < 2 ^ j := by positivity
  have hcast : (q ^ order (s.take i) * 2 ^ j < q ^ order (s.take j) * 2 ^ i) ↔
      ((q : ℚ) ^ order (s.take i) * 2 ^ j < q ^ order (s.take j) * 2 ^ i) := by
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

/-- The steps u ≤ i < v multiply the level at u to the level at v. -/
theorem lvlQ_mul_prod_Ico (q : ℕ) (s : List Bool) {u v : ℕ} (huv : u ≤ v)
    (hv : v ≤ s.length) :
    lvlQ q s u * ∏ i ∈ Finset.Ico u v, factorQ q (s.getD i false) = lvlQ q s v := by
  induction v, huv using Nat.le_induction with
  | base =>
    simp
  | succ v huv ih =>
    have hlt : v < s.length := by omega
    have hget : s[v]? = some (s.getD v false) := by
      simp [List.getD_eq_getElem?_getD, hlt]
    rw [Finset.prod_Ico_succ_top huv, ← mul_assoc, ih (by omega), lvlQ_succ q s hget]

/-! ### Prefixes of the start sweep -/

/-- A set of steps that start below all other steps is a prefix of the start sweep. -/
theorem toFinset_take_startIdxQ {s : List Bool} {T : Finset ℕ}
    (hT : ∀ i ∈ T, i < s.length)
    (hlow : ∀ i ∈ T, ∀ k, k < s.length → k ∉ T → lvlQ q s i < lvlQ q s k) :
    ((startIdxQ q s).take T.card).toFinset = T := by
  set l := startIdxQ q s with hl
  have hnd : l.Nodup := startIdxQ_nodup q s
  have hpw := startIdxQ_pairwise q s
  have hlen : l.length = s.length := length_startIdxQ q s
  have hTsub : T ⊆ Finset.range s.length := fun i hi => Finset.mem_range.mpr (hT i hi)
  have hcardle : T.card ≤ s.length := by
    have := Finset.card_le_card hTsub
    rwa [Finset.card_range] at this
  have hsplit : (l.take T.card ++ l.drop T.card).Nodup := by
    rw [List.take_append_drop]
    exact hnd
  obtain ⟨hnd1, _, hdisj⟩ := List.nodup_append.mp hsplit
  have hcard : (l.take T.card).toFinset.card = T.card := by
    rw [List.toFinset_card_of_nodup hnd1, List.length_take]
    omega
  have hsub : (l.take T.card).toFinset ⊆ T := by
    intro i hi
    rw [List.mem_toFinset] at hi
    by_contra hiT
    have hex : ∃ k ∈ T, k ∉ (l.take T.card).toFinset := by
      by_contra hall
      push Not at hall
      have hsubT : T ⊆ (l.take T.card).toFinset := hall
      have heq := Finset.eq_of_subset_of_card_le hsubT (le_of_eq hcard)
      exact hiT (heq ▸ List.mem_toFinset.mpr hi)
    obtain ⟨k, hkT, hkn⟩ := hex
    rw [List.mem_toFinset] at hkn
    have hkl : k ∈ l := mem_startIdxQ.mpr (hT k hkT)
    rw [← List.take_append_drop T.card l, List.mem_append] at hkl
    have hkd : k ∈ l.drop T.card := hkl.resolve_left hkn
    have hle := hpw.rel_of_mem_take_of_mem_drop hi hkd
    have hiL : i < s.length := mem_startIdxQ.mp (List.mem_of_mem_take hi)
    have hlt := hlow k hkT i hiL hiT
    linarith
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

/-- The level of a prefix of the start sweep: the product over its set of steps. -/
theorem seqProductQ_take_startSweepQ {s : List Bool} {T : Finset ℕ}
    (hT : ∀ i ∈ T, i < s.length)
    (hlow : ∀ i ∈ T, ∀ k, k < s.length → k ∉ T → lvlQ q s i < lvlQ q s k) :
    seqProductQ q ((startSweepQ q s).take T.card) = ∏ i ∈ T, factorQ q (s.getD i false) := by
  have hnd1 : ((startIdxQ q s).take T.card).Nodup :=
    (startIdxQ_nodup q s).sublist (List.take_sublist _ _)
  have hfin := toFinset_take_startIdxQ hT hlow
  conv_rhs => rw [← hfin]
  rw [List.prod_toFinset _ hnd1]
  unfold startSweepQ seqProductQ
  rw [← List.map_take, List.map_map]
  rfl

/-- Every prefix of the start sweep is the set of steps that start below the others. -/
theorem exists_startSweepQ_prefix_set (hodd : Odd q) (s : List Bool) {m : ℕ} (hm : m ≤ s.length) :
    ∃ T : Finset ℕ, T.card = m ∧ (∀ i ∈ T, i < s.length) ∧
      (∀ i ∈ T, ∀ k, k < s.length → k ∉ T → lvlQ q s i < lvlQ q s k) ∧
      seqProductQ q ((startSweepQ q s).take m) = ∏ i ∈ T, factorQ q (s.getD i false) := by
  set l := startIdxQ q s with hl
  have hnd : l.Nodup := startIdxQ_nodup q s
  have hpw := startIdxQ_pairwise q s
  have hlen : l.length = s.length := length_startIdxQ q s
  have hsplit : (l.take m ++ l.drop m).Nodup := by
    rw [List.take_append_drop]
    exact hnd
  obtain ⟨hnd1, _, hdisj⟩ := List.nodup_append.mp hsplit
  have hcard : (l.take m).toFinset.card = m := by
    rw [List.toFinset_card_of_nodup hnd1, List.length_take]
    omega
  have hT : ∀ i ∈ (l.take m).toFinset, i < s.length := by
    intro i hi
    rw [List.mem_toFinset] at hi
    exact mem_startIdxQ.mp (List.mem_of_mem_take hi)
  have hlow : ∀ i ∈ (l.take m).toFinset, ∀ k, k < s.length → k ∉ (l.take m).toFinset →
      lvlQ q s i < lvlQ q s k := by
    intro i hi k hk hkT
    rw [List.mem_toFinset] at hi hkT
    have hkl : k ∈ l := mem_startIdxQ.mpr hk
    rw [← List.take_append_drop m l, List.mem_append] at hkl
    have hkd : k ∈ l.drop m := hkl.resolve_left hkT
    have hle := hpw.rel_of_mem_take_of_mem_drop hi hkd
    have hik : i ≠ k := hdisj i hi k hkd
    have hi' := mem_startIdxQ.mp (List.mem_of_mem_take hi)
    exact lt_of_le_of_ne hle (lvlQ_ne_of_ne hodd (by omega) (by omega) hik)
  refine ⟨(l.take m).toFinset, hcard, hT, hlow, ?_⟩
  have h := seqProductQ_take_startSweepQ hT hlow
  rwa [hcard] at h

/-! ### The word of n odd steps followed by halvings -/

theorem lt_p2Q (hq : 3 ≤ q) (n : ℕ) : n < p2Q q n := by
  have h1 : 2 ^ n ≤ q ^ n := Nat.pow_le_pow_left (by omega) n
  have h2 := p2Q_spec hq n
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h1 h2)

/-- p2Q(a) + c ≤ p2Q(a + c). -/
theorem p2Q_add_ge (hq : 3 ≤ q) (a c : ℕ) : p2Q q a + c ≤ p2Q q (a + c) := by
  have h1 : 2 ^ (p2Q q a - 1) * 2 ^ c ≤ q ^ a * q ^ c :=
    Nat.mul_le_mul (p2Q_spec_lower hq a) (Nat.pow_le_pow_left (by omega) c)
  rw [← pow_add, ← pow_add] at h1
  have h2 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp
    (lt_of_le_of_lt h1 (p2Q_spec hq (a + c)))
  have hp := one_le_p2Q q a
  omega

/-- n odd steps, then halvings up to the length p2Q(n). -/
def upDownQ (q n : ℕ) : List Bool :=
  List.replicate n true ++ List.replicate (p2Q q n - n) false

theorem length_upDownQ (hq : 3 ≤ q) (n : ℕ) : (upDownQ q n).length = p2Q q n := by
  have := lt_p2Q hq n
  simp only [upDownQ, List.length_append, List.length_replicate]
  omega

theorem order_take_upDownQ (q n j : ℕ) : order ((upDownQ q n).take j) = min j n := by
  unfold upDownQ order
  rw [List.take_append, List.filter_append, List.length_append, List.take_replicate,
    List.take_replicate, List.length_replicate]
  simp

theorem order_upDownQ (hq : 3 ≤ q) (n : ℕ) : order (upDownQ q n) = n := by
  have h := order_take_upDownQ q n (upDownQ q n).length
  rw [List.take_length, length_upDownQ hq] at h
  have := lt_p2Q hq n
  omega

/-- The word of n odd steps followed by halvings is admissible. -/
theorem upDownQ_mem_admSetQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    upDownQ q n ∈ admSetQ q n := by
  rw [mem_admSetQ (by omega)]
  have hlen := length_upDownQ hq n
  refine ⟨⟨?_, ?_⟩, order_upDownQ hq n⟩
  · intro m hm1 hmL
    rw [hlen] at hmL
    have h0 : lvlQ q (upDownQ q n) 0 < lvlQ q (upDownQ q n) m := by
      rw [lvlQ_lt_iff q (by omega) (by omega), order_take_upDownQ, order_take_upDownQ]
      simp only [Nat.zero_min, pow_zero, one_mul, mul_one]
      rcases Nat.le_total m n with hmn | hnm
      · rw [min_eq_left hmn]
        exact Nat.pow_lt_pow_left (by omega) (by omega)
      · rw [min_eq_right hnm]
        have hn1 : 1 ≤ n := by
          by_contra h0
          have hn0 : n = 0 := by omega
          rw [hn0] at hmL
          simp [p2Q] at hmL
          omega
        exact (two_pow_lt_q_pow_iff hodd hq hn1).mpr hmL
    rw [lvlQ_zero] at h0
    exact h0
  · have h := seqProductQ_mul_pow q (upDownQ q n)
    rw [hlen, order_upDownQ hq] at h
    have hspec : (q : ℚ) ^ n < 2 ^ p2Q q n := by exact_mod_cast p2Q_spec hq n
    have hpos : (0 : ℚ) < 2 ^ p2Q q n := by positivity
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_right hge hpos.le
    linarith

/-- At an Order that is no upper record, the start sweep of the word of n odd steps
    followed by halvings is not admissible. -/
theorem startSweepQ_upDownQ_not_mem (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ}
    (hR : ¬UpperRecordQ q n) : startSweepQ q (upDownQ q n) ∉ admSetQ q n := by
  rw [upperRecordQ_iff_add hq] at hR
  push Not at hR
  obtain ⟨a, ha1, han, hne⟩ := hR
  obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
  rw [Nat.add_sub_cancel_left] at hne
  have hb1 : 1 ≤ b := by omega
  have hadd : p2Q q (a + b) = p2Q q a + p2Q q b := by
    have h1 := p2Q_add_le hq a b
    have h2 := p2Q_add_le_succ hq a b
    omega
  have hq0 : 0 < q := by omega
  have hqpos : ∀ e : ℕ, 0 < q ^ e := fun e => pow_pos hq0 e
  set w := upDownQ q (a + b) with hw
  have hlen : w.length = p2Q q a + p2Q q b := by
    rw [hw, length_upDownQ hq, hadd]
  have hbp := lt_p2Q hq b
  have hap := lt_p2Q hq a
  set T : Finset ℕ := Finset.range b ∪ Finset.Ico (b + p2Q q a) w.length with hTdef
  have hdisj : Disjoint (Finset.range b) (Finset.Ico (b + p2Q q a) w.length) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico] at hi'
    omega
  have hcard : T.card = p2Q q b := by
    rw [hTdef, Finset.card_union_of_disjoint hdisj, Finset.card_range, Nat.card_Ico, hlen]
    omega
  have hmem : ∀ i, i ∈ T ↔ i < b ∨ (b + p2Q q a ≤ i ∧ i < w.length) := by
    intro i
    rw [hTdef, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  have hT : ∀ i ∈ T, i < w.length := by
    intro i hi
    rcases (hmem i).mp hi with h | h
    · omega
    · exact h.2
  have hlow : ∀ i ∈ T, ∀ k, k < w.length → k ∉ T → lvlQ q w i < lvlQ q w k := by
    intro i hi k hk hkT
    rw [hmem] at hkT
    push Not at hkT
    obtain ⟨hkb, hk2⟩ := hkT
    have hkj : k < b + p2Q q a := by
      by_contra h
      have := hk2 (by omega)
      omega
    rw [lvlQ_lt_iff q (hT i hi).le hk.le, hw, order_take_upDownQ, order_take_upDownQ]
    rcases (hmem i).mp hi with hib | ⟨hij, hiL⟩
    · rw [min_eq_left (by omega : i ≤ a + b)]
      obtain ⟨e, he⟩ : ∃ e, min k (a + b) = i + e := ⟨min k (a + b) - i, by omega⟩
      have he1 : 1 ≤ e := by omega
      rw [he, pow_add, mul_assoc, Nat.mul_lt_mul_left (hqpos i),
        lt_q_pow_mul_iff hodd hq he1]
      rcases Nat.le_total k (a + b) with hkn | hnk
      · have := lt_p2Q hq e
        omega
      · have hge := p2Q_add_ge hq a (b - i)
        have hae : a + (b - i) = e := by omega
        rw [hae] at hge
        omega
    · rw [min_eq_right (by omega : a + b ≤ i)]
      obtain ⟨e, he⟩ : ∃ e, a + b = min k (a + b) + e := ⟨a + b - min k (a + b), by omega⟩
      conv_lhs => rw [he]
      rw [pow_add, mul_assoc, Nat.mul_lt_mul_left (hqpos _), q_pow_mul_lt_iff hq]
      rcases Nat.le_total k (a + b) with hkn | hnk
      · have hge := p2Q_add_ge hq e (a - e)
        have hae : e + (a - e) = a := by omega
        rw [hae] at hge
        omega
      · have he0 : e = 0 := by omega
        rw [he0]
        simp only [p2Q, pow_zero, Nat.log_one_right]
        omega
  have hprod : (∏ i ∈ T, factorQ q (w.getD i false)) < 1 := by
    have h1 := lvlQ_mul_prod_Ico q w (Nat.zero_le b) (by omega)
    have h2 := lvlQ_mul_prod_Ico q w (u := b + p2Q q a) (v := w.length) (by omega) le_rfl
    rw [lvlQ_zero, one_mul, ← Finset.range_eq_Ico] at h1
    have e1 := lvlQ_mul_pow q (s := w) (j := b) (by omega)
    have e2 := lvlQ_mul_pow q (s := w) (j := w.length) le_rfl
    have e3 := lvlQ_mul_pow q (s := w) (j := b + p2Q q a) (by omega)
    rw [hw, order_take_upDownQ, ← hw] at e1 e2 e3
    rw [min_eq_left (by omega : b ≤ a + b)] at e1
    rw [min_eq_right (by omega : a + b ≤ w.length)] at e2
    rw [min_eq_right (by omega : a + b ≤ b + p2Q q a)] at e3
    have hsplit : (2 : ℚ) ^ b * 2 ^ w.length = 2 ^ (b + p2Q q a) * 2 ^ p2Q q b := by
      rw [← pow_add, ← pow_add, hlen]
      congr 1
      omega
    have hspec : (q : ℚ) ^ b < 2 ^ p2Q q b := by exact_mod_cast p2Q_spec hq b
    have hqn : (0 : ℚ) < (q : ℚ) ^ (a + b) := by positivity
    have hj0 : 0 < lvlQ q w (b + p2Q q a) := lvlQ_pos hq0 w _
    have hlt : lvlQ q w b * lvlQ q w w.length < lvlQ q w (b + p2Q q a) := by
      have hC : (0 : ℚ) < 2 ^ b * 2 ^ w.length := by positivity
      apply lt_of_mul_lt_mul_right _ hC.le
      calc lvlQ q w b * lvlQ q w w.length * (2 ^ b * 2 ^ w.length)
          = lvlQ q w b * 2 ^ b * (lvlQ q w w.length * 2 ^ w.length) := by ring
        _ = (q : ℚ) ^ (a + b) * (q : ℚ) ^ b := by rw [e1, e2, mul_comm]
        _ < (q : ℚ) ^ (a + b) * 2 ^ p2Q q b := mul_lt_mul_of_pos_left hspec hqn
        _ = lvlQ q w (b + p2Q q a) * 2 ^ (b + p2Q q a) * 2 ^ p2Q q b := by rw [e3]
        _ = lvlQ q w (b + p2Q q a) * (2 ^ b * 2 ^ w.length) := by rw [hsplit, mul_assoc]
    rw [hTdef, Finset.prod_union hdisj, h1]
    apply lt_of_mul_lt_mul_left _ hj0.le
    rw [mul_one]
    calc lvlQ q w (b + p2Q q a) * (lvlQ q w b *
          ∏ i ∈ Finset.Ico (b + p2Q q a) w.length, factorQ q (w.getD i false))
        = lvlQ q w b * (lvlQ q w (b + p2Q q a) *
          ∏ i ∈ Finset.Ico (b + p2Q q a) w.length, factorQ q (w.getD i false)) := by ring
      _ = lvlQ q w b * lvlQ q w w.length := by rw [h2]
      _ < lvlQ q w (b + p2Q q a) := hlt
  intro hin
  have hA := ((mem_admSetQ (by omega) _ _).mp hin).1
  have hpL : p2Q q b < (startSweepQ q w).length := by
    rw [length_startSweepQ, hlen]
    omega
  have hgt := hA.prefix_gt (p2Q q b) (one_le_p2Q q b) hpL
  rw [← hcard, seqProductQ_take_startSweepQ hT hlow] at hgt
  linarith

end AcceleratedCollatz
