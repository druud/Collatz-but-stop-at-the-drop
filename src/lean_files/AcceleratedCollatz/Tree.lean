-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Numlib

/-!
  Tree/accumulator machinery for the lexicographic enumeration (paper
  sec:fast, `lex_enumeration`). Increasing enumeration via
  `gapOk_preserved` (GapOk is closed under `nextLevel`).
-/

namespace AcceleratedCollatz

/-- One child of accumulator `t` under exponent increment `m`, indexed by
    `i` (the trailing-zero-bit position being flipped): the step
    `s -> (s + 2^i) << m` of `a_iter_R` (paper app:pari; there the bit is
    i - 1 and m = w - u). -/
def childAt (t m i : ℕ) : ℕ := (t + 2 ^ i) <<< m

/-- Number of children a parent accumulator `t` spawns: 1 for `t = 0`
    (the sole order-0 root), else `trailingZeros t` (0 for odd `t`: no
    children). -/
def childCount (t : ℕ) : ℕ := if t = 0 then 1 else trailingZeros t

/-- All children of one parent `t` under increment `m` (paper app:pari,
    the inner `vector`). -/
def childrenOf (t m : ℕ) : List ℕ :=
  (List.range (childCount t)).map (childAt t m)

/-- One full order-transition: children of every parent, concatenated in
    parent order (paper app:pari, `concat(apply(...))` over the rows of one
    Order). -/
def nextLevel (parents : List ℕ) (m : ℕ) : List ℕ :=
  parents.flatMap (childrenOf · m)

/-- Gap invariant: a parent's FULL band of children -- `[a+1, a+2^count]`
    before the `<<m` shift -- stays clear of the next parent. -/
def GapOk (level : List ℕ) : Prop :=
  level.IsChain (fun a b => a + 2 ^ (childCount a) ≤ b)

/-- For i < trailingZeros t (t != 0), t + 2^i has trailingZeros exactly i. -/
theorem trailingZeros_add_pow_eq (t i : ℕ) (_ht : t ≠ 0) (hi : i < trailingZeros t) :
    trailingZeros (t + 2 ^ i) = i := by
  unfold trailingZeros at *
  have hdvd_ip1 : 2 ^ (i + 1) ∣ t :=
    dvd_trans (pow_dvd_pow 2 hi) pow_padicValNat_dvd
  obtain ⟨s, hs⟩ := hdvd_ip1
  have heq : t + 2 ^ i = 2 ^ i * (2 * s + 1) := by
    rw [hs]
    ring
  rw [heq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
  have hodd : padicValNat 2 (2 * s + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by omega)
  omega

theorem gapOk_base : GapOk [0] := by
  unfold GapOk
  exact List.isChain_singleton 0

/-- Within one parent `t`, consecutive children (index i, i+1 with
    i+1 < childCount t): the child at i plus 2^(its childCount) is the child
    at i+1. -/
theorem gapOk_within_parent (t m i : ℕ) (ht : t ≠ 0) (hi : i + 1 < childCount t) :
    childAt t m i + 2 ^ (childCount (childAt t m i)) = childAt t m (i + 1) := by
  have hcc : childCount t = trailingZeros t := ite_eq_right ht
  have hiv2 : i < trailingZeros t := by omega
  have hv2eq : trailingZeros (t + 2 ^ i) = i := trailingZeros_add_pow_eq t i ht hiv2
  unfold childAt
  have hne : t + 2 ^ i ≠ 0 := by positivity
  have hcc_child : childCount ((t + 2 ^ i) <<< m) = i + m := by
    unfold childCount
    have hne2 : (t + 2 ^ i) <<< m ≠ 0 := by
      rw [Nat.shiftLeft_eq]
      positivity
    rw [ite_eq_right hne2, Nat.shiftLeft_eq]
    unfold trailingZeros
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [padicValNat.mul hne (by positivity)]
    unfold trailingZeros at hv2eq
    rw [hv2eq, padicValNat.prime_pow]
  rw [hcc_child, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  ring

/-- Across two adjacent parents a, b with childCount a > 0: if
    a + 2^(childCount a) ≤ b, then the last child of a plus 2^(its
    childCount) is at most the first child of b. Covers a = 0. -/
theorem gapOk_step_adjacent (a b m : ℕ) (hb_pos : childCount a > 0)
    (hgap : a + 2 ^ (childCount a) ≤ b) :
    childAt a m (childCount a - 1) + 2 ^ (childCount (childAt a m (childCount a - 1)))
      ≤ childAt b m 0 := by
  set A' := a + 2 ^ (childCount a - 1) with hA'_def
  have hv2A' : trailingZeros A' = childCount a - 1 := by
    by_cases ha : a = 0
    · subst ha
      have : childCount (0:ℕ) = 1 := by
        unfold childCount
        simp
      rw [this] at hA'_def ⊢
      simp only [tsub_self] at hA'_def
      rw [hA'_def]
      unfold trailingZeros
      simp
    · have hcc : childCount a = trailingZeros a := ite_eq_right ha
      have hi : childCount a - 1 < trailingZeros a := by omega
      exact trailingZeros_add_pow_eq a (childCount a - 1) ha hi
  have hA'ne : A' ≠ 0 := by
    rw [hA'_def]
    positivity
  have hcc_last : childCount (A' <<< m) = (childCount a - 1) + m := by
    have hne2 : A' <<< m ≠ 0 := by
      rw [Nat.shiftLeft_eq]
      positivity
    have hccA' : childCount (A' <<< m) = trailingZeros (A' <<< m) := ite_eq_right hne2
    rw [hccA', Nat.shiftLeft_eq]
    unfold trailingZeros
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [padicValNat.mul hA'ne (by positivity)]
    unfold trailingZeros at hv2A'
    rw [hv2A', padicValNat.prime_pow]
  unfold childAt
  rw [← hA'_def, hcc_last]
  have key : A' + 2 ^ (childCount a - 1) ≤ b + 1 := by
    have h2 : (2:ℕ) ^ (childCount a - 1) + 2 ^ (childCount a - 1) = 2 ^ (childCount a) := by
      have hpos : childCount a - 1 + 1 = childCount a := by omega
      calc (2:ℕ) ^ (childCount a - 1) + 2 ^ (childCount a - 1)
          = 2 * 2 ^ (childCount a - 1) := by ring
        _ = 2 ^ (childCount a - 1 + 1) := by
          rw [pow_succ]
          ring
        _ = 2 ^ (childCount a) := by rw [hpos]
    rw [hA'_def]
    omega
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  simp only [pow_zero]
  have hthis : (A' + 2 ^ (childCount a - 1)) * 2 ^ m ≤ (b + 1) * 2 ^ m :=
    Nat.mul_le_mul_right _ key
  have hsplit : (2:ℕ) ^ (childCount a - 1 + m) = 2 ^ (childCount a - 1) * 2 ^ m := pow_add 2 _ m
  nlinarith [hthis, hsplit]

/-- The head of a GapOk list is a lower bound for every later element. -/
theorem gapOk_head_le (a : ℕ) (l : List ℕ) (h : GapOk (a :: l)) :
    ∀ b ∈ l, a ≤ b := by
  induction l generalizing a with
  | nil => simp
  | cons c l' ih =>
    intro b hb
    have hac : a + 2 ^ (childCount a) ≤ c := (List.isChain_cons.mp h).1 c (by simp)
    have htail : GapOk (c :: l') := (List.isChain_cons.mp h).2
    have hale : a ≤ c := by
      have h1 : (1:ℕ) ≤ 2 ^ (childCount a) := Nat.one_le_two_pow
      omega
    rcases List.mem_cons.mp hb with hbc | hbl'
    · omega
    · have hcb : c ≤ b := ih c htail b hbl'
      omega

/-- The gap bound of the head of a GapOk list holds against every later
    element, not only its successor. -/
theorem gapOk_forward (a : ℕ) (l : List ℕ) (h : GapOk (a :: l)) :
    ∀ b ∈ l, a + 2 ^ (childCount a) ≤ b := by
  intro b hb
  cases l with
  | nil => simp at hb
  | cons c l' =>
    have hac : a + 2 ^ (childCount a) ≤ c := (List.isChain_cons.mp h).1 c (by simp)
    have htail : GapOk (c :: l') := (List.isChain_cons.mp h).2
    rcases List.mem_cons.mp hb with hbc | hbl'
    · omega
    · have hcb : c ≤ b := gapOk_head_le c l' htail b hbl'
      omega

theorem gapOk_singleton (x : ℕ) : GapOk [x] :=
  List.isChain_singleton x

/-- A mapped range with the gap relation between consecutive entries is
    GapOk, and its last element is f (n - 1). -/
theorem gapOk_of_rangeMap' (n : ℕ) (f : ℕ → ℕ) (hn : n > 0)
    (hstep : ∀ i, i + 1 < n → f i + 2 ^ (childCount (f i)) = f (i + 1)) :
    GapOk ((List.range n).map f) ∧ ((List.range n).map f).getLast? = some (f (n - 1)) := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      refine ⟨?_, ?_⟩
      · simp only [zero_add, List.range_one, List.map_cons, List.map_nil]
        exact gapOk_singleton (f 0)
      · simp [List.range_succ, List.range_zero]
    · obtain ⟨ihchain, ihlast⟩ := ih hkpos (fun i hi => hstep i (by omega))
      have hstep_last : f (k - 1) + 2 ^ (childCount (f (k - 1))) = f k := by
        have := hstep (k - 1) (by omega)
        rwa [Nat.sub_add_cancel hkpos] at this
      rw [List.range_succ, List.map_append]
      refine ⟨?_, by simp⟩
      rw [GapOk, List.isChain_append]
      refine ⟨ihchain, gapOk_singleton (f k), ?_⟩
      intro x hx y hy
      have hx' : x = f (k - 1) := by
        rw [ihlast] at hx
        simp at hx
        omega
      have hy' : y = f k := by
        simp at hy
        omega
      rw [hx', hy']
      omega

/-- `gapOk_of_rangeMap'` for every n, the empty list (n = 0) included. -/
theorem gapOk_of_rangeMap (n : ℕ) (f : ℕ → ℕ)
    (hstep : ∀ i, i + 1 < n → f i + 2 ^ (childCount (f i)) = f (i + 1)) :
    GapOk ((List.range n).map f) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp [GapOk]
  · exact (gapOk_of_rangeMap' n f hnpos hstep).1

/-- The children list of one parent is GapOk. -/
theorem gapOk_childrenOf (t m : ℕ) : GapOk (childrenOf t m) := by
  unfold childrenOf
  apply gapOk_of_rangeMap
  intro i hi
  by_cases ht : t = 0
  · exfalso
    have hcc0 : childCount (0:ℕ) = 1 := by
      unfold childCount
      simp
    rw [ht, hcc0] at hi
    omega
  · exact gapOk_within_parent t m i ht hi

/-- `List.range (n+1)` starts at 0. -/
theorem range_succ_head (n : ℕ) : (List.range (n + 1)).head? = some 0 := by
  induction n with
  | zero => simp [List.range_succ, List.range_zero]
  | succ j ih =>
    rw [List.range_succ]
    rcases hR : List.range (j + 1) with _ | ⟨a, t⟩
    · rw [hR] at ih
      simp at ih
    · rw [hR] at ih
      simp only [List.head?_cons, Option.some.injEq] at ih
      subst ih
      simp

/-- `nextLevel` of a cons: the children of the head, then `nextLevel` of
    the rest. -/
theorem nextLevel_cons (c : ℕ) (rest : List ℕ) (m : ℕ) :
    nextLevel (c :: rest) m = childrenOf c m ++ nextLevel rest m := by
  unfold nextLevel
  rw [List.flatMap_cons]

/-- The head of `nextLevel rest m`, if it exists, is the first child
    (index 0) of some parent b in `rest` with childCount b > 0. -/
theorem nextLevel_head_eq (rest : List ℕ) (m y : ℕ)
    (hy : (nextLevel rest m).head? = some y) :
    ∃ b ∈ rest, childCount b > 0 ∧ y = childAt b m 0 := by
  induction rest with
  | nil => simp [nextLevel] at hy
  | cons c rest' ih =>
    rw [nextLevel_cons] at hy
    rcases Nat.eq_zero_or_pos (childCount c) with hc0 | hcpos
    · have hempty : childrenOf c m = [] := by
        unfold childrenOf
        rw [hc0]
        simp
      rw [hempty, List.nil_append] at hy
      obtain ⟨b, hb, hbpos, hbeq⟩ := ih hy
      exact ⟨b, List.mem_cons_of_mem c hb, hbpos, hbeq⟩
    · have hheadc : (childrenOf c m).head? = some (childAt c m 0) := by
        unfold childrenOf
        rw [List.head?_map]
        have hrange0 : (List.range (childCount c)).head? = some 0 := by
          cases hcc : childCount c with
          | zero => omega
          | succ k => exact range_succ_head k
        rw [hrange0]
        simp
      have hheadapp : (childrenOf c m ++ nextLevel rest' m).head? = (childrenOf c m).head? := by
        cases hcm : childrenOf c m with
        | nil =>
          rw [hcm] at hheadc
          exact absurd hheadc (by simp)
        | cons a l => simp
      rw [hheadapp, hheadc] at hy
      simp only [Option.some.injEq] at hy
      exact ⟨c, List.mem_cons_self, hcpos, hy.symm⟩

/-- GapOk is preserved by `nextLevel`. -/
theorem gapOk_preserved (parents : List ℕ) (m : ℕ) (h : GapOk parents) :
    GapOk (nextLevel parents m) := by
  induction parents with
  | nil => simp [nextLevel, GapOk]
  | cons p rest ih =>
    have hrest : GapOk rest := (List.isChain_cons.mp h).2
    rw [nextLevel_cons, GapOk, List.isChain_append]
    refine ⟨gapOk_childrenOf p m, ih hrest, ?_⟩
    intro x hx y hy
    obtain ⟨b, hb_mem, hb_pos, hb_eq⟩ := nextLevel_head_eq rest m y hy
    have hgap : p + 2 ^ (childCount p) ≤ b := gapOk_forward p rest h b hb_mem
    have hppos : childCount p > 0 := by
      by_contra hzero
      push Not at hzero
      have : childrenOf p m = [] := by
        unfold childrenOf
        simp [Nat.le_zero.mp hzero]
      rw [this] at hx
      simp at hx
    have hlast_eq : x = childAt p m (childCount p - 1) := by
      have hstep : ∀ i, i + 1 < childCount p →
          childAt p m i + 2 ^ (childCount (childAt p m i)) = childAt p m (i + 1) := by
        intro i hi
        by_cases hp0 : p = 0
        · exfalso
          have : childCount (0:ℕ) = 1 := by
            unfold childCount
            simp
          rw [hp0, this] at hi
          omega
        · exact gapOk_within_parent p m i hp0 hi
      have hget := (gapOk_of_rangeMap' (childCount p) (childAt p m) hppos hstep).2
      unfold childrenOf at hx
      rw [hget] at hx
      simpa using hx.symm
    rw [hlast_eq, hb_eq]
    exact gapOk_step_adjacent p b m hppos hgap

/-- A GapOk list has no duplicates. -/
theorem gapOk_nodup (l : List ℕ) (h : GapOk l) : l.Nodup := by
  have hlt : l.IsChain (· < ·) :=
    h.imp_of_mem_imp (fun a b _ _ hR => by
      have : (1:ℕ) ≤ 2 ^ (childCount a) := Nat.one_le_two_pow
      omega)
  rw [List.isChain_iff_pairwise] at hlt
  exact hlt.nodup

end AcceleratedCollatz
