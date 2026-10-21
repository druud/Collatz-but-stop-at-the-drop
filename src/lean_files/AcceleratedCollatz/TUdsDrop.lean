-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TNest
import AcceleratedCollatz.TUds

/-!
  The stop of the three letters and the drop under T (paper sec:three). Each value the
  letters reach stands on the T-path of k, or one T-step before it after a letter S
  (`udsTrace_iterate`), and every odd value of that path up to the letters' Order is
  reached (`exists_udsStep_iterate_eq`). So M, the Order of the letters up to the stop, is
  at most the Order of the drop, with equality exactly for a stop by D
  (`le_order_of_isUdsStop`); a stop by S is a merge before the drop
  (`isUdsStop_of_S`), and no stop is by U (`udsOf_isUdsStop_ne_U`).
-/

namespace AcceleratedCollatz

/-- z on the T-path of k at step n with Order u before it (`false`), or one T-step from z
    to step n, the Order there u + 1 (`true`). -/
def UdsTrace (k z n u : ℕ) : Bool → Prop
  | false => z = tStep^[n] k ∧ order (tBits k n) = u
  | true => tStep z = tStep^[n] k ∧ order (tBits k n) = u + 1

theorem udsWord_succ' (k n : ℕ) :
    udsWord k (n + 1) = udsWord k n ++ [udsOf (udsStep^[n] k)] := by
  induction n generalizing k with
  | zero =>
    rfl
  | succ n ih =>
    rw [udsWord_succ, ih (udsStep k), udsWord_succ, Function.iterate_succ_apply]
    rfl

theorem order_udsBits_udsWord_succ (k n : ℕ) :
    order (udsBits (udsWord k (n + 1))) =
      order (udsBits (udsWord k n)) + order (udsOf (udsStep^[n] k)).bits := by
  rw [udsWord_succ', udsBits_append, order_append]
  simp [udsBits]

theorem order_tBits_add (x n a : ℕ) :
    order (tBits x (n + a)) = order (tBits x n) + order (tBits (tStep^[n] x) a) := by
  rw [tBits_add, order_append]

theorem order_tBits_one_of_odd (y : ℕ) (h : y % 2 = 1) : order (tBits y 1) = 1 := by
  simp [tBits, order, h]

theorem order_tBits_one_of_even (y : ℕ) (h : y % 2 = 0) : order (tBits y 1) = 0 := by
  simp [tBits, order, h]

/-- U is one odd T-step. -/
theorem tStep_of_U (z : ℕ) (h : z % 4 = 3) : tStep z = udsStep z := by
  have hz : z % 2 = 1 := by omega
  rw [tStep_odd z hz]
  simp [udsStep, udsOf, h]

/-- D is an odd and an even T-step. -/
theorem tStep_tStep_of_D (z : ℕ) (h : z % 8 = 1) :
    tStep z % 2 = 0 ∧ tStep (tStep z) = udsStep z := by
  have hz : z % 2 = 1 := by omega
  have h4 : z % 4 ≠ 3 := by omega
  rw [tStep_odd z hz]
  have he : (3 * z + 1) / 2 % 2 = 0 := by omega
  refine ⟨he, ?_⟩
  rw [tStep_even _ (by omega)]
  simp only [udsStep, udsOf, h4, h, ↓reduceIte]
  omega

/-- After S one T-step lands where z lands after an odd and two even T-steps. -/
theorem tStep_of_S (z : ℕ) (h : z % 8 = 5) :
    tStep z % 2 = 0 ∧ tStep (tStep z) % 2 = 0 ∧
      tStep (tStep (tStep z)) = tStep (udsStep z) := by
  have hz : z % 2 = 1 := by omega
  have h4 : z % 4 ≠ 3 := by omega
  have h8 : z % 8 ≠ 1 := by omega
  rw [tStep_odd z hz]
  have he1 : (3 * z + 1) / 2 % 2 = 0 := by omega
  rw [tStep_even _ (by omega)]
  have he2 : (3 * z + 1) / 2 / 2 % 2 = 0 := by omega
  refine ⟨he1, he2, ?_⟩
  rw [tStep_even _ (by omega)]
  have hs : udsStep z = (z - 1) / 4 := by
    simp [udsStep, udsOf, h4, h8]
  have ho : (z - 1) / 4 % 2 = 1 := by omega
  rw [hs, tStep_odd _ ho]
  omega

theorem tBits_of_D (z : ℕ) (h : z % 8 = 1) : tBits z 2 = [true, false] := by
  have hz : z % 2 = 1 := by omega
  have he := (tStep_tStep_of_D z h).1
  simp only [tBits, hz, he]
  rfl

theorem tBits_of_S (z : ℕ) (h : z % 8 = 5) :
    tBits z 3 = [true, false, false] ∧ tBits (tStep z) 2 = [false, false] := by
  have hz : z % 2 = 1 := by omega
  obtain ⟨he1, he2, -⟩ := tStep_of_S z h
  constructor
  · simp only [tBits, hz, he1, he2]
    rfl
  · simp only [tBits, he1, he2]
    rfl

/-- One letter moves the trace along the T-path of k. -/
theorem udsTrace_step (k z n u : ℕ) (e : Bool) (hz : z % 2 = 1) (h : UdsTrace k z n u e) :
    ∃ n', UdsTrace k (udsStep z) n' (u + order (udsOf z).bits) (decide (udsOf z = .S)) := by
  unfold udsOf
  split_ifs with h1 h2
  · have hU := tStep_of_U z h1
    cases e with
    | false =>
      obtain ⟨hzn, hu⟩ := h
      refine ⟨n + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', ← hzn, hU]
      · rw [order_tBits_add, ← hzn, order_tBits_one_of_odd z hz, hu]
        rfl
    | true =>
      obtain ⟨hzn, hu⟩ := h
      refine ⟨n, ?_, ?_⟩
      · rw [← hzn, hU]
      · rw [hu]
        rfl
  · obtain ⟨he, hD⟩ := tStep_tStep_of_D z h2
    cases e with
    | false =>
      obtain ⟨hzn, hu⟩ := h
      refine ⟨n + 2, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← hzn, hD]
      · rw [order_tBits_add, ← hzn, hu, tBits_of_D z h2]
        rfl
    | true =>
      obtain ⟨hzn, hu⟩ := h
      refine ⟨n + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', ← hzn, hD]
      · rw [order_tBits_add, ← hzn, order_tBits_one_of_even _ he, hu]
        rfl
  · have h5 : z % 8 = 5 := by omega
    obtain ⟨he1, he2, hS⟩ := tStep_of_S z h5
    cases e with
    | false =>
      obtain ⟨hzn, hu⟩ := h
      refine ⟨n + 3, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', ← hzn, hS]
      · rw [order_tBits_add, ← hzn, hu, (tBits_of_S z h5).1]
        rfl
    | true =>
      obtain ⟨hzn, hu⟩ := h
      refine ⟨n + 2, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← hzn, hS]
      · rw [order_tBits_add, ← hzn, hu, (tBits_of_S z h5).2]
        rfl

/-- Every value the letters reach stands on the T-path of k, or one T-step before it. -/
theorem udsTrace_iterate (k : ℕ) (hk : k % 2 = 1) (i : ℕ) :
    ∃ n e, UdsTrace k (udsStep^[i] k) n (order (udsBits (udsWord k i))) e := by
  induction i with
  | zero =>
    exact ⟨0, false, rfl, rfl⟩
  | succ i ih =>
    obtain ⟨n, e, h⟩ := ih
    obtain ⟨n', h'⟩ := udsTrace_step k _ n _ e (udsStep_iterate_odd k hk i) h
    rw [Function.iterate_succ_apply', order_udsBits_udsWord_succ]
    exact ⟨n', _, h'⟩

/-- After letter i + 1 the trace is on the path exactly when that letter is U or D. -/
theorem udsTrace_iterate_succ (k : ℕ) (hk : k % 2 = 1) (i : ℕ) :
    ∃ n, UdsTrace k (udsStep^[i + 1] k) n (order (udsBits (udsWord k (i + 1))))
      (decide (udsOf (udsStep^[i] k) = .S)) := by
  obtain ⟨n, e, h⟩ := udsTrace_iterate k hk i
  obtain ⟨n', h'⟩ := udsTrace_step k _ n _ e (udsStep_iterate_odd k hk i) h
  rw [Function.iterate_succ_apply', order_udsBits_udsWord_succ]
  exact ⟨n', h'⟩

/-- Every Order up to that of the first i letters is reached on the T-path of k by a
    value of the letters. -/
theorem exists_udsStep_iterate_eq (k : ℕ) (hk : k % 2 = 1) (i u : ℕ)
    (hu : u ≤ order (udsBits (udsWord k i))) :
    ∃ i' ≤ i, ∃ n, udsStep^[i'] k = tStep^[n] k ∧ order (tBits k n) = u := by
  induction i generalizing u with
  | zero =>
    have hu0 : u = 0 := by simpa [udsWord, order] using hu
    exact ⟨0, le_rfl, 0, rfl, by simp [hu0, tBits, order]⟩
  | succ i ih =>
    rw [order_udsBits_udsWord_succ] at hu
    by_cases hle : u ≤ order (udsBits (udsWord k i))
    · obtain ⟨i', hi', n, h⟩ := ih u hle
      exact ⟨i', by omega, n, h⟩
    · obtain ⟨n, h⟩ := udsTrace_iterate_succ k hk i
      have hS : udsOf (udsStep^[i] k) ≠ .S := by
        intro hS
        rw [hS] at hu
        have h0 : order UDS.S.bits = 0 := rfl
        omega
      have hfalse : decide (udsOf (udsStep^[i] k) = .S) = false := decide_eq_false hS
      rw [hfalse] at h
      obtain ⟨hz, ho⟩ := h
      have hc : order (udsOf (udsStep^[i] k)).bits ≤ 1 := by
        cases udsOf (udsStep^[i] k) with
        | U =>
          decide
        | D =>
          decide
        | S =>
          decide
      rw [order_udsBits_udsWord_succ] at ho
      exact ⟨i + 1, le_rfl, n, hz, by omega⟩

/-- Order 0 after a steps: the value does not grow. -/
theorem tStep_iterate_le_of_order_zero (y a : ℕ) (h : order (tBits y a) = 0) :
    tStep^[a] y ≤ y := by
  induction a generalizing y with
  | zero =>
    exact le_rfl
  | succ a ih =>
    rw [tBits, order_cons] at h
    have hy : y % 2 ≠ 1 := by
      intro hy
      simp [hy] at h
    have ht : order (tBits (tStep y) a) = 0 := by
      simp only [hy, decide_false, Bool.false_eq_true, ↓reduceIte] at h
      omega
    have := ih (tStep y) ht
    rw [tStep_even y hy] at this
    rw [Function.iterate_succ_apply, tStep_even y hy]
    omega

/-- An odd value of the T-path is at most every value with the same Order before it. -/
theorem tStep_iterate_le_of_order_eq (x m n : ℕ) (hm : tStep^[m] x % 2 = 1)
    (h : order (tBits x m) = order (tBits x n)) : tStep^[m] x ≤ tStep^[n] x := by
  rcases le_or_gt n m with hnm | hmn
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [order_tBits_add] at h
    have h0 : order (tBits (tStep^[n] x) a) = 0 := by omega
    rw [Nat.add_comm n a, Function.iterate_add_apply]
    exact tStep_iterate_le_of_order_zero _ a h0
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [Nat.add_assoc, order_tBits_add x m (a + 1), Nat.add_comm a 1,
      tBits_add (tStep^[m] x) 1 a, order_append, order_tBits_one_of_odd _ hm] at h
    omega

/-- Before the stop the T-path of k stays at or above k at every Order up to the letters'. -/
theorem le_tStep_iterate (k i : ℕ) (hk : k % 2 = 1)
    (hmin : ∀ i' ≤ i, k ≤ udsStep^[i'] k) (n : ℕ)
    (hn : order (tBits k n) ≤ order (udsBits (udsWord k i))) : k ≤ tStep^[n] k := by
  obtain ⟨i', hi', m, hz, ho⟩ := exists_udsStep_iterate_eq k hk i _ hn
  have hodd : tStep^[m] k % 2 = 1 := by
    rw [← hz]
    exact udsStep_iterate_odd k hk i'
  have hle := tStep_iterate_le_of_order_eq k m n hodd (by rw [ho])
  have := hmin i' hi'
  omega

theorem isUdsStop_pos (k j : ℕ) (hs : IsUdsStop k j) : 1 ≤ j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    exact absurd hs.1 (lt_irrefl k)
  · exact h

/-- No stop is by U. -/
theorem udsOf_isUdsStop_ne_U (k j : ℕ) (hs : IsUdsStop k j) :
    udsOf (udsStep^[j - 1] k) ≠ .U := by
  have hj := isUdsStop_pos k j hs
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  intro hU
  have hge := hs.2 i (by omega)
  have hlt := hs.1
  rw [Function.iterate_succ_apply'] at hlt
  rw [Nat.add_sub_cancel] at hU
  have hstep : udsStep (udsStep^[i] k) = (3 * udsStep^[i] k + 1) / 2 := by
    simp [udsStep, hU]
  rw [hstep] at hlt
  omega

/-- A stop by D is the drop: its value is the T-path's at the letters' Order M, and every
    first drop of k has Order M. -/
theorem isUdsStop_of_D (k j : ℕ) (hk : k % 2 = 1) (hs : IsUdsStop k j)
    (hD : udsOf (udsStep^[j - 1] k) = .D) :
    (∃ n, tStep^[n] k = udsStep^[j] k ∧ order (tBits k n) = order (udsBits (udsWord k j))) ∧
      ∀ n, IsFirstDrop (tTraj k) 0 n → order (tBits k n) = order (udsBits (udsWord k j)) := by
  have hj := isUdsStop_pos k j hs
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hD
  obtain ⟨n0, h⟩ := udsTrace_iterate_succ k hk i
  have hfalse : decide (udsOf (udsStep^[i] k) = .S) = false := by
    rw [hD]
    rfl
  rw [hfalse] at h
  obtain ⟨hz, ho⟩ := h
  refine ⟨⟨n0, hz.symm, ho⟩, fun n hn => ?_⟩
  obtain ⟨hn0, hlt, hmin⟩ := hn
  have hM : order (udsBits (udsWord k (i + 1))) = order (udsBits (udsWord k i)) + 1 := by
    rw [order_udsBits_udsWord_succ, hD]
    rfl
  have hmin' : ∀ i' ≤ i, k ≤ udsStep^[i'] k := fun i' hi' => hs.2 i' (by omega)
  have hge : order (udsBits (udsWord k (i + 1))) ≤ order (tBits k n) := by
    by_contra hlt'
    have := le_tStep_iterate k i hk hmin' n (by omega)
    exact absurd hlt (not_lt.mpr this)
  have hnn0 : n ≤ n0 := by
    by_contra hgt
    have hpos : 0 < n0 := by
      rcases Nat.eq_zero_or_pos n0 with h0 | h0
      · rw [h0] at hz
        have := hs.1
        rw [hz] at this
        exact absurd this (lt_irrefl k)
      · exact h0
    have := hmin n0 hpos (by omega)
    have hs1 := hs.1
    rw [hz] at hs1
    exact absurd hs1 (not_lt.mpr this)
  have hle := order_tBits_mono k n n0 hnn0
  omega

/-- A stop by S is a merge before the drop: the T-path of k stays at or above k up to the
    letters' Order M, and one T-step from the stop value lands on it at Order M + 1. -/
theorem isUdsStop_of_S (k j : ℕ) (hk : k % 2 = 1) (hs : IsUdsStop k j)
    (hS : udsOf (udsStep^[j - 1] k) = .S) :
    (∀ n, order (tBits k n) ≤ order (udsBits (udsWord k j)) → k ≤ tStep^[n] k) ∧
      ∃ n, tStep (udsStep^[j] k) = tStep^[n] k ∧
        order (tBits k n) = order (udsBits (udsWord k j)) + 1 := by
  have hj := isUdsStop_pos k j hs
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hS
  have hM : order (udsBits (udsWord k (i + 1))) = order (udsBits (udsWord k i)) := by
    rw [order_udsBits_udsWord_succ, hS]
    rfl
  refine ⟨fun n hn => ?_, ?_⟩
  · exact le_tStep_iterate k i hk (fun i' hi' => hs.2 i' (by omega)) n (by omega)
  · obtain ⟨n0, h⟩ := udsTrace_iterate_succ k hk i
    have htrue : decide (udsOf (udsStep^[i] k) = .S) = true := by
      rw [hS]
      rfl
    rw [htrue] at h
    exact ⟨n0, h⟩

/-- M, the Order of the letters up to the stop, is at most the Order of the drop, with
    equality exactly for a stop by D. -/
theorem le_order_of_isUdsStop (k j n : ℕ) (hk : k % 2 = 1) (hs : IsUdsStop k j)
    (hn : IsFirstDrop (tTraj k) 0 n) :
    order (udsBits (udsWord k j)) ≤ order (tBits k n) ∧
      (order (udsBits (udsWord k j)) = order (tBits k n) ↔
        udsOf (udsStep^[j - 1] k) = .D) := by
  have hU := udsOf_isUdsStop_ne_U k j hs
  cases hc : udsOf (udsStep^[j - 1] k) with
  | U =>
    exact absurd hc hU
  | D =>
    have h := (isUdsStop_of_D k j hk hs hc).2 n hn
    exact ⟨h.symm.le, ⟨fun _ => rfl, fun _ => h.symm⟩⟩
  | S =>
    have h := (isUdsStop_of_S k j hk hs hc).1 n
    have hgt : order (udsBits (udsWord k j)) < order (tBits k n) := by
      by_contra hle
      have := h (by omega)
      exact absurd hn.2.1 (not_lt.mpr this)
    refine ⟨hgt.le, ⟨fun heq => absurd heq (by omega), fun h' => ?_⟩⟩
    exact absurd h' (by decide)

end AcceleratedCollatz
