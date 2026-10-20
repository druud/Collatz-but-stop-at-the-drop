-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRecordFloor

/-!
  The walk of the A003586 program from (u, v) = (1, 1) to the last record Orders below N
  (`recordWalk`). It keeps d = u P - (p2(u) - 1) Q and e = p2(v) Q - v P for a record
  fraction P/Q with N ≤ Q; the next record Order is u + v, a lower one when e < d (then
  u becomes u + v and d becomes d - e) and an upper one otherwise (then v becomes u + v
  and e becomes e - d). It stops at the first u + v ≥ N, with u and v the last lower and
  the last upper record Order below N (`recordWalk_spec`).
-/

namespace AcceleratedCollatz

/-- The walk of the A003586 program towards the last record Orders below N. -/
def recordWalk (N u v d e : ℕ) : ℕ × ℕ :=
  if 0 < u ∧ 0 < v ∧ u + v < N then
    if e < d then recordWalk N (u + v) v (d - e) e
    else recordWalk N u (u + v) d (e - d)
  else (u, v)
termination_by N - (u + v)

/-- `LastRecords a b K` stays true for a smaller N, as long as a, b < N. -/
theorem lastRecords_of_le {a b K N : ℕ} (h : LastRecords a b K) (haN : a < N) (hbN : b < N)
    (hNK : N ≤ K) : LastRecords a b N where
  one_le_lower := h.one_le_lower
  lower_lt := haN
  lower := h.lower
  no_lower := fun x hx hxN => h.no_lower x hx (by omega)
  one_le_upper := h.one_le_upper
  upper_lt := hbN
  upper := h.upper
  no_upper := fun x hx hxN => h.no_upper x hx (by omega)

/-- With a, b the last record Orders below a + b, the Order a + b is a lower record Order
    with p2(a + b) = p2(a) + p2(b), or an upper one with p2(a + b) + 1 = p2(a) + p2(b). -/
theorem record_add_cases {a b : ℕ} (h : LastRecords a b (a + b)) :
    (LowerRecord (a + b) ∧ p2_of (a + b) = p2_of a + p2_of b) ∨
      (UpperRecord (a + b) ∧ p2_of (a + b) + 1 = p2_of a + p2_of b) := by
  have ha1 := h.one_le_lower
  have hb1 := h.one_le_upper
  by_cases hL : LowerRecord (a + b)
  · left
    refine ⟨hL, ?_⟩
    have hnU : ¬UpperRecord (a + b) := fun hU =>
      not_lowerRecordQ_of_upperRecordQ le_rfl (by omega) hU hL
    have hnone : ∀ x, b < x → x < a + b + 1 → ¬UpperRecord x := by
      intro x hbx hx
      rcases Nat.lt_or_ge x (a + b) with hlt | hge
      · exact h.no_upper x hbx hlt
      · have : x = a + b := by omega
        rw [this]
        exact hnU
    have : p2_of (b + a) = p2_of b + p2_of a :=
      p2Q_add_of_upperRecordQ (by decide) le_rfl h.upper hnone ha1 (by omega)
    rw [Nat.add_comm b a] at this
    omega
  · by_cases hU : UpperRecord (a + b)
    · right
      refine ⟨hU, ?_⟩
      have hnone : ∀ x, a < x → x < a + b + 1 → ¬LowerRecord x := by
        intro x hax hx
        rcases Nat.lt_or_ge x (a + b) with hlt | hge
        · exact h.no_lower x hax hlt
        · have : x = a + b := by omega
          rw [this]
          exact hL
      exact p2_of_add_of_lowerRecord h.lower hnone hb1 (by omega)
    · exfalso
      have h' : LastRecords a b (a + b + 1) := lastRecordsQ_succ h hL hU
      have := le_add_of_lastRecords h'
      omega

/-- The walk ends at the last record Orders below N: from a pair u, v below N that are the
    last record Orders below u + v, with d and e as above, for a record fraction P/Q with
    N ≤ Q. -/
theorem recordWalk_spec {P Q N : ℕ} (hPQ : RecordFrac P Q) (hNQ : N ≤ Q) :
    ∀ u v d e, LastRecords u v (u + v) → u < N → v < N →
      d = u * P - (p2_of u - 1) * Q → e = p2_of v * Q - v * P →
        LastRecords (recordWalk N u v d e).1 (recordWalk N u v d e).2 N := by
  intro u v d e
  induction u, v, d, e using recordWalk.induct N with
  | case1 u v d e hc hed ih =>
    intro h huN hvN hd he
    rw [recordWalk]
    simp only [hc, hed, and_self, ↓reduceIte]
    obtain ⟨hu0, hv0, hK⟩ := hc
    obtain ⟨hlu, hhu⟩ := record_mul_bounds hPQ hu0 (by omega)
    obtain ⟨hlv, hhv⟩ := record_mul_bounds hPQ hv0 (by omega)
    obtain ⟨hlK, hhK⟩ := record_mul_bounds hPQ (i := u + v) (by omega) (by omega)
    have hKP : (u + v) * P = u * P + v * P := Nat.add_mul u v P
    have hpu : 1 ≤ p2_of u := by
      have := p2_of_mono (Nat.zero_le u)
      have h0 : p2_of 0 = 1 := by
        unfold p2_of
        simp
      omega
    rcases record_add_cases h with ⟨hL, hp⟩ | ⟨hU, hp⟩
    · have hK1 : (p2_of (u + v) - 1) * Q = (p2_of u - 1) * Q + p2_of v * Q := by
        rw [← Nat.add_mul]
        congr 1
        omega
      have hL' : LastRecords (u + v) v (u + v + 1) := lastRecordsQ_succ_lower le_rfl h hL
      have hL'' : LastRecords (u + v) v (u + v + v) := lastRecordsQ_add (by decide) le_rfl hL'
      apply ih hL'' hK hvN
      · omega
      · exact he
    · exfalso
      have hK1 : p2_of (u + v) * Q = (p2_of u - 1) * Q + p2_of v * Q := by
        rw [← Nat.add_mul]
        congr 1
        omega
      omega
  | case2 u v d e hc hed ih =>
    intro h huN hvN hd he
    rw [recordWalk]
    simp only [hc, hed, and_self, ↓reduceIte]
    obtain ⟨hu0, hv0, hK⟩ := hc
    obtain ⟨hlu, hhu⟩ := record_mul_bounds hPQ hu0 (by omega)
    obtain ⟨hlv, hhv⟩ := record_mul_bounds hPQ hv0 (by omega)
    obtain ⟨hlK, hhK⟩ := record_mul_bounds hPQ (i := u + v) (by omega) (by omega)
    have hKP : (u + v) * P = u * P + v * P := Nat.add_mul u v P
    have hpu : 1 ≤ p2_of u := by
      have := p2_of_mono (Nat.zero_le u)
      have h0 : p2_of 0 = 1 := by
        unfold p2_of
        simp
      omega
    rcases record_add_cases h with ⟨hL, hp⟩ | ⟨hU, hp⟩
    · exfalso
      have hK1 : (p2_of (u + v) - 1) * Q = (p2_of u - 1) * Q + p2_of v * Q := by
        rw [← Nat.add_mul]
        congr 1
        omega
      omega
    · have hK1 : p2_of (u + v) * Q = (p2_of u - 1) * Q + p2_of v * Q := by
        rw [← Nat.add_mul]
        congr 1
        omega
      have hU' : LastRecords u (u + v) (u + v + 1) := lastRecordsQ_succ_upper le_rfl h hU
      have hU'' : LastRecords u (u + v) (u + (u + v)) := lastRecordsQ_add (by decide) le_rfl hU'
      apply ih hU'' huN hK
      · exact hd
      · omega
  | case3 u v d e hc =>
    intro h huN hvN _ _
    rw [recordWalk]
    simp only [hc, ↓reduceIte]
    have hu0 := h.one_le_lower
    have hv0 := h.one_le_upper
    exact lastRecords_of_le h huN hvN (by omega)

end AcceleratedCollatz
