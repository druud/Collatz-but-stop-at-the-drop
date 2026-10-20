-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TLex
import Mathlib.Data.List.Lex

/-!
  sec:sorting, marked-vector part. On well-formed marked vectors (nonzero
  entries, no two adjacent negative entries) whose decoded bit strings have
  equal length, `decodeVector` preserves and reflects the lexicographic order
  (`decodeVector_lt_iff`). `markedVector` produces well-formed vectors
  (`markedWF_markedVector`). For class ids of Order p3 with rho < d_23 x,
  encodings, parity bits and marked vectors are sorted alike
  (`encode_lt_iff_markedVector_lt`).
-/

namespace AcceleratedCollatz

/-- Well-formed marked vector: nonzero entries, no two adjacent negative entries. -/
def MarkedWF (m : List ℤ) : Prop :=
  (∀ e ∈ m, e ≠ 0) ∧ m.IsChain (fun a b => 0 < a ∨ 0 < b)

theorem MarkedWF.tail {e : ℤ} {m : List ℤ} (h : MarkedWF (e :: m)) : MarkedWF m :=
  ⟨fun x hx => h.1 x (List.mem_cons_of_mem e hx), h.2.tail⟩

theorem MarkedWF.head_pos {e c : ℤ} {m : List ℤ} (h : MarkedWF (e :: c :: m)) (he : e < 0) :
    0 < c := by
  have hc := (List.isChain_cons_cons.mp h.2).1
  omega

/-- Split form of bit-string order: u ++ 0 :: v < u ++ 1 :: w. -/
theorem split_lt (u v w : List Bool) : u ++ false :: v < u ++ true :: w := by
  apply List.append_left_lt
  exact List.cons_lt_cons_iff.mpr (Or.inl (by decide))

/-- Split form and list order agree on bit strings of equal length. -/
theorem exists_split_iff_lt (s t : List Bool) (hlen : s.length = t.length) :
    (∃ u v w, s = u ++ false :: v ∧ t = u ++ true :: w) ↔ s < t := by
  constructor
  · rintro ⟨u, v, w, rfl, rfl⟩
    exact split_lt u v w
  · intro h
    induction s generalizing t with
    | nil =>
      cases t with
      | nil =>
        exact absurd h (List.not_lt_nil _)
      | cons c t =>
        simp at hlen
    | cons b s ih =>
      cases t with
      | nil =>
        exact absurd h (List.not_lt_nil _)
      | cons c t =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        rcases List.cons_lt_cons_iff.mp h with hbc | ⟨rfl, hst⟩
        · cases b
          · cases c
            · exact absurd hbc (by decide)
            · exact ⟨[], s, t, rfl, rfl⟩
          · cases c
            · exact absurd hbc (by decide)
            · exact absurd hbc (by decide)
        · obtain ⟨u, v, w, rfl, rfl⟩ := ih t hlen hst
          exact ⟨b :: u, v, w, rfl, rfl⟩

theorem replicate_split (x : Bool) (k j : ℕ) :
    List.replicate (k + 1 + j) x = List.replicate k x ++ x :: List.replicate j x := by
  rw [List.replicate_add, List.replicate_add]
  simp

theorem expandEntry_of_pos (e : ℤ) (he : 0 < e) :
    expandEntry e = List.replicate e.toNat true ++ [false] := by
  simp [expandEntry, he]

theorem expandEntry_of_neg (e : ℤ) (he : e < 0) :
    expandEntry e = List.replicate (-e).toNat false := by
  have hne : ¬ e > 0 := by omega
  simp [expandEntry, hne]

theorem decodeVector_ne_nil_of_mem {m : List ℤ} (h : ∀ e ∈ m, e ≠ 0) (hne : m ≠ []) :
    decodeVector m ≠ [] := by
  obtain ⟨e, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  have he := h e List.mem_cons_self
  rw [decodeVector_cons]
  rcases lt_or_gt_of_ne he with hlt | hgt
  · rw [expandEntry_of_neg e hlt]
    have hpos : 0 < (-e).toNat := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hpos
    rw [hk, zero_add, List.replicate_succ]
    simp
  · rw [expandEntry_of_pos e hgt]
    simp

/-- decodeVector is strictly monotone on well-formed vectors of equal decoded length. -/
theorem decodeVector_lt_of_lt :
    ∀ (m m' : List ℤ), MarkedWF m → MarkedWF m' →
      (decodeVector m).length = (decodeVector m').length → m < m' →
        decodeVector m < decodeVector m'
  | [], [], _, _, _, h => absurd h (List.not_lt_nil _)
  | [], b :: r', _, hm', hlen, _ => by
    have hne := decodeVector_ne_nil_of_mem hm'.1 (List.cons_ne_nil b r')
    have h0 : (decodeVector []).length = 0 := by
      simp [decodeVector]
    rw [h0, eq_comm, List.length_eq_zero_iff] at hlen
    exact absurd hlen hne
  | _ :: _, [], _, _, _, h => absurd h (List.not_lt_nil _)
  | a :: r, b :: r', hm, hm', hlen, h => by
    rw [decodeVector_cons, decodeVector_cons] at hlen ⊢
    rcases List.cons_lt_cons_iff.mp h with hab | ⟨rfl, hr⟩
    · have ha := hm.1 a List.mem_cons_self
      have hb := hm'.1 b List.mem_cons_self
      rcases lt_or_gt_of_ne ha with ha0 | ha0
      · rcases lt_or_gt_of_ne hb with hb0 | hb0
        · -- a < b < 0: the longer zero run comes first
          rw [expandEntry_of_neg a ha0, expandEntry_of_neg b hb0] at hlen ⊢
          have hk : (-b).toNat + 1 ≤ (-a).toNat := by omega
          obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
          rw [hj, replicate_split]
          cases r' with
          | nil =>
            simp only [List.length_append, List.length_replicate] at hlen
            simp [decodeVector] at hlen
            omega
          | cons c r'' =>
            have hc := hm'.head_pos hb0
            rw [decodeVector_cons, expandEntry_of_pos c hc]
            have hcpos : 0 < c.toNat := by omega
            obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_lt hcpos
            rw [hi, zero_add, List.replicate_succ]
            simp only [List.append_assoc, List.cons_append]
            exact split_lt _ _ _
        · -- a < 0 < b
          rw [expandEntry_of_neg a ha0, expandEntry_of_pos b hb0]
          have hapos : 0 < (-a).toNat := by omega
          have hbpos : 0 < b.toNat := by omega
          obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hapos
          obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_lt hbpos
          rw [hj, hi, zero_add, zero_add, List.replicate_succ, List.replicate_succ]
          exact split_lt [] _ _
      · -- 0 < a < b
        have hb0 : 0 < b := by omega
        rw [expandEntry_of_pos a ha0, expandEntry_of_pos b hb0]
        have hk : a.toNat + 1 ≤ b.toNat := by omega
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
        rw [hj, replicate_split]
        simp only [List.append_assoc, List.cons_append]
        exact split_lt _ _ _
    · simp only [List.length_append, Nat.add_left_cancel_iff] at hlen
      exact List.append_left_lt (decodeVector_lt_of_lt r r' hm.tail hm'.tail hlen hr)

/-- sec:sorting, transfer: on well-formed vectors of equal decoded length, the vectors and
    their bit strings are sorted alike. -/
theorem decodeVector_lt_iff (m m' : List ℤ) (hm : MarkedWF m) (hm' : MarkedWF m')
    (hlen : (decodeVector m).length = (decodeVector m').length) :
    m < m' ↔ decodeVector m < decodeVector m' := by
  constructor
  · exact decodeVector_lt_of_lt m m' hm hm' hlen
  · intro h
    by_contra hn
    rcases lt_or_eq_of_le (not_lt.mp hn) with hlt | heq
    · exact lt_asymm h (decodeVector_lt_of_lt m' m hm' hm hlen.symm hlt)
    · rw [heq] at h
      exact lt_irrefl _ h

/-- markedVector is well-formed; from an odd value its first entry is positive. -/
theorem markedWF_markedVector (x0 : ℕ) (hx0 : x0 > 1) :
    ∀ fuel x, x0 ≤ x →
      MarkedWF (markedVector fuel x0 x) ∧
        (x % 2 = 1 → ∀ e ∈ (markedVector fuel x0 x).head?, 0 < e) := by
  intro fuel
  induction fuel with
  | zero =>
    intro x _
    simp [markedVector, MarkedWF]
  | succ fuel ih =>
    intro x hxge
    by_cases hxodd : x % 2 = 1
    · have hv1 : 1 ≤ trailingOnes x := by
        have hxOdd : Odd x := Nat.odd_iff.mpr hxodd
        obtain ⟨j, hj⟩ := hxOdd
        exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
      rw [markedVector_succ_odd fuel x0 x hxodd]
      by_cases hR : R x < x0
      · simp only [hR, ↓reduceIte, markedEntry_true]
        refine ⟨⟨?_, List.IsChain.singleton _⟩, ?_⟩
        · intro e he
          simp only [List.mem_singleton] at he
          omega
        · intro _ e he
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
          omega
      · simp only [hR, ↓reduceIte, markedEntry_true]
        obtain ⟨hwf, _⟩ := ih (R x) (by omega)
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | hmem
          · omega
          · exact hwf.1 e hmem
        · rw [List.isChain_cons]
          refine ⟨?_, hwf.2⟩
          intro _ _
          left
          omega
        · intro _ e he
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
          omega
    · have hxeven : Even x := Nat.even_iff.mpr (by omega)
      have hxne : x ≠ 0 := by omega
      rw [markedVector_succ_even fuel x0 x hxodd,
        evenStep_spec x0 (by omega) x hxge hxeven]
      by_cases hE : x / 2 ^ trailingZeros x < x0
      · simp only [hE, ↓reduceIte, markedEntry_false]
        have hmc1 : minCorrection x0 x ≥ 1 := by
          rw [minCorrection_eq]
          grind
        refine ⟨⟨?_, List.IsChain.singleton _⟩, ?_⟩
        · intro e he
          simp only [List.mem_singleton] at he
          omega
        · intro h
          omega
      · simp only [hE, ↓reduceIte, markedEntry_false]
        have hv1 : trailingZeros x ≥ 1 := by
          obtain ⟨r, hr⟩ := hxeven
          exact one_le_padicValNat_of_dvd hxne ⟨r, by omega⟩
        have hodd : (x / 2 ^ trailingZeros x) % 2 = 1 :=
          Nat.odd_iff.mp (odd_div_pow_trailingZeros x hxne)
        obtain ⟨hwf, hhead⟩ := ih (x / 2 ^ trailingZeros x) (by omega)
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | hmem
          · omega
          · exact hwf.1 e hmem
        · rw [List.isChain_cons]
          refine ⟨?_, hwf.2⟩
          intro y hy
          right
          exact hhead hodd y hy
        · intro h
          omega

/-- sec:sorting for class ids of Order p3 (rho < d_23 x): bit strings and marked vectors are
    sorted alike. -/
theorem tBits_lt_iff_markedVector_lt (p3 x y : ℕ) (hx : IsClassId p3 x) (hy : IsClassId p3 y)
    (hxd : rho (tBits x (p2_of p3)) < d_23 (tBits x (p2_of p3)) * x)
    (hyd : rho (tBits y (p2_of p3)) < d_23 (tBits y (p2_of p3)) * y) :
    tBits x (p2_of p3) < tBits y (p2_of p3) ↔
      markedVector (p2_of p3) x x < markedVector (p2_of p3) y y := by
  have hx1 : x > 1 := one_lt_of_class _ x (classCond_of_isClassId p3 x hx hxd)
  have hy1 : y > 1 := one_lt_of_class _ y (classCond_of_isClassId p3 y hy hyd)
  have hdx := decodeVector_classId p3 x hx hxd
  have hdy := decodeVector_classId p3 y hy hyd
  rw [decodeVector_lt_iff _ _ (markedWF_markedVector x hx1 _ x le_rfl).1
    (markedWF_markedVector y hy1 _ y le_rfl).1 (by rw [hdx, hdy, length_tBits, length_tBits]),
    hdx, hdy]

/-- sec:sorting for class ids of Order p3 (rho < d_23 x): encodings and marked vectors are sorted
    alike. -/
theorem encode_lt_iff_markedVector_lt (p3 x y : ℕ) (hx : IsClassId p3 x) (hy : IsClassId p3 y)
    (hxd : rho (tBits x (p2_of p3)) < d_23 (tBits x (p2_of p3)) * x)
    (hyd : rho (tBits y (p2_of p3)) < d_23 (tBits y (p2_of p3)) * y) :
    encode (tBits x (p2_of p3)) < encode (tBits y (p2_of p3)) ↔
      markedVector (p2_of p3) x x < markedVector (p2_of p3) y y := by
  rw [← tBits_lt_iff_markedVector_lt p3 x y hx hy hxd hyd,
    encode_lt_iff_lex _ _ (by rw [length_tBits, length_tBits])]
  exact exists_split_iff_lt _ _ (by rw [length_tBits, length_tBits])

end AcceleratedCollatz
