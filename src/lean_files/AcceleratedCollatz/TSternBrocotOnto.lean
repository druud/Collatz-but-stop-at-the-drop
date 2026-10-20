-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChain
import AcceleratedCollatz.TCorrespondence
import AcceleratedCollatz.TPersistent
import AcceleratedCollatz.TSternBrocotInterval

/-!
  The class of a word onto the interval of its node. Different words have different points
  (`sbPoint_injective`). Every fraction p/n strictly inside the interval of the node of w
  is the point of exactly one word that continues w (`existsUnique_sbPoint_append_eq`): the
  descent compares p/n with the mediant and moves to the left or to the right; the two
  cross-product gaps to the fractions of the node shrink by each other. For the empty word
  the interval is all of 0/1 to 1/0: every positive rational is the point of exactly one
  word (`existsUnique_sbPoint_eq`, `existsUnique_sbPoint_eq_rat`). The class of a word that
  continues w lies in the class of w (`tBits_classId_append`), so the classes below w meet
  the fractions inside its interval one to one (`existsUnique_class_point`). Below a
  persistent word w, a word whose level is below 1 continues an admissible word s that
  continues w (`exists_admissible_between`); its point lies inside the interval of s
  (`sbNode_inside`).
-/

namespace AcceleratedCollatz

/-- Different words have different points. -/
theorem sbPoint_injective : Function.Injective sbPoint := by
  intro s t h
  by_contra hst
  rcases prefix_or_split s t with hp | hp | ⟨u, v, w, rfl, rfl⟩ | ⟨u, v, w, rfl, rfl⟩
  · obtain ⟨r, rfl⟩ := hp
    cases r with
    | nil =>
      exact hst (List.append_nil s).symm
    | cons b r =>
      cases b
      · exact ne_of_gt (sbPoint_append_false_lt s r) h
      · exact ne_of_lt (sbPoint_lt_append_true s r) h
  · obtain ⟨r, rfl⟩ := hp
    cases r with
    | nil =>
      exact hst (List.append_nil t)
    | cons b r =>
      cases b
      · exact ne_of_lt (sbPoint_append_false_lt t r) h
      · exact ne_of_gt (sbPoint_lt_append_true t r) h
  · exact ne_of_lt (sbPoint_split_lt u v w) h
  · exact ne_of_gt (sbPoint_split_lt u w v) h

/-- The point of a word is p/n when the mediant of its node is p/n in cross products. -/
theorem sbPoint_eq_of_cross (w : List Bool) (p n : ℕ) (hn : 0 < n)
    (h : p * ((sbNode w).loDen + (sbNode w).hiDen) =
      n * ((sbNode w).loNum + (sbNode w).hiNum)) :
    sbPoint w = (p : ℚ) / n := by
  have hd : (((sbNode w).loDen + (sbNode w).hiDen : ℕ) : ℚ) ≠ 0 := by
    have h1 := one_le_sbNode_den w
    positivity
  have hn' : (n : ℚ) ≠ 0 := by
    positivity
  rw [sbPoint_eq_sbMed, sbMed, div_eq_div_iff hd hn']
  have hnat : ((sbNode w).loNum + (sbNode w).hiNum) * n =
      p * ((sbNode w).loDen + (sbNode w).hiDen) := by
    rw [h]
    ring
  exact_mod_cast hnat

/-- The descent: p/n strictly inside the interval of w, with the two cross-product gaps
    summing to at most k, is the point of a word that continues w. -/
theorem exists_sbPoint_append_eq (p n : ℕ) (hn : 0 < n) :
    ∀ k : ℕ, ∀ w : List Bool,
      n * (sbNode w).loNum < p * (sbNode w).loDen →
      p * (sbNode w).hiDen < n * (sbNode w).hiNum →
      p * (sbNode w).loDen - n * (sbNode w).loNum +
          (n * (sbNode w).hiNum - p * (sbNode w).hiDen) ≤ k →
      ∃ u, sbPoint (w ++ u) = (p : ℚ) / n := by
  intro k
  induction k with
  | zero =>
    intro w hlo hhi hk
    omega
  | succ k ih =>
    intro w hlo hhi hk
    have hl1 : (sbNode (w ++ [false])).loNum = (sbNode w).loNum := by
      rw [sbNode_append]
      rfl
    have hl2 : (sbNode (w ++ [false])).loDen = (sbNode w).loDen := by
      rw [sbNode_append]
      rfl
    have hl3 : (sbNode (w ++ [false])).hiNum = (sbNode w).loNum + (sbNode w).hiNum := by
      rw [sbNode_append]
      rfl
    have hl4 : (sbNode (w ++ [false])).hiDen = (sbNode w).loDen + (sbNode w).hiDen := by
      rw [sbNode_append]
      rfl
    have hr1 : (sbNode (w ++ [true])).loNum = (sbNode w).loNum + (sbNode w).hiNum := by
      rw [sbNode_append]
      rfl
    have hr2 : (sbNode (w ++ [true])).loDen = (sbNode w).loDen + (sbNode w).hiDen := by
      rw [sbNode_append]
      rfl
    have hr3 : (sbNode (w ++ [true])).hiNum = (sbNode w).hiNum := by
      rw [sbNode_append]
      rfl
    have hr4 : (sbNode (w ++ [true])).hiDen = (sbNode w).hiDen := by
      rw [sbNode_append]
      rfl
    have e1 : p * ((sbNode w).loDen + (sbNode w).hiDen) =
        p * (sbNode w).loDen + p * (sbNode w).hiDen :=
      Nat.mul_add _ _ _
    have e2 : n * ((sbNode w).loNum + (sbNode w).hiNum) =
        n * (sbNode w).loNum + n * (sbNode w).hiNum :=
      Nat.mul_add _ _ _
    rcases lt_trichotomy (p * ((sbNode w).loDen + (sbNode w).hiDen))
        (n * ((sbNode w).loNum + (sbNode w).hiNum)) with h | h | h
    · have hlo' : n * (sbNode (w ++ [false])).loNum < p * (sbNode (w ++ [false])).loDen := by
        rw [hl1, hl2]
        exact hlo
      have hhi' : p * (sbNode (w ++ [false])).hiDen < n * (sbNode (w ++ [false])).hiNum := by
        rw [hl3, hl4]
        exact h
      have hk' : p * (sbNode (w ++ [false])).loDen - n * (sbNode (w ++ [false])).loNum +
          (n * (sbNode (w ++ [false])).hiNum - p * (sbNode (w ++ [false])).hiDen) ≤ k := by
        rw [hl1, hl2, hl3, hl4, e1, e2]
        omega
      obtain ⟨u, hu⟩ := ih (w ++ [false]) hlo' hhi' hk'
      rw [List.append_assoc] at hu
      exact ⟨[false] ++ u, hu⟩
    · refine ⟨[], ?_⟩
      rw [List.append_nil]
      exact sbPoint_eq_of_cross w p n hn h
    · have hlo' : n * (sbNode (w ++ [true])).loNum < p * (sbNode (w ++ [true])).loDen := by
        rw [hr1, hr2]
        exact h
      have hhi' : p * (sbNode (w ++ [true])).hiDen < n * (sbNode (w ++ [true])).hiNum := by
        rw [hr3, hr4]
        exact hhi
      have hk' : p * (sbNode (w ++ [true])).loDen - n * (sbNode (w ++ [true])).loNum +
          (n * (sbNode (w ++ [true])).hiNum - p * (sbNode (w ++ [true])).hiDen) ≤ k := by
        rw [hr1, hr2, hr3, hr4, e1, e2]
        omega
      obtain ⟨u, hu⟩ := ih (w ++ [true]) hlo' hhi' hk'
      rw [List.append_assoc] at hu
      exact ⟨[true] ++ u, hu⟩

/-- Every fraction p/n strictly inside the interval of the node of w (cross products) is
    the point of exactly one word that continues w. -/
theorem existsUnique_sbPoint_append_eq (w : List Bool) (p n : ℕ) (hn : 0 < n)
    (hlo : n * (sbNode w).loNum < p * (sbNode w).loDen)
    (hhi : p * (sbNode w).hiDen < n * (sbNode w).hiNum) :
    ∃! u, sbPoint (w ++ u) = (p : ℚ) / n := by
  obtain ⟨u, hu⟩ := exists_sbPoint_append_eq p n hn _ w hlo hhi le_rfl
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact List.append_cancel_left (sbPoint_injective (hv.trans hu.symm))

/-- Every positive fraction p/n is the point of exactly one word. -/
theorem existsUnique_sbPoint_eq (p n : ℕ) (hp : 0 < p) (hn : 0 < n) :
    ∃! s, sbPoint s = (p : ℚ) / n := by
  have hlo : n * (sbNode []).loNum < p * (sbNode []).loDen := by
    change n * 0 < p * 1
    omega
  have hhi : p * (sbNode []).hiDen < n * (sbNode []).hiNum := by
    change p * 0 < n * 1
    omega
  obtain ⟨u, hu, huniq⟩ := existsUnique_sbPoint_append_eq [] p n hn hlo hhi
  exact ⟨u, hu, huniq⟩

/-- Every positive rational is the point of exactly one word. -/
theorem existsUnique_sbPoint_eq_rat (r : ℚ) (hr : 0 < r) : ∃! s, sbPoint s = r := by
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hp : 0 < r.num.toNat := by
    omega
  have h1 : ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have h2 : ((r.num.toNat : ℕ) : ℚ) / ((r.den : ℕ) : ℚ) = r := by
    rw [h1]
    exact Rat.num_div_den r
  have h := existsUnique_sbPoint_eq r.num.toNat r.den hp r.den_pos
  rw [h2] at h
  exact h

/-- The class of a word that continues w lies in the class of w: its class id has the
    parity bits of w. -/
theorem tBits_classId_append (w u : List Bool) :
    tBits (classId (w ++ u)) w.length = w := by
  have h := tBits_take (classId (w ++ u)) (w ++ u).length w.length (by simp)
  rw [tBits_classId] at h
  rw [← h]
  exact List.take_left' rfl

/-- The classes below w meet the fractions inside the interval of w one to one: p/n is the
    point of exactly one word that continues w, and the class of that word lies in the
    class of w. -/
theorem existsUnique_class_point (w : List Bool) (p n : ℕ) (hn : 0 < n)
    (hlo : n * (sbNode w).loNum < p * (sbNode w).loDen)
    (hhi : p * (sbNode w).hiDen < n * (sbNode w).hiNum) :
    ∃! u, sbPoint (w ++ u) = (p : ℚ) / n ∧ tBits (classId (w ++ u)) w.length = w := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_sbPoint_append_eq w p n hn hlo hhi
  refine ⟨u, ⟨hu, tBits_classId_append w u⟩, ?_⟩
  intro v hv
  exact huniq v hv.1

/-- A word whose level is below 1 has an admissible prefix of length at least 1. -/
theorem exists_admissible_take (v : List Bool) (hv : seqProduct v < 1) :
    ∃ m, 1 ≤ m ∧ m ≤ v.length ∧ Admissible (v.take m) := by
  have hne : v ≠ [] := by
    rintro rfl
    have h1 : seqProduct [] = 1 := rfl
    rw [h1] at hv
    exact lt_irrefl 1 hv
  have hlen : 1 ≤ v.length := List.length_pos_of_ne_nil hne
  have hvt : seqProduct (v.take v.length) < 1 := by
    rw [List.take_length]
    exact hv
  have hex : ∃ m, 1 ≤ m ∧ seqProduct (v.take m) < 1 := ⟨v.length, hlen, hvt⟩
  obtain ⟨hm1, hmlt⟩ := Nat.find_spec hex
  have hmle : Nat.find hex ≤ v.length := Nat.find_min' hex ⟨hlen, hvt⟩
  refine ⟨Nat.find hex, hm1, hmle, ⟨?_, hmlt⟩⟩
  intro j hj1 hjm
  rw [List.length_take] at hjm
  have hjm' : j < Nat.find hex := by
    omega
  have hmin : j ≤ Nat.find hex := hjm'.le
  rw [List.take_take, Nat.min_eq_left hmin]
  have hjne : v.take j ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [List.length_take]
    omega
  have hnot := Nat.find_min hex hjm'
  have hge : 1 ≤ seqProduct (v.take j) := by
    by_contra hlt
    exact hnot ⟨hj1, lt_of_not_ge hlt⟩
  exact lt_of_le_of_ne hge (Ne.symm (seqProduct_ne_one (v.take j) hjne))

/-- Below a persistent word w, a word whose level is below 1 continues an admissible word
    s that continues w. -/
theorem exists_admissible_between (w u : List Bool) (hw : Persistent w)
    (hv : seqProduct (w ++ u) < 1) :
    ∃ s t, Admissible s ∧ w <+: s ∧ w.length < s.length ∧ w ++ u = s ++ t := by
  obtain ⟨m, hm1, hmle, hA⟩ := exists_admissible_take (w ++ u) hv
  have hslen : ((w ++ u).take m).length = m := by
    rw [List.length_take]
    omega
  have hwm : w.length < m := by
    by_contra hle
    have hle' : m ≤ w.length := by
      omega
    have htake : (w ++ u).take m = w.take m := List.take_append_of_le_length hle'
    have hgt := hw m hm1 hle'
    rw [← htake] at hgt
    exact absurd hA.lt_one (not_lt.mpr hgt.le)
  have hpre : w <+: (w ++ u).take m := by
    have hw' : ((w ++ u).take m).take w.length = w := by
      rw [List.take_take, Nat.min_eq_left hwm.le]
      exact List.take_left' rfl
    have hp := List.take_prefix w.length ((w ++ u).take m)
    rw [hw'] at hp
    exact hp
  refine ⟨(w ++ u).take m, (w ++ u).drop m, hA, hpre, ?_, (List.take_append_drop m (w ++ u)).symm⟩
  rw [hslen]
  exact hwm

end AcceleratedCollatz
