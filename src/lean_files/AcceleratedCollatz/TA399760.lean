-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TDropPeriod
import AcceleratedCollatz.TCorrespondence
import Mathlib.Data.List.DropRight

/-!
  More of OEIS A399760, a(n) = the odd part of the parity vector of x = 4n - 1 until the drop
  (the word `tBits x L`, L the drop step, without its final 0's: `oddWord`, read in binary).

  * Unconditional: with n = 2^v m, m odd (A001511(n) = v + 1), the word starts with v + 2
    1's and then a 0 (`take_tBits_four_mul_sub_one`): after j <= v + 2 tripling steps,
    T^j(x) + 1 = 3^j 2^(v+2-j) m, so no drop comes before step v + 3.
  * When x drops at an admissible word (Terras's conjecture, as in `TDropPeriod`):
    L = A020914(A000120(a(n))) (`a399760_length`, A020914 = `p2_of`), so a(n) determines
    the word (`eq_of_oddWord_eq`).
  * First occurrences (A243115): when 4n - 1 drops at L, no smaller m >= 1 has the same
    word iff 4n - 1 < 2^L, assuming the smaller 4m - 1 drop at admissible words
    (`a399760_first_iff`); with the same assumption for the words themselves, the same
    for the terms a(m) (`a399760_first_oddWord_iff`). The direction from 4n - 1 < 2^L needs
    no assumption at the word level.
-/

namespace AcceleratedCollatz

/-- The odd part of a word: the word without its final 0's. -/
def oddWord (w : List Bool) : List Bool := w.rdropWhile (!·)

theorem oddWord_append (w : List Bool) :
    w = oddWord w ++ List.replicate (w.rtakeWhile (!·)).length false := by
  conv_lhs => rw [← List.rdropWhile_append_rtakeWhile (p := (!·)) (l := w)]
  congr 1
  refine List.eq_replicate_iff.mpr ⟨rfl, fun b hb => ?_⟩
  simpa using List.mem_rtakeWhile_imp hb

theorem order_oddWord (w : List Bool) : order (oddWord w) = order w := by
  conv_rhs => rw [oddWord_append w]
  rw [order_append, order_replicate_false, Nat.add_zero]

/-- Two admissible words with the same odd part are equal. -/
theorem eq_of_oddWord_eq {w w' : List Bool} (hA : Admissible w) (hA' : Admissible w')
    (h : oddWord w = oddWord w') : w = w' := by
  have hl : w.length = w'.length := by
    rw [admissible_length _ hA, admissible_length _ hA', ← order_oddWord w, ← order_oddWord w', h]
  rw [oddWord_append w, oddWord_append w'] at hl ⊢
  simp only [List.length_append, List.length_replicate, h] at hl ⊢
  rw [Nat.add_left_cancel hl]

/-- T^j(y) + 1 = 3^j d while y + 1 = 2^j d: j tripling steps. -/
theorem tStep_iterate_add_one_of_eq :
    ∀ (j y d : ℕ), y + 1 = 2 ^ j * d →
      tStep^[j] y + 1 = 3 ^ j * d ∧ tBits y j = List.replicate j true
  | 0, y, d, h => by simpa [tBits] using h
  | j + 1, y, d, h => by
    have hy : y % 2 = 1 := by
      have : y + 1 = 2 * (2 ^ j * d) := by rw [h, pow_succ]; ring
      omega
    have hs : tStep y + 1 = 2 ^ j * (3 * d) := by
      rw [tStep_odd y hy]
      have : 2 * ((3 * y + 1) / 2 + 1) = 2 * (2 ^ j * (3 * d)) := by
        have h2 : 2 * ((3 * y + 1) / 2) = 3 * y + 1 := by omega
        rw [Nat.mul_add, h2]
        have : 3 * y + 1 + 2 = 3 * (y + 1) := by ring
        rw [this, h, pow_succ]
        ring
      omega
    obtain ⟨ih1, ih2⟩ := tStep_iterate_add_one_of_eq j (tStep y) (3 * d) hs
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply, ih1, pow_succ]
      ring
    · simp only [tBits, List.replicate_succ, hy, decide_true, ih2]

/-- A399760: with n = 2^v m, m odd, the word of 4n - 1 until its drop at L starts with
v + 2 = A001511(n) + 1 ones and then a 0 (so L >= v + 3). -/
theorem take_tBits_four_mul_sub_one {n v m L : ℕ} (hn : n = 2 ^ v * m) (hm : m % 2 = 1)
    (hD : IsTDrop (4 * n - 1) L) :
    v + 3 ≤ L ∧ (tBits (4 * n - 1) L).take (v + 3) = List.replicate (v + 2) true ++ [false] := by
  set x := 4 * n - 1 with hx
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by rw [hn]; positivity
  have hx1 : x + 1 = 2 ^ (v + 2) * m := by
    have h4 : 2 ^ (v + 2) * m = 4 * (2 ^ v * m) := by ring
    have : 0 < 2 ^ v * m := by positivity
    omega
  -- the first j <= v + 2 steps: T^j(x) + 1 = 3^j 2^(v+2-j) m >= x + 1
  have hge : ∀ j, j ≤ v + 2 → x ≤ tStep^[j] x := by
    intro j hj
    have hsplit : x + 1 = 2 ^ j * (2 ^ (v + 2 - j) * m) := by
      rw [hx1, ← Nat.mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]
    have h1 := (tStep_iterate_add_one_of_eq j x _ hsplit).1
    have h2 : 2 ^ j * (2 ^ (v + 2 - j) * m) ≤ 3 ^ j * (2 ^ (v + 2 - j) * m) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) j)
    omega
  have hL : v + 3 ≤ L := by
    have hx1' : x ≠ 1 := by omega
    simp only [IsTDrop, hx1', ↓reduceIte, IsFirstDrop] at hD
    obtain ⟨_, hlt, _⟩ := hD
    by_contra hcon
    have := hge L (by omega)
    simp only [tTraj, Function.iterate_zero, id] at hlt
    omega
  refine ⟨hL, ?_⟩
  obtain ⟨h1, h2⟩ := tStep_iterate_add_one_of_eq (v + 2) x m hx1
  rw [tBits_take x L (v + 3) hL, tBits_add x (v + 2) 1, h2]
  have hev : tStep^[v + 2] x % 2 ≠ 1 := by
    have : (3 ^ (v + 2) * m) % 2 = 1 := by
      rw [Nat.mul_mod, Nat.pow_mod]
      norm_num [hm]
    omega
  simp only [tBits, hev, decide_false]

/-- A399760: the drop step of 4n - 1 is A020914 of the count of its 1's, when the word is
admissible. -/
theorem a399760_length {n L : ℕ} (hA : Admissible (tBits (4 * n - 1) L)) :
    L = p2_of (order (oddWord (tBits (4 * n - 1) L))) := by
  rw [order_oddWord, ← admissible_length _ hA, length_tBits]

/-- A start has at most one admissible word among its parity prefixes. -/
theorem eq_of_admissible_tBits {y L L' : ℕ} (hA : Admissible (tBits y L))
    (hA' : Admissible (tBits y L')) : L = L' := by
  have key : ∀ {K K' : ℕ}, Admissible (tBits y K) → Admissible (tBits y K') → K ≤ K' →
      K = K' := by
    intro K K' hA hA' hK
    by_contra hne
    have hlt : K < K' := lt_of_le_of_ne hK hne
    have hK0 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · rw [h0] at hA
        exact absurd hA.lt_one (by simp [tBits, seqProduct])
      · exact h0
    have hp := hA'.prefix_gt K hK0 (by rw [length_tBits]; exact hlt)
    rw [tBits_take y K' K hK] at hp
    exact absurd hA.lt_one (not_lt.mpr hp.le)
  rcases le_total L L' with h | h
  · exact key hA hA' h
  · exact (key hA' hA h).symm

/-- The drop of 4m - 1 at an admissible word (Terras's conjecture for 4m - 1). -/
def DropsAdmissible (m : ℕ) : Prop :=
  ∃ L, IsTDrop (4 * m - 1) L ∧ Admissible (tBits (4 * m - 1) L)

/-- A399760, first occurrences (A243115): when 4n - 1 drops at L, no m with 1 <= m < n has
the same word iff 4n - 1 < 2^L; the smaller 4m - 1 drop at admissible words. -/
theorem a399760_first_iff {n L : ℕ} (hn : 1 ≤ n) (hD : IsTDrop (4 * n - 1) L)
    (hA : Admissible (tBits (4 * n - 1) L)) (hH : ∀ m, 1 ≤ m → m < n → DropsAdmissible m) :
    (∀ m L', 1 ≤ m → m < n → IsTDrop (4 * m - 1) L' →
        tBits (4 * m - 1) L' ≠ tBits (4 * n - 1) L) ↔ 4 * n - 1 < 2 ^ L := by
  constructor
  · intro hfirst
    by_contra hge
    rw [not_lt] at hge
    have hL2 : 2 ≤ L := by
      rcases L with _ | _ | L
      · exact absurd hA.lt_one (by simp [tBits, seqProduct])
      · have hodd : (4 * n - 1) % 2 = 1 := by omega
        exact absurd hA.lt_one (by norm_num [tBits, hodd, seqProduct, factor])
      · omega
    have h4 : 2 ^ L = 4 * 2 ^ (L - 2) := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    set m := n - 2 ^ (L - 2) with hm
    have hm1 : 1 ≤ m := by omega
    have hmn : m < n := by
      have : 0 < 2 ^ (L - 2) := by positivity
      omega
    have hxm : 4 * n - 1 = 4 * m - 1 + 2 ^ L * 1 := by omega
    obtain ⟨L', hD', hA'⟩ := hH m hm1 hmn
    have hb : tBits (4 * m - 1) L = tBits (4 * n - 1) L := by
      refine tBits_congr _ _ _ ?_
      rw [hxm]
      exact (Nat.add_mul_mod_self_left _ _ _).symm
    have hLL : L = L' := eq_of_admissible_tBits (hb ▸ hA) hA'
    subst hLL
    exact hfirst m L hm1 hmn hD' hb
  · intro hlt m L' hm1 hmn hD' heq
    have hlen : L' = L := by
      have := congrArg List.length heq
      simpa using this
    subst hlen
    have hmod := modEq_of_tBits_eq _ _ _ heq
    have hlt' : 4 * m - 1 < 2 ^ L' := by omega
    have := Nat.ModEq.eq_of_lt_of_lt hmod hlt' hlt
    omega

/-- The drop step is unique. -/
theorem isTDrop_unique {x L L' : ℕ} (h : IsTDrop x L) (h' : IsTDrop x L') : L = L' := by
  unfold IsTDrop at h h'
  split_ifs at h h'
  · rw [h, h']
  · exact isFirstDrop_unique h h'

/-- A399760, first occurrences of the terms (A243115): when 4n - 1 drops at L, no m with
1 <= m < n has a(m) = a(n) iff 4n - 1 < 2^L; the smaller 4m - 1 drop at admissible
words. -/
theorem a399760_first_oddWord_iff {n L : ℕ} (hn : 1 ≤ n) (hD : IsTDrop (4 * n - 1) L)
    (hA : Admissible (tBits (4 * n - 1) L)) (hH : ∀ m, 1 ≤ m → m < n → DropsAdmissible m) :
    (∀ m L', 1 ≤ m → m < n → IsTDrop (4 * m - 1) L' →
        oddWord (tBits (4 * m - 1) L') ≠ oddWord (tBits (4 * n - 1) L)) ↔
      4 * n - 1 < 2 ^ L := by
  rw [← a399760_first_iff hn hD hA hH]
  refine forall_congr' fun m => forall_congr' fun L' => forall_congr' fun hm1 =>
    forall_congr' fun hmn => forall_congr' fun hD' => not_congr ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain ⟨L'', hD'', hA''⟩ := hH m hm1 hmn
  rw [← isTDrop_unique hD'' hD'] at h ⊢
  exact eq_of_oddWord_eq hA'' hA h

end AcceleratedCollatz
