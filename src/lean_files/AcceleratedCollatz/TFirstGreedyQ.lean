-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TFirstChainQ

/-!
  The first word of Order n as a greedy sum, in the q-family (q ≥ 3). Take the largest
  lower record Order a1 ≤ n, then the largest lower record Order a2 ≤ n - a1, and so on
  until nothing is left (`IsGreedyLowQ`; it exists and is unique: `exists_isGreedyLowQ`,
  `IsGreedyLowQ.unique`; its parts do not increase: `IsGreedyLowQ.le_head`). The first
  word of Order n is the first parts of the first words of a1, a2, ..., in turn, then a
  halving (`firstWordQ_eq_greedy`). So the last block of a first word, the first word of
  n - a1, is again such a greedy sum, down to a lower record Order.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- A greedy sum of lower record Orders for n: each part the largest lower record Order up
    to what is left of n. -/
def IsGreedyLowQ (q : ℕ) : ℕ → List ℕ → Prop
  | n, [] => n = 0
  | n, a :: as => 1 ≤ a ∧ a ≤ n ∧ LowerRecordQ q a ∧
      (∀ x, a < x → x ≤ n → ¬LowerRecordQ q x) ∧ IsGreedyLowQ q (n - a) as

/-- Every n has a greedy sum of lower record Orders. -/
theorem exists_isGreedyLowQ (q n : ℕ) : ∃ as, IsGreedyLowQ q n as := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact ⟨[], h0⟩
    · by_cases hR : LowerRecordQ q n
      · obtain ⟨as, has⟩ := ih 0 h0
        refine ⟨n :: as, h0, le_rfl, hR, ?_, ?_⟩
        · intro x hx1 hx2
          omega
        · rw [Nat.sub_self]
          exact has
      · have h2 : 2 ≤ n := by
          by_contra hc
          have h1 : n = 1 := by
            omega
          rw [h1] at hR
          exact hR (lowerRecordQ_one q)
        obtain ⟨a, ha1, han, hRa, hnone⟩ := exists_last_lowerRecordQ q h2
        obtain ⟨as, has⟩ := ih (n - a) (by omega)
        refine ⟨a :: as, ha1, han.le, hRa, ?_, has⟩
        intro x hax hxn
        rcases Nat.lt_or_ge x n with h | h
        · exact hnone x hax h
        · have hx : x = n := by
            omega
          rw [hx]
          exact hR

/-- The greedy sum of n is unique. -/
theorem IsGreedyLowQ.unique : ∀ {n : ℕ} {as bs : List ℕ},
    IsGreedyLowQ q n as → IsGreedyLowQ q n bs → as = bs
  | _, [], [], _, _ => rfl
  | n, [], b :: bs, ha, hb => by
    obtain ⟨hb1, hbn, _, _, _⟩ := hb
    have h : n = 0 := ha
    omega
  | n, a :: as, [], ha, hb => by
    obtain ⟨ha1, han, _, _, _⟩ := ha
    have h : n = 0 := hb
    omega
  | n, a :: as, b :: bs, ha, hb => by
    obtain ⟨ha1, han, hRa, hnonea, hra⟩ := ha
    obtain ⟨hb1, hbn, hRb, hnoneb, hrb⟩ := hb
    have hab : a = b := by
      rcases Nat.lt_trichotomy a b with h | h | h
      · exact absurd hRb (hnonea b h hbn)
      · exact h
      · exact absurd hRa (hnoneb a h han)
    subst hab
    rw [IsGreedyLowQ.unique hra hrb]

/-- The parts of a greedy sum do not increase. -/
theorem IsGreedyLowQ.le_head {n a b : ℕ} {as : List ℕ}
    (h : IsGreedyLowQ q n (a :: b :: as)) : b ≤ a := by
  obtain ⟨_, han, _, hnone, _, hbn, hRb, _, _⟩ := h
  by_contra hc
  exact hnone b (by omega) (by omega) hRb

/-- The first part of the first word of Order n is the first parts of the first words of
    its greedy sum, in turn. -/
theorem firstBodyQ_eq_greedy (hq : 3 ≤ q) : ∀ (as : List ℕ) (n : ℕ), IsGreedyLowQ q n as →
    firstBodyQ q n = (as.map (firstBodyQ q)).flatten
  | [], n, h => by
    have h0 : n = 0 := h
    rw [h0]
    rfl
  | a :: as, n, ⟨_, han, hRa, hnone, hrest⟩ => by
    have ih := firstBodyQ_eq_greedy hq as (n - a) hrest
    rw [List.map_cons, List.flatten_cons, ← ih]
    rcases Nat.eq_or_lt_of_le han with heq | hlt
    · rw [← heq, Nat.sub_self]
      exact (List.append_nil _).symm
    · have h := firstWordQ_eq_append_firstWordQ hq hlt hRa hnone
      rw [firstWordQ, firstWordQ, ← List.append_assoc] at h
      exact List.append_cancel_right h

/-- The first word of Order n is the first parts of the first words of its greedy sum of
    lower record Orders, in turn, then a halving. -/
theorem firstWordQ_eq_greedy (hq : 3 ≤ q) {n : ℕ} {as : List ℕ} (h : IsGreedyLowQ q n as) :
    firstWordQ q n = (as.map (firstBodyQ q)).flatten ++ [false] := by
  rw [firstWordQ, firstBodyQ_eq_greedy hq as n h]

end AcceleratedCollatz
