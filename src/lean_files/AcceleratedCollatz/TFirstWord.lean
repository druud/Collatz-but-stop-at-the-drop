-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecord
import AcceleratedCollatz.TFirstWordQ
import AcceleratedCollatz.TRank
import AcceleratedCollatz.TRecordLow

/-!
  The first word of each Order (paper sec:chain): the q = 3 case of TFirstWordQ
  (`firstBodyQ_three`, `firstWordQ_three`). `firstWord n` takes, after each odd
  step, every halving that keeps the level above 1; it is admissible of Order n
  (`firstWord_mem`) and the least admissible word of Order n (`firstWord_le`), so it is
  `unrank n 0` (`unrank_zero`). After a of its odd steps and the halvings that follow
  them it is p2(a) - 1 letters long (`take_firstWord`) and its level is twice the block
  factor of a (`seqProduct_firstBody`); every other level before the end is at least 2
  (`two_le_seqProduct_firstBody_append`). So its record lows, the cuts of its chain, are
  its end and the points after p2(a) - 1 letters for the lower record Orders a ≤ n
  (`isRecordLow_firstWord`). In its chain 1 A_1 ... A_k t the Orders of 1 A_1 ... A_i,
  i < k, are the lower record Orders below n, t = [0] exactly when n is one, and
  every block A_i is the first word of its Order (`firstWord_chain`,
  `firstBody_eq_append_firstWord`, `firstWord_eq_append_firstWord`).
-/

namespace AcceleratedCollatz

/-- The first word of Order n without its final halving: after each odd step every
    halving that keeps the level above 1. -/
def firstBody : ℕ → List Bool
  | 0 => []
  | n + 1 => firstBody n ++ true :: List.replicate (p2_of (n + 1) - p2_of n - 1) false

/-- The first word of Order n. -/
def firstWord (n : ℕ) : List Bool := firstBody n ++ [false]

theorem firstBody_succ (n : ℕ) : firstBody (n + 1) =
    firstBody n ++ true :: List.replicate (p2_of (n + 1) - p2_of n - 1) false :=
  rfl

/-- For q = 3 the first word of the q-family without its final halving is `firstBody`. -/
theorem firstBodyQ_three : firstBodyQ 3 = firstBody := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firstBodyQ_succ, firstBody_succ, ih, p2Q_three]

/-- For q = 3 the first word of the q-family is `firstWord`. -/
theorem firstWordQ_three : firstWordQ 3 = firstWord := by
  funext n
  rw [firstWordQ, firstWord, firstBodyQ_three]

/-- The first odd step of the first word is followed by no halving that keeps the level
    above 1. -/
theorem firstBody_one : firstBody 1 = [true] := by
  have h : firstBody 1 =
      firstBody 0 ++ true :: List.replicate (p2_of 1 - p2_of 0 - 1) false := rfl
  rw [h, p2_of_one, p2_of_zero]
  rfl

/-- `firstBody n` has p2(n) - 1 letters. -/
theorem length_firstBody (n : ℕ) : (firstBody n).length + 1 = p2_of n := by
  rw [← firstBodyQ_three]
  exact length_firstBodyQ le_rfl n

theorem length_firstWord (n : ℕ) : (firstWord n).length = p2_of n := by
  rw [← firstWordQ_three]
  exact length_firstWordQ le_rfl n

theorem order_firstBody (n : ℕ) : order (firstBody n) = n := by
  rw [← firstBodyQ_three]
  exact order_firstBodyQ 3 n

theorem order_firstWord (n : ℕ) : order (firstWord n) = n := by
  rw [← firstWordQ_three]
  exact order_firstWordQ 3 n

/-- After a of its odd steps and the halvings that follow them, the first word of
    Order n ≥ a is p2(a) - 1 letters long. -/
theorem take_firstWord {n a m : ℕ} (ha : a ≤ n) (hm : m + 1 = p2_of a) :
    (firstWord n).take m = firstBody a := by
  rw [← firstWordQ_three, ← firstBodyQ_three]
  exact take_firstWordQ le_rfl ha hm

/-- The first word of Order k without its final halving, then an odd step and r halvings,
    has level at least 2 when p2(k) + r + 1 < p2(k + 1). -/
theorem two_le_seqProduct_firstBody_append {k r : ℕ}
    (hr : p2_of k + r + 1 < p2_of (k + 1)) :
    2 ≤ seqProduct (firstBody k ++ true :: List.replicate r false) := by
  rw [← seqProductQ_three, ← firstBodyQ_three]
  exact two_le_seqProductQ_firstBodyQ_append le_rfl hr

theorem blockFactor_lt_one (n : ℕ) : blockFactor n < 1 :=
  blockFactorQ_lt_one le_rfl n

/-- After n odd steps and the halvings that follow them the level is twice the block
    factor of n. -/
theorem seqProduct_firstBody (n : ℕ) : seqProduct (firstBody n) = 2 * blockFactor n := by
  rw [← seqProductQ_three, ← firstBodyQ_three]
  exact seqProductQ_firstBodyQ le_rfl n

theorem seqProduct_firstWord (n : ℕ) : seqProduct (firstWord n) = blockFactor n := by
  rw [← seqProductQ_three, ← firstWordQ_three]
  exact seqProductQ_firstWordQ le_rfl n

/-- The first word of Order n is admissible. -/
theorem firstWord_admissible (n : ℕ) : Admissible (firstWord n) := by
  rw [← admissibleQ_three, ← firstWordQ_three]
  exact firstWordQ_admissibleQ (by decide) le_rfl n

/-- The first word of Order n is an admissible word of Order n. -/
theorem firstWord_mem (n : ℕ) : firstWord n ∈ admSet n :=
  (mem_admSet _ _).mpr ⟨firstWord_admissible n, order_firstWord n⟩

/-- The first word of Order n is the least admissible word of Order n. -/
theorem firstWord_le {n : ℕ} {s : List Bool} (hs : s ∈ admSet n) : firstWord n ≤ s := by
  rw [← admSetQ_three] at hs
  rw [← firstWordQ_three]
  exact firstWordQ_le le_rfl hs

/-- The first word of Order n is the word of rank 0. -/
theorem unrank_zero (n : ℕ) : unrank n 0 = firstWord n := by
  have hpos : 0 < (admSet n).card := Finset.card_pos.mpr ⟨_, firstWord_mem n⟩
  have hcard := card_lt_unrank hpos
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard
  exact le_antisymm (not_lt.mp (hcard (firstWord_mem n))) (firstWord_le (unrank_mem hpos))

/-- The record lows of the first word of Order n: its end, and the points after
    p2(a) - 1 letters for the lower record Orders a ≤ n. -/
theorem isRecordLow_firstWord (n m : ℕ) :
    IsRecordLow (firstWord n) m ↔
      m = p2_of n ∨ ∃ a, 1 ≤ a ∧ a ≤ n ∧ LowerRecord a ∧ m + 1 = p2_of a := by
  have h21 : p2Q 3 1 = 2 := p2_of_one
  have hQ : 1 ≤ m → m < p2_of n →
      ((∀ j, 1 ≤ j → j < m →
          seqProduct ((firstWord n).take m) < seqProduct ((firstWord n).take j)) ↔
        ∃ a, 1 ≤ a ∧ a ≤ n ∧ LowerRecord a ∧ m + 1 = p2_of a) := by
    intro hm1 hm
    have h := firstWordQ_low_iff (q := 3) le_rfl (n := n) (m := m) (by omega) hm
    rw [seqProductQ_three, firstWordQ_three, h21] at h
    constructor
    · intro hl
      exact h.mp (fun j hj1 hjm => hl j (by omega) hjm)
    · intro hex j hj1 hjm
      exact h.mpr hex j (by omega) hjm
  constructor
  · rintro ⟨hm1, hm, hlow⟩
    rw [length_firstWord] at hm
    rcases Nat.eq_or_lt_of_le hm with heq | hlt
    · exact Or.inl heq
    · exact Or.inr ((hQ hm1 hlt).mp hlow)
  · rintro (heq | ⟨a, ha1, han, hR, hma⟩)
    · have hA := firstWord_admissible n
      have h1 : 1 ≤ m := by
        rw [heq]
        exact one_le_p2Q 3 n
      have h2 : m ≤ (firstWord n).length := by
        rw [heq, length_firstWord]
      refine ⟨h1, h2, ?_⟩
      intro j hj1 hjm
      have hjl : j < (firstWord n).length := by
        rw [length_firstWord]
        omega
      have hgt := hA.prefix_gt j hj1 hjl
      have hlt := hA.lt_one
      rw [heq, ← length_firstWord n, List.take_length]
      linarith
    · have hpa : 2 ≤ p2_of a := two_le_p2Q le_rfl ha1
      have hpan : p2_of a ≤ p2_of n := p2_of_mono han
      have hmn : m < p2_of n := by omega
      have hm1 : 1 ≤ m := by omega
      refine ⟨hm1, ?_, (hQ hm1 hmn).mpr ⟨a, ha1, han, hR, hma⟩⟩
      rw [length_firstWord]
      omega

/-- Between two neighbouring lower record Orders a < b the first word reads the first
    word of Order b - a. -/
theorem firstBody_eq_append_firstWord {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hRa : LowerRecord a) (hRb : LowerRecord b)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecord x) :
    firstBody b = firstBody a ++ firstWord (b - a) := by
  rw [← firstBodyQ_three, ← firstWordQ_three]
  exact firstBodyQ_eq_append_firstWordQ le_rfl ha hab hRa hRb hnone

/-- After a lower record Order a with no lower record Order from a + 1 to n, the first
    word of Order n reads the first word of Order n - a. -/
theorem firstWord_eq_append_firstWord {a n : ℕ} (han : a < n) (hRa : LowerRecord a)
    (hnone : ∀ x, a < x → x ≤ n → ¬LowerRecord x) :
    firstWord n = firstBody a ++ firstWord (n - a) := by
  rw [← firstBodyQ_three, ← firstWordQ_three]
  exact firstWordQ_eq_append_firstWordQ le_rfl han hRa hnone

/-- The chain of the first word of Order n ≥ 1: every block is the first word of its
    Order; before each block the Order of the part read so far is a lower record Order
    below n, and every such Order occurs there; the tail is [0] exactly when n is a lower
    record Order. -/
theorem firstWord_chain {n : ℕ} (hn : 1 ≤ n) :
    ∃ (bs : List (List Bool)) (t : List Bool),
      firstWord n = true :: (bs.flatten ++ t) ∧ (∀ b ∈ bs, IsChainBlock b) ∧
      (∀ b ∈ bs, b = firstWord (order b)) ∧
      1 + (bs.map order).sum = n ∧
      (∀ a, (∃ i, i < bs.length ∧ a = 1 + ((bs.take i).map order).sum) ↔
        (1 ≤ a ∧ a < n ∧ LowerRecord a)) ∧
      (t = [false] ↔ LowerRecord n) ∧ (t = [] ∨ t = [false]) := by
  obtain ⟨bs, t, hs, hbs, htail, ht⟩ := firstWordQ_blocks (q := 3) le_rfl hn
  rw [firstWordQ_three, firstBodyQ_three, firstBody_one, List.singleton_append] at hs
  have hfirst : ∀ b ∈ bs, b = firstWord (order b) := by
    intro b hb
    have h := (hbs.first b hb).2
    rw [firstWordQ_three] at h
    exact h
  have hblock : ∀ b ∈ bs, IsChainBlock b := by
    intro b hb
    refine ⟨?_, (hbs.first b hb).1⟩
    rw [hfirst b hb]
    exact firstWord_admissible (order b)
  exact ⟨bs, t, hs, hblock, hfirst, hbs.sum, hbs.cuts, htail, ht⟩

end AcceleratedCollatz
