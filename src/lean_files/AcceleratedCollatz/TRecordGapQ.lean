-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecordQ

/-!
  Gaps of the record Orders of the q-family (odd q ≥ 3). After a lower record Order a,
  no Order before the next lower record Order has a block factor below that of a
  (`not_blockFactorQ_lt_of_lowerRecordQ`), so p2Q(a + i) + 1 = p2Q(a) + p2Q(i) there
  (`p2Q_add_of_lowerRecordQ`); the same with "above" after an upper record Order
  (`not_blockFactorQ_lt_of_upperRecordQ`, `p2Q_add_of_upperRecordQ`). So the gap between
  two neighbouring lower record Orders is an upper record Order
  (`upperRecordQ_sub_of_lowerRecordQ`), and the gap between two neighbouring upper
  record Orders is a lower record Order (`lowerRecordQ_sub_of_upperRecordQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Between a lower record Order a and the next one, no block factor is below that of
    a. -/
theorem not_blockFactorQ_lt_of_lowerRecordQ (hq : 3 ≤ q) {a b : ℕ} (hRa : LowerRecordQ q a)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecordQ q x) {x : ℕ} (hax : a < x) (hxb : x < b) :
    ¬blockFactorQ q x < blockFactorQ q a := by
  intro hlt
  have hex : ∃ y, a < y ∧ blockFactorQ q y < blockFactorQ q a := ⟨x, hax, hlt⟩
  have hy := Nat.find_spec hex
  have hyle : Nat.find hex ≤ x := Nat.find_min' hex ⟨hax, hlt⟩
  have hRy : LowerRecordQ q (Nat.find hex) := by
    rw [lowerRecordQ_iff_blockFactorQ hq]
    intro z hz1 hzy
    rcases Nat.lt_or_ge a z with haz | hza
    · have hmin := Nat.find_min hex hzy
      rw [not_and] at hmin
      exact lt_of_lt_of_le hy.2 (not_lt.mp (hmin haz))
    · rcases Nat.eq_or_lt_of_le hza with heq | hlt'
      · rw [heq]
        exact hy.2
      · exact lt_trans hy.2 ((lowerRecordQ_iff_blockFactorQ hq a).mp hRa z hz1 hlt')
  exact hnone (Nat.find hex) hy.1 (by omega) hRy

/-- Between an upper record Order a and the next one, no block factor is above that of
    a. -/
theorem not_blockFactorQ_lt_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {a b : ℕ}
    (hRa : UpperRecordQ q a) (hnone : ∀ x, a < x → x < b → ¬UpperRecordQ q x) {x : ℕ}
    (hax : a < x) (hxb : x < b) : ¬blockFactorQ q a < blockFactorQ q x := by
  intro hlt
  have hex : ∃ y, a < y ∧ blockFactorQ q a < blockFactorQ q y := ⟨x, hax, hlt⟩
  have hy := Nat.find_spec hex
  have hyle : Nat.find hex ≤ x := Nat.find_min' hex ⟨hax, hlt⟩
  have hRy : UpperRecordQ q (Nat.find hex) := by
    rw [upperRecordQ_iff_blockFactorQ hodd hq]
    intro z hz1 hzy
    rcases Nat.lt_or_ge a z with haz | hza
    · have hmin := Nat.find_min hex hzy
      rw [not_and] at hmin
      exact lt_of_le_of_lt (not_lt.mp (hmin haz)) hy.2
    · rcases Nat.eq_or_lt_of_le hza with heq | hlt'
      · rw [heq]
        exact hy.2
      · exact lt_trans ((upperRecordQ_iff_blockFactorQ hodd hq a).mp hRa z hz1 hlt') hy.2
  exact hnone (Nat.find hex) hy.1 (by omega) hRy

/-- Between a lower record Order a and the next one, p2Q(a + i) + 1 = p2Q(a) + p2Q(i). -/
theorem p2Q_add_of_lowerRecordQ (hq : 3 ≤ q) {a b : ℕ} (hRa : LowerRecordQ q a)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecordQ q x) {i : ℕ} (hi : 1 ≤ i) (hib : a + i < b) :
    p2Q q (a + i) + 1 = p2Q q a + p2Q q i := by
  have hle := p2Q_add_le hq a i
  have hle2 := p2Q_add_le_succ hq a i
  have hnot := not_blockFactorQ_lt_of_lowerRecordQ hq hRa hnone (x := a + i) (by omega) hib
  rw [blockFactorQ_add_lt_iff hq] at hnot
  omega

/-- Between an upper record Order a and the next one, p2Q(a + i) = p2Q(a) + p2Q(i). -/
theorem p2Q_add_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {a b : ℕ} (hRa : UpperRecordQ q a)
    (hnone : ∀ x, a < x → x < b → ¬UpperRecordQ q x) {i : ℕ} (hi : 1 ≤ i) (hib : a + i < b) :
    p2Q q (a + i) = p2Q q a + p2Q q i := by
  have hle := p2Q_add_le hq a i
  have hle2 := p2Q_add_le_succ hq a i
  have hnot := not_blockFactorQ_lt_of_upperRecordQ hodd hq hRa hnone (x := a + i) (by omega) hib
  rw [blockFactorQ_lt_add_iff hodd hq a hi] at hnot
  omega

/-- Between two neighbouring lower record Orders a < b the gap b - a is an upper record
    Order. -/
theorem upperRecordQ_sub_of_lowerRecordQ (hq : 3 ≤ q) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hRa : LowerRecordQ q a) (hRb : LowerRecordQ q b)
    (hnone : ∀ x, a < x → x < b → ¬LowerRecordQ q x) : UpperRecordQ q (b - a) := by
  rw [upperRecordQ_iff_add hq]
  intro c hc1 hcg
  have hadd := (lowerRecordQ_iff_add hq b).mp hRb
  have h1 := hadd a ha hab
  have h2 := hadd (a + c) (by omega) (by omega)
  rw [Nat.sub_add_eq] at h2
  have h3 := p2Q_add_of_lowerRecordQ hq hRa hnone hc1 (by omega)
  omega

/-- Between two neighbouring upper record Orders a < b the gap b - a is a lower record
    Order. -/
theorem lowerRecordQ_sub_of_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) (hRa : UpperRecordQ q a) (hRb : UpperRecordQ q b)
    (hnone : ∀ x, a < x → x < b → ¬UpperRecordQ q x) : LowerRecordQ q (b - a) := by
  rw [lowerRecordQ_iff_add hq]
  intro c hc1 hcg
  have hadd := (upperRecordQ_iff_add hq b).mp hRb
  have h1 := hadd a ha hab
  have h2 := hadd (a + c) (by omega) (by omega)
  rw [Nat.sub_add_eq] at h2
  have h3 := p2Q_add_of_upperRecordQ hodd hq hRa hnone hc1 (by omega)
  omega

end AcceleratedCollatz
