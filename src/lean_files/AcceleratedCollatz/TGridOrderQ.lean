-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TSweepPermQ

/-!
  Record Orders as the Orders with a linear grid, for odd q ≥ 3. The points (o, j)
  with o ≤ n and j ≤ P are sorted by the levels q^o / 2^j; the grid is linear for
  (n, P) when the linear levels o P - j n sort all pairs of points the same way,
  except the pair of origin and corner (`GridLinearQ`). With P = p2Q(n) this holds
  exactly at the upper record Orders (`gridLinearQ_iff_upperRecordQ`); with
  P = p2Q(n) - 1 exactly at the lower record Orders (`gridLinearQ_iff_lowerRecordQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

theorem p2Q_mono (hq : 3 ≤ q) {i n : ℕ} (h : i ≤ n) : p2Q q i ≤ p2Q q n := by
  unfold p2Q
  have hp : q ^ i ≤ q ^ n := Nat.pow_le_pow_right (by omega) h
  have hl := Nat.log_mono_right (b := 2) hp
  omega

theorem two_pow_pred_p2Q_lt (hodd : Odd q) (hq : 3 ≤ q) {a : ℕ} (ha : 1 ≤ a) :
    2 ^ (p2Q q a - 1) < q ^ a := by
  rw [two_pow_lt_q_pow_iff hodd hq ha]
  have := one_le_p2Q q a
  omega

/-- The linear levels o P - j n sort the points of the (n, P) grid like q^o / 2^j,
    except the pair of origin and corner. -/
def GridLinearQ (q n P : ℕ) : Prop :=
  ∀ o o' j j' : ℕ, o ≤ n → o' ≤ n → j ≤ P → j' ≤ P →
    ¬(o = 0 ∧ j = 0 ∧ o' = n ∧ j' = P) → ¬(o = n ∧ j = P ∧ o' = 0 ∧ j' = 0) →
    (q ^ o * 2 ^ j' < q ^ o' * 2 ^ j ↔ o * P + j' * n < o' * P + j * n)

/-- Upper record Order: p2Q(n)/n is below p2Q(a)/a for every 1 ≤ a < n.
    Orders 0 and 1 qualify: there is no such a. -/
def UpperRecordQ (q n : ℕ) : Prop :=
  ∀ a, 1 ≤ a → a < n → a * p2Q q n < n * p2Q q a

/-- Lower record Order: (p2Q(n) - 1)/n is above (p2Q(a) - 1)/a for every 1 ≤ a < n.
    Orders 0 and 1 qualify: there is no such a. -/
def LowerRecordQ (q n : ℕ) : Prop :=
  ∀ a, 1 ≤ a → a < n → n * (p2Q q a - 1) < a * (p2Q q n - 1)

/-- Both comparisons of a pair with o ≤ o' reduce to the difference a = o' - o. -/
theorem grid_cancel_leQ (hq : 3 ≤ q) (o a j j' n P : ℕ) :
    (q ^ o * 2 ^ j' < q ^ (o + a) * 2 ^ j ↔ 2 ^ j' < q ^ a * 2 ^ j) ∧
      (o * P + j' * n < (o + a) * P + j * n ↔ j' * n < a * P + j * n) := by
  refine ⟨?_, ?_⟩
  · rw [pow_add, mul_assoc, Nat.mul_lt_mul_left (pow_pos (by omega) _)]
  · rw [add_mul]
    omega

/-- Both comparisons of a pair with o' ≤ o reduce to the difference a = o - o'. -/
theorem grid_cancel_geQ (hq : 3 ≤ q) (o' a j j' n P : ℕ) :
    (q ^ (o' + a) * 2 ^ j' < q ^ o' * 2 ^ j ↔ q ^ a * 2 ^ j' < 2 ^ j) ∧
      ((o' + a) * P + j' * n < o' * P + j * n ↔ a * P + j' * n < j * n) := by
  refine ⟨?_, ?_⟩
  · rw [pow_add, mul_assoc, Nat.mul_lt_mul_left (pow_pos (by omega) _)]
  · rw [add_mul]
    omega

/-- Pairs in the same column compare by j alone. -/
theorem grid_same_columnQ (q : ℕ) {j j' n : ℕ} (hn : 1 ≤ n) (P : ℕ) :
    (2 ^ j' < q ^ 0 * 2 ^ j ↔ j' * n < 0 * P + j * n) := by
  rw [pow_zero, one_mul, zero_mul, zero_add, Nat.pow_lt_pow_iff_right (by norm_num),
    Nat.mul_lt_mul_right (by omega)]

/-- The grid of slope p2Q(n)/n is linear exactly at the upper record Orders. -/
theorem gridLinearQ_iff_upperRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    GridLinearQ q n (p2Q q n) ↔ UpperRecordQ q n := by
  constructor
  · intro hG a ha1 han
    have hle : p2Q q a ≤ p2Q q n := p2Q_mono hq (by omega)
    have h := hG a 0 (p2Q q a) 0 (by omega) (by omega) hle (by omega)
      (by omega) (by omega)
    have htrue : q ^ a * 2 ^ 0 < q ^ 0 * 2 ^ p2Q q a := by
      simpa using p2Q_spec hq a
    have hlin := h.mp htrue
    nlinarith
  · intro hR o o' j j' ho ho' hj hj' hx1 hx2
    rcases le_or_gt o o' with hoo | hoo
    · obtain ⟨a, rfl⟩ : ∃ a, o' = o + a := ⟨o' - o, by omega⟩
      rw [(grid_cancel_leQ hq o a j j' n (p2Q q n)).1, (grid_cancel_leQ hq o a j j' n (p2Q q n)).2]
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · rw [ha0]
        exact grid_same_columnQ q hn _
      · rw [lt_q_pow_mul_iff hodd hq (by omega)]
        have hm := p2Q_sub_one_mul_lt hq (a := a) (b := n) (by omega)
        have hp := one_le_p2Q q a
        constructor
        · intro h
          have h1 : j' * n ≤ (j + (p2Q q a - 1)) * n := Nat.mul_le_mul_right n (by omega)
          nlinarith
        · intro h
          by_contra hc
          push Not at hc
          have h1 : (j + p2Q q a) * n ≤ j' * n := Nat.mul_le_mul_right n hc
          rcases Nat.lt_or_ge a n with han | han
          · have := hR a (by omega) han
            nlinarith
          · have hn' : p2Q q a = p2Q q n := by
              congr 1
              omega
            exact hx1 ⟨by omega, by omega, by omega, by omega⟩
    · obtain ⟨a, rfl⟩ : ∃ a, o = o' + a := ⟨o - o', by omega⟩
      rw [(grid_cancel_geQ hq o' a j j' n (p2Q q n)).1,
        (grid_cancel_geQ hq o' a j j' n (p2Q q n)).2,
        q_pow_mul_lt_iff hq]
      have hm := p2Q_sub_one_mul_lt hq (a := a) (b := n) (by omega)
      have hp := one_le_p2Q q a
      constructor
      · intro h
        have h1 : (j' + p2Q q a) * n ≤ j * n := Nat.mul_le_mul_right n h
        rcases Nat.lt_or_ge a n with han | han
        · have := hR a (by omega) han
          nlinarith
        · have hn' : p2Q q a = p2Q q n := by
            congr 1
            omega
          exact absurd ⟨by omega, by omega, by omega, by omega⟩ hx2
      · intro h
        by_contra hc
        push Not at hc
        have h1 : j * n ≤ (j' + (p2Q q a - 1)) * n := Nat.mul_le_mul_right n (by omega)
        nlinarith

/-- The grid of slope (p2Q(n) - 1)/n is linear exactly at the lower record Orders. -/
theorem gridLinearQ_iff_lowerRecordQ (hodd : Odd q) (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    GridLinearQ q n (p2Q q n - 1) ↔ LowerRecordQ q n := by
  constructor
  · intro hG a ha1 han
    have hle : p2Q q a - 1 ≤ p2Q q n - 1 := Nat.sub_le_sub_right (p2Q_mono hq (by omega)) 1
    have h := hG 0 a 0 (p2Q q a - 1) (by omega) (by omega) (by omega) hle
      (by omega) (by omega)
    have htrue : q ^ 0 * 2 ^ (p2Q q a - 1) < q ^ a * 2 ^ 0 := by
      simpa using two_pow_pred_p2Q_lt hodd hq ha1
    have hlin := h.mp htrue
    nlinarith
  · intro hR o o' j j' ho ho' hj hj' hx1 hx2
    have hpn := one_le_p2Q q n
    rcases le_or_gt o o' with hoo | hoo
    · obtain ⟨a, rfl⟩ : ∃ a, o' = o + a := ⟨o' - o, by omega⟩
      rw [(grid_cancel_leQ hq o a j j' n (p2Q q n - 1)).1,
        (grid_cancel_leQ hq o a j j' n (p2Q q n - 1)).2]
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · rw [ha0]
        exact grid_same_columnQ q hn _
      · rw [lt_q_pow_mul_iff hodd hq (by omega)]
        have hm := p2Q_sub_one_mul_lt hq (a := n) (b := a) hn
        have hp := one_le_p2Q q a
        constructor
        · intro h
          have h1 : j' * n ≤ (j + (p2Q q a - 1)) * n := Nat.mul_le_mul_right n (by omega)
          rcases Nat.lt_or_ge a n with han | han
          · have := hR a (by omega) han
            nlinarith
          · have hn' : p2Q q a = p2Q q n := by
              congr 1
              omega
            have hj'P : j' < j + (p2Q q n - 1) ∨ j' = j + (p2Q q n - 1) := by omega
            rcases hj'P with hlt | heq
            · have h2 : j' * n < (j + (p2Q q n - 1)) * n :=
                Nat.mul_lt_mul_of_pos_right hlt (by omega)
              have ha : a = n := by omega
              rw [ha]
              nlinarith
            · exact absurd ⟨by omega, by omega, by omega, by omega⟩ hx1
        · intro h
          by_contra hc
          push Not at hc
          have h1 : (j + p2Q q a) * n ≤ j' * n := Nat.mul_le_mul_right n hc
          nlinarith
    · obtain ⟨a, rfl⟩ : ∃ a, o = o' + a := ⟨o - o', by omega⟩
      rw [(grid_cancel_geQ hq o' a j j' n (p2Q q n - 1)).1,
        (grid_cancel_geQ hq o' a j j' n (p2Q q n - 1)).2, q_pow_mul_lt_iff hq]
      have hm := p2Q_sub_one_mul_lt hq (a := n) (b := a) hn
      have hp := one_le_p2Q q a
      constructor
      · intro h
        have h1 : (j' + p2Q q a) * n ≤ j * n := Nat.mul_le_mul_right n h
        nlinarith
      · intro h
        by_contra hc
        push Not at hc
        have h1 : j * n ≤ (j' + (p2Q q a - 1)) * n := Nat.mul_le_mul_right n (by omega)
        rcases Nat.lt_or_ge a n with han | han
        · have := hR a (by omega) han
          nlinarith
        · have ha : a = n := by omega
          subst ha
          nlinarith

end AcceleratedCollatz
