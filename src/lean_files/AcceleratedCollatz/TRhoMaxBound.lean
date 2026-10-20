-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhoMax
import AcceleratedCollatz.TWidthBound

/-!
  The finite reduction of ClassDrops with the largest rho of an Order in place of the
  bound n 3^(n-1). `rhoMax n`, a sum of 3-smooth numbers, bounds rho over the admissible
  words of Order n, so only class ids c with d c ≤ rhoMax n can fail to drop
  (`classDrops_iff_small_rhoMax`); per Order, the ids up to
  `widthBoundMax n` = ⌊rhoMax n / d(n)⌋ suffice (`classDropsAt_of_widthMax`,
  `classDropsAt_of_verifiedMax`), a bound at most `widthBound n`
  (`widthBoundMax_le_widthBound`).
-/

namespace AcceleratedCollatz

/-- ⌊rhoMax n / (2^p2(n) - 3^n)⌋. -/
def widthBoundMax (n : ℕ) : ℕ := rhoMax n / (2 ^ p2_of n - 3 ^ n)

/-- rhoMax n ≤ n 3^(n-1). -/
theorem rhoMax_le (n : ℕ) : rhoMax n ≤ n * 3 ^ (n - 1) := by
  have h := rho_le_of_admissible (firstWord n) (firstWord_admissible n)
  rw [rho_firstWord, order_firstWord] at h
  exact h

/-- widthBoundMax n ≤ widthBound n. -/
theorem widthBoundMax_le_widthBound (n : ℕ) : widthBoundMax n ≤ widthBound n :=
  Nat.div_le_div_right (rhoMax_le n)

/-- ClassDrops only needs checking at the class ids c with d c ≤ rhoMax(Order). -/
theorem classDrops_iff_small_rhoMax :
    ClassDrops ↔ ∀ s, Admissible s → 1 < classId s →
      d_23 s * classId s ≤ rhoMax (order s) → rho s < d_23 s * classId s := by
  constructor
  · intro h s hA hc _
    exact h s hA hc
  · intro h s hA hc
    by_cases hsmall : d_23 s * classId s ≤ rhoMax (order s)
    · exact h s hA hc hsmall
    · exact lt_of_le_of_lt (rho_le_rhoMax hA) (Nat.lt_of_not_le hsmall)

/-- ClassDrops at Order n from the drop of every x with 1 < x ≤ widthBoundMax n at its
    coefficient stopping time. -/
theorem classDropsAt_of_widthMax (n : ℕ)
    (h : ∀ x, 1 < x → x ≤ widthBoundMax n → ∀ m, Admissible (tBits x m) →
      order (tBits x m) = n → tStep^[m] x < x) :
    ClassDropsAt n := by
  intro s hA hn hc
  by_cases hsmall : d_23 s * classId s ≤ rhoMax n
  · have hlen : s.length = p2_of n := by rw [admissible_length s hA, hn]
    have hd : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
    have hdpos : 0 < d_23 s := by
      simp only [d_23]
      omega
    have hdn : d_23 s = 2 ^ p2_of n - 3 ^ n := by simp only [d_23, hlen, hn]
    have hle : classId s ≤ widthBoundMax n := by
      unfold widthBoundMax
      rw [← hdn, Nat.le_div_iff_mul_le hdpos, mul_comm]
      exact hsmall
    have hbits := tBits_classId s
    have hA' : Admissible (tBits (classId s) s.length) := by
      rw [hbits]
      exact hA
    have hdrop := h (classId s) hc hle s.length hA' (by rw [hbits, hn])
    exact (drop_iff_rho s (classId s) hA hbits).mp hdrop
  · have hlt : rhoMax (order s) < d_23 s * classId s := by
      rw [hn]
      exact Nat.lt_of_not_le hsmall
    exact lt_of_le_of_lt (rho_le_rhoMax hA) hlt

/-- A verified range: if every x with 1 < x ≤ X drops at its coefficient stopping
    time, ClassDrops holds at every Order n with widthBoundMax n ≤ X. -/
theorem classDropsAt_of_verifiedMax (X : ℕ)
    (hX : ∀ x, 1 < x → x ≤ X → ∀ m, Admissible (tBits x m) → tStep^[m] x < x)
    (n : ℕ) (hn : widthBoundMax n ≤ X) : ClassDropsAt n :=
  classDropsAt_of_widthMax n fun x hx hxb m hA _ => hX x hx (hxb.trans hn) m hA

set_option linter.hashCommand false in
#guard [17, 41].map widthBoundMax = [108, 867]

end AcceleratedCollatz
