-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Zeta.TMassShareQ
import AcceleratedCollatz.TBlockRecordQ
import AcceleratedCollatz.TFirstWordQ

/-!
  The zeros of the mass identity for odd q ≥ 3 (C110.1). With L = p2Q q n, every word of length L
  with n ones is a rotation of a drop word, that is L N_q(n) = C(L, n), exactly at the upper record
  Orders (`p2Q_mul_card_eq_choose_iff`): by `choose_p2Q_eq_split` the difference is a sum over the
  split Orders of positive terms (every Order has a drop word, `firstWordQ`), and m < n is a split
  Order iff its floor q^m/2^p2Q(m) lies below that of n (`mem_splitOrdersQ_iff`; never equal, as q
  is odd). For q = 3 this is the corollary of Winkler 2026 in the drop zeta draft (Theorem 5.5) and
  the zeros of OEIS A400061.
-/

namespace AcceleratedCollatz

variable {q : ℕ}

theorem admSetQ_card_pos (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) : 0 < (admSetQ q n).card :=
  Finset.card_pos.2 ⟨firstWordQ q n,
    (mem_admSetQ (by omega) n _).2 ⟨firstWordQ_admissibleQ hodd hq n, order_firstWordQ q n⟩⟩

/-- No split Order iff every earlier Order has a lower floor. -/
theorem splitOrdersQ_eq_empty_iff (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    splitOrdersQ q n = ∅ ↔ ∀ m, 1 ≤ m → m < n → blockFactorQ q m < blockFactorQ q n := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h m hm1 hmn
    have hns := h m
    rw [mem_splitOrdersQ_iff hq hm1 hmn, not_lt] at hns
    rw [blockFactorQ_lt_iff]
    rcases hns.lt_or_eq with hlt | heq
    · rw [mul_comm (q ^ m), mul_comm (q ^ n)]; exact hlt
    · exact absurd (by rw [mul_comm (q ^ m), mul_comm (q ^ n)]; exact heq)
        (q_pow_mul_two_pow_ne hodd hq hmn (p2Q q n) (p2Q q m))
  · intro h m hm
    have hm' := Finset.mem_Ico.1 (Finset.mem_filter.1 hm).1
    have hb := h m hm'.1 hm'.2
    rw [blockFactorQ_lt_iff] at hb
    rw [mem_splitOrdersQ_iff hq hm'.1 hm'.2] at hm
    rw [mul_comm (q ^ m), mul_comm (q ^ n)] at hb
    exact absurd hm (not_lt.2 hb.le)

/-- C110.1: p2Q q n · N_q(n) = C(p2Q q n, n) iff n is an upper record Order (odd q ≥ 3). -/
theorem p2Q_mul_card_eq_choose_iff (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    p2Q q n * (admSetQ q n).card = (p2Q q n).choose n ↔ UpperRecordQ q n := by
  rw [upperRecordQ_iff_blockFactorQ hodd hq, ← splitOrdersQ_eq_empty_iff hodd hq,
    choose_p2Q_eq_split hodd hq n, left_eq_add, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro m hm
    have h0 := h m hm
    have hm' := Finset.mem_Ico.1 (Finset.mem_filter.1 hm).1
    have hc : 0 < (p2Q q (n - m)).choose (n - m) := Nat.choose_pos (lt_p2Q hq _).le
    have := Nat.mul_pos (admSetQ_card_pos hodd hq m) hc
    omega
  · intro h m hm
    rw [h] at hm
    exact absurd hm (Finset.notMem_empty m)

end AcceleratedCollatz
