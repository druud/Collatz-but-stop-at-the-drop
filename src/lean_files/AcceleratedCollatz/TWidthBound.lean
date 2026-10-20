-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TRhoBound

/-!
  Per-Order finite reduction of ClassDrops. `widthBound n` = ⌊n 3^(n-1) / d(n)⌋
  with d(n) = 2^p2(n) - 3^n. ClassDrops at Order n follows from the drop, at the
  coefficient stopping time, of every x with 1 < x ≤ widthBound n
  (`classDropsAt_of_width`); a verified range x ≤ X covers every Order n with
  widthBound n ≤ X (`classDropsAt_of_verified`).
-/

namespace AcceleratedCollatz

/-- ⌊n 3^(n-1) / (2^p2(n) - 3^n)⌋. -/
def widthBound (n : ℕ) : ℕ := n * 3 ^ (n - 1) / (2 ^ p2_of n - 3 ^ n)

/-- ClassDrops restricted to words of Order n. -/
def ClassDropsAt (n : ℕ) : Prop :=
  ∀ s, Admissible s → order s = n → 1 < classId s → rho s < d_23 s * classId s

theorem classDrops_iff_forall_at : ClassDrops ↔ ∀ n, ClassDropsAt n :=
  ⟨fun h _ s hA _ hc => h s hA hc, fun h s hA hc => h (order s) s hA rfl hc⟩

/-- ClassDrops at Order n from the drop of every x with 1 < x ≤ widthBound n at its
    coefficient stopping time. -/
theorem classDropsAt_of_width (n : ℕ)
    (h : ∀ x, 1 < x → x ≤ widthBound n → ∀ m, Admissible (tBits x m) →
      order (tBits x m) = n → tStep^[m] x < x) :
    ClassDropsAt n := by
  intro s hA hn hc
  by_cases hsmall : d_23 s * classId s ≤ order s * 3 ^ (order s - 1)
  · have hlen : s.length = p2_of n := by rw [admissible_length s hA, hn]
    have hd : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
    have hdpos : 0 < d_23 s := by
      simp only [d_23]
      omega
    have hdn : d_23 s = 2 ^ p2_of n - 3 ^ n := by simp only [d_23, hlen, hn]
    have hle : classId s ≤ widthBound n := by
      unfold widthBound
      rw [← hdn, Nat.le_div_iff_mul_le hdpos, mul_comm, ← hn]
      exact hsmall
    have hbits := tBits_classId s
    have hA' : Admissible (tBits (classId s) s.length) := by
      rw [hbits]
      exact hA
    have hdrop := h (classId s) hc hle s.length hA' (by rw [hbits, hn])
    exact (drop_iff_rho s (classId s) hA hbits).mp hdrop
  · exact lt_of_le_of_lt (rho_le_of_admissible s hA) (Nat.lt_of_not_le hsmall)

/-- A verified range: if every x with 1 < x ≤ X drops at its coefficient stopping
    time, ClassDrops holds at every Order n with widthBound n ≤ X. -/
theorem classDropsAt_of_verified (X : ℕ)
    (hX : ∀ x, 1 < x → x ≤ X → ∀ m, Admissible (tBits x m) → tStep^[m] x < x)
    (n : ℕ) (hn : widthBound n ≤ X) : ClassDropsAt n :=
  classDropsAt_of_width n fun x hx hxb m hA _ => hX x hx (hxb.trans hn) m hA

set_option linter.hashCommand false in
#guard [17, 41, 306].map widthBound = [144, 1185, 99729]

end AcceleratedCollatz
