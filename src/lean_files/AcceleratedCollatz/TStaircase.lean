-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TDrop
import AcceleratedCollatz.TRhoMax

/-!
  A word as a staircase. The o-th odd step of a word of Order n, at position k, is the
  point 2^k 3^(n-o) of rho. The step bound of `admissible_step_le` says that every such
  point after the first stands below 3^(n-1); together with the length p2(n) it is also
  enough: a word is admissible exactly when every odd step that follows m odd steps
  stands at a position k with k + 1 ≤ p2(m), and its length is p2 of its Order
  (`admissible_iff_steps`).
-/

namespace AcceleratedCollatz

/-- The Order of a prefix grows by one exactly at an odd step. -/
theorem order_take_succ (s : List Bool) (m : ℕ) :
    order (s.take (m + 1)) = order (s.take m) + order s[m]?.toList := by
  rw [List.take_add_one, order_append]

/-- Under the step bound and length p2 of the Order, every position m < length lies below
    p2 of the Order of the prefix before it. -/
theorem lt_p2_of_steps (s : List Bool)
    (hstep : ∀ k, s[k]? = some true → k + 1 ≤ p2_of (order (s.take k)))
    (hlen : s.length = p2_of (order s)) :
    ∀ d m, m + d + 1 = s.length → m < p2_of (order (s.take m)) := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hlt : m < s.length := by omega
    cases hb : s[m] with
    | true =>
      have h := hstep m (by rw [List.getElem?_eq_getElem hlt, hb])
      omega
    | false =>
      have h1 := order_take_succ s m
      rw [List.getElem?_eq_getElem hlt, hb] at h1
      have h0 : order [false] = 0 := by
        simp [order]
      simp only [Option.toList_some, h0, Nat.add_zero] at h1
      have hm1 : m + 1 = s.length := by omega
      rw [hm1, List.take_length] at h1
      rw [← h1, ← hlen]
      omega
  | succ d ih =>
    intro m hm
    have hlt : m < s.length := by omega
    cases hb : s[m] with
    | true =>
      have h := hstep m (by rw [List.getElem?_eq_getElem hlt, hb])
      omega
    | false =>
      have h1 := order_take_succ s m
      rw [List.getElem?_eq_getElem hlt, hb] at h1
      have h0 : order [false] = 0 := by
        simp [order]
      simp only [Option.toList_some, h0, Nat.add_zero] at h1
      have h2 := ih (m + 1) (by omega)
      rw [h1] at h2
      omega

/-- A word with the step bound and length p2 of its Order is admissible. -/
theorem admissible_of_steps (s : List Bool)
    (hstep : ∀ k, s[k]? = some true → k + 1 ≤ p2_of (order (s.take k)))
    (hlen : s.length = p2_of (order s)) : Admissible s := by
  constructor
  · intro m hm1 hmlt
    rw [one_lt_seqProduct_iff, List.length_take, min_eq_left hmlt.le]
    have hp := lt_p2_of_steps s hstep hlen (s.length - m - 1) m (by omega)
    have hlog : m ≤ Nat.log 2 (3 ^ order (s.take m)) := by
      unfold p2_of at hp
      omega
    have hle : 2 ^ m ≤ 3 ^ order (s.take m) :=
      Nat.pow_le_of_le_log (by positivity) hlog
    have hodd : 3 ^ order (s.take m) % 2 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have heven : 2 ^ m % 2 = 0 := by
      obtain ⟨e, he⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
      rw [he, pow_succ]
      simp
    omega
  · rw [seqProduct_lt_one_iff, hlen]
    exact p2_of_spec (order s)

/-- A word is admissible exactly when every odd step that follows m odd steps stands at a
    position k with k + 1 ≤ p2(m), and its length is p2 of its Order. -/
theorem admissible_iff_steps (s : List Bool) :
    Admissible s ↔ (∀ k, s[k]? = some true → k + 1 ≤ p2_of (order (s.take k))) ∧
      s.length = p2_of (order s) :=
  ⟨fun hA => ⟨admissible_step_le hA, admissible_length s hA⟩,
    fun h => admissible_of_steps s h.1 h.2⟩

end AcceleratedCollatz
