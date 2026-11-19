-- SPDX-License-Identifier: MIT
import BestOfOrder.Bridge

/-!
  The start parts (paper, Lemma 3.4). A key is a word of some Order without its final 0's
  (`IsKey`, `keyPV`, `core` of `AcceleratedCollatz`): [] or a persistent word followed by a one.
  The prefix of an admissible word that ends in one of its ones is a key (`isKey_of_prefix`),
  so it is a word of its own Order without its final 0's (`admissible_keyPV'`, `core_keyPV'`).
  Conversely every nonempty key of Order w < n is such a prefix of an admissible word of Order n
  (`exists_of_key`): append n - w - 1 ones (`persistent_append_true`), then one more and 0's.
-/

namespace BestOfOrder

open AcceleratedCollatz

theorem order_replicate_true (i : ℕ) : order (List.replicate i true) = i := by
  simp [order]

/-- A persistent word stays persistent after a one. -/
theorem persistent_append_true {q : List Bool} (hq : Persistent q) : Persistent (q ++ [true]) := by
  intro m h1 hm
  rw [List.length_append, List.length_singleton] at hm
  rcases Nat.lt_or_ge q.length m with hgt | hle
  · have hm' : m = q.length + 1 := by omega
    rw [hm', show q.length + 1 = (q ++ [true]).length by simp, List.take_length,
      one_lt_seqProduct_iff, order_append, List.length_append, List.length_singleton]
    have hord1 : order [true] = 1 := by simp [order]
    rw [hord1, pow_succ, pow_succ]
    have hq' : 2 ^ q.length ≤ 3 ^ order q := by
      rcases Nat.eq_zero_or_pos q.length with h0 | hpos
      · rw [h0]; exact Nat.one_le_pow _ _ (by norm_num)
      · have h := hq q.length hpos le_rfl
        rw [List.take_length, one_lt_seqProduct_iff] at h
        exact h.le
    have hb : 0 < 3 ^ order q := by positivity
    omega
  · rw [List.take_append_of_le_length hle]
    exact hq m h1 hle

theorem persistent_append_replicate {q : List Bool} (hq : Persistent q) (i : ℕ) :
    Persistent (q ++ List.replicate i true) := by
  induction i with
  | zero => simpa using hq
  | succ i ih =>
    rw [List.replicate_succ', ← List.append_assoc]
    exact persistent_append_true ih

/-- Lemma 3.4, one way: a prefix of an admissible word ending in a one is a key. -/
theorem isKey_of_prefix {s p r : List Bool} (hA : Admissible s) (hs : s = p ++ true :: r) :
    IsKey (p ++ [true]) := by
  refine Or.inr ⟨p, ?_, rfl⟩
  intro m h1 hm
  have hlt : m < s.length := by rw [hs]; simp; omega
  have h := hA.prefix_gt m h1 hlt
  rwa [hs, List.take_append_of_le_length hm] at h

/-- The word of a key is admissible. -/
theorem admissible_keyPV' {k : List Bool} (hk : IsKey k) : Admissible (keyPV k) :=
  admissible_keyPV hk

/-- The word of a key has the key's Order. -/
theorem order_keyPV' (k : List Bool) : order (keyPV k) = order k := order_keyPV k

/-- The word of a key, without its final 0's, is the key. -/
theorem core_keyPV' {k : List Bool} (hk : IsKey k) : core (keyPV k) = k := core_keyPV hk

/-- Lemma 3.4, the other way: a nonempty key of Order w < n starts an admissible word of
    Order n. -/
theorem exists_of_key {p : List Bool} (hp : Persistent p) {n : ℕ}
    (hn : order (p ++ [true]) < n) :
    ∃ s, Admissible s ∧ order s = n ∧ (p ++ [true]) <+: s := by
  set k := p ++ [true] with hk
  set q := k ++ List.replicate (n - order k - 1) true with hq
  have hpq : Persistent q := persistent_append_replicate (persistent_append_true hp) _
  obtain ⟨hA, hord⟩ := admissible_complete q hpq
  have hoq : order q = n - 1 := by
    rw [hq, order_append, order_replicate_true]
    omega
  refine ⟨complete (order q) q, hA, by omega, ?_⟩
  exact ⟨List.replicate (n - order k - 1) true ++ true ::
      List.replicate (p2_of (order q + 1) - q.length - 1) false, by
    simp [complete, hq, List.append_assoc]⟩

end BestOfOrder
