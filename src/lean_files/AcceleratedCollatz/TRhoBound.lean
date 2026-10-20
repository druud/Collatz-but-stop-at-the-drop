-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TWidth

/-!
  A bound on rho. Each odd step at position k contributes 3^(n - o) 2^k to rho s
  (o = odd steps up to and including k), and before an odd step at k ≥ 1 the level of an
  admissible word is above 1, so 2^k < 3^(o - 1). Hence rho s ≤ n 3^(n-1) for admissible s
  of Order n (`rho_le_of_admissible`). So every x with n 3^(n-1) < d_23 s * x drops at the
  end of its word s (`drop_of_large`), and ClassDrops only needs checking for class ids
  with d_23 * classId ≤ n 3^(n-1) (`classDrops_iff_small`).
-/

namespace AcceleratedCollatz

/-- affineNum over a concatenation. -/
theorem affineNum_append (a b : List Bool) (j N : ℕ) :
    affineNum (a ++ b) j N = affineNum b (j + a.length) (affineNum a j N) := by
  induction a generalizing j N with
  | nil =>
    simp [affineNum]
  | cons c a ih =>
    simp only [List.cons_append, affineNum, List.length_cons]
    rw [ih]
    congr 1
    omega

/-- rho after one more odd step. -/
theorem rho_append_true (s : List Bool) : rho (s ++ [true]) = 3 * rho s + 2 ^ s.length := by
  unfold rho
  rw [affineNum_append]
  simp [affineNum]

/-- rho after one more halving. -/
theorem rho_append_false (s : List Bool) : rho (s ++ [false]) = rho s := by
  unfold rho
  rw [affineNum_append]
  simp [affineNum]

/-- Order after one more letter. -/
theorem order_append_single (s : List Bool) (b : Bool) :
    order (s ++ [b]) = order s + (if b then 1 else 0) := by
  cases b with
  | false =>
    simp [order]
  | true =>
    simp [order]

/-- 3 (o 3^(o-1)) = o 3^o. -/
theorem three_mul_mul_pow_pred (o : ℕ) : 3 * (o * 3 ^ (o - 1)) = o * 3 ^ o := by
  cases o with
  | zero =>
    simp
  | succ o =>
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

/-- rho ≤ n 3^(n-1) when every odd step at position k has 2^k ≤ 3^(odd steps before k). -/
theorem rho_le_of_steps (s : List Bool)
    (H : ∀ k, s[k]? = some true → 2 ^ k ≤ 3 ^ order (s.take k)) :
    rho s ≤ order s * 3 ^ (order s - 1) := by
  induction s using List.reverseRecOn with
  | nil =>
    simp [rho, affineNum]
  | append_singleton p b ih =>
    have Hp : ∀ k, p[k]? = some true → 2 ^ k ≤ 3 ^ order (p.take k) := by
      intro k hk
      have hlt : k < p.length := by
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at hk
        simp at hk
      have hk' : (p ++ [b])[k]? = some true := by
        rw [List.getElem?_append_left hlt]
        exact hk
      have h := H k hk'
      rwa [List.take_append_of_le_length hlt.le] at h
    have hp := ih Hp
    cases b with
    | false =>
      rw [rho_append_false, order_append_single]
      simpa using hp
    | true =>
      have hlast : 2 ^ p.length ≤ 3 ^ order p := by
        have h := H p.length (by simp)
        rwa [List.take_append_of_le_length le_rfl, List.take_length] at h
      rw [rho_append_true, order_append_single]
      simp only [↓reduceIte, Nat.add_sub_cancel]
      have h3 := three_mul_mul_pow_pred (order p)
      have hmul : 3 * rho p ≤ 3 * (order p * 3 ^ (order p - 1)) := Nat.mul_le_mul_left 3 hp
      rw [add_mul, one_mul]
      omega

/-- rho s ≤ n 3^(n-1) for an admissible word s of Order n. -/
theorem rho_le_of_admissible (s : List Bool) (hA : Admissible s) :
    rho s ≤ order s * 3 ^ (order s - 1) := by
  apply rho_le_of_steps
  intro k hk
  have hlt : k < s.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hk
    simp at hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]
    simp only [pow_zero]
    exact Nat.one_le_pow _ _ (by norm_num)
  · have h := hA.prefix_gt k hpos hlt
    rw [one_lt_seqProduct_iff, List.length_take, min_eq_left hlt.le] at h
    exact h.le

/-- A member x of an admissible class with n 3^(n-1) < d_23 x drops at the end of its word. -/
theorem drop_of_large (s : List Bool) (x : ℕ) (hA : Admissible s)
    (hs : tBits x s.length = s) (hx : order s * 3 ^ (order s - 1) < d_23 s * x) :
    tStep^[s.length] x < x :=
  (drop_iff_rho s x hA hs).mpr (lt_of_le_of_lt (rho_le_of_admissible s hA) hx)

/-- ClassDrops only needs checking at small class ids: d_23 * classId ≤ n 3^(n-1). -/
theorem classDrops_iff_small :
    ClassDrops ↔ ∀ s, Admissible s → 1 < classId s →
      d_23 s * classId s ≤ order s * 3 ^ (order s - 1) → rho s < d_23 s * classId s := by
  constructor
  · intro h s hA hc _
    exact h s hA hc
  · intro h s hA hc
    by_cases hsmall : d_23 s * classId s ≤ order s * 3 ^ (order s - 1)
    · exact h s hA hc hsmall
    · exact lt_of_le_of_lt (rho_le_of_admissible s hA) (Nat.lt_of_not_le hsmall)

end AcceleratedCollatz
