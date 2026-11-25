-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Zeta.Best.Base
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Intervals

/-!
  The congruence of the class, the walk, the tail bound and the window below a prefix
  (paper, Lemma 2.4, Lemma 5.3, Corollary 3.3 and Theorem 6.1).

  * `congruence`: x ≡ -rho · 3^(-n) (mod 2^L) for every x of the class of a word.
  * `rho_eq_sum`: rho = Σ_l e_l 3^(n - q_l) 2^l, with n - q_l the ones after letter l.
  * `walk`: rho - λ c = Σ_l 2^l (e_l 3^(n - q_l) - λ t_l), t_l the bits of c < 2^L.
  * `tail_bound`: below a prefix p (j ones), rho ≤ 3^(n-j) rho_p + (R(n) - 3^(n-j) R(j)), stated
    without subtraction; R(n) - 3^(n-j) R(j) is the sum of the wall terms of the ones after j.
  * `window_prefix`: the window for every member x ≥ r of the class below a prefix.
-/

namespace AcceleratedCollatz.Best

/-- Lemma 2.4: every x of the class of s has x ≡ -rho · (3^n)⁻¹ modulo 2^L. -/
theorem congruence {s : List Bool} {x : ℕ} (hx : tBits x s.length = s) :
    (x : ZMod (2 ^ s.length)) =
      -(rho s : ZMod (2 ^ s.length)) * ((3 ^ order s : ℕ) : ZMod _)⁻¹ := by
  have hd := (mem_class_iff s x).mp hx
  have h0 : ((3 ^ order s * x + rho s : ℕ) : ZMod (2 ^ s.length)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hc : Nat.Coprime (3 ^ order s) (2 ^ s.length) :=
    Nat.Coprime.pow (order s) s.length (by decide : Nat.Coprime 3 2)
  have hu := ZMod.coe_mul_inv_eq_one (3 ^ order s) hc
  push_cast at h0 hu ⊢
  have h1 : (3 : ZMod (2 ^ s.length)) ^ order s * x = -(rho s) := eq_neg_of_add_eq_zero_left h0
  calc (x : ZMod (2 ^ s.length))
      = ((3 : ZMod (2 ^ s.length)) ^ order s * ((3 : ZMod (2 ^ s.length)) ^ order s)⁻¹) *
          (x : ZMod (2 ^ s.length)) := by rw [hu, one_mul]
    _ = ((3 : ZMod (2 ^ s.length)) ^ order s * (x : ZMod (2 ^ s.length))) *
          ((3 : ZMod (2 ^ s.length)) ^ order s)⁻¹ := by ring
    _ = -(rho s : ZMod _) * ((3 : ZMod _) ^ order s)⁻¹ := by rw [h1]

/-- The term of letter l in rho: 3^(ones after l) 2^l at a one, 0 at a zero. -/
def rhoTerm (s : List Bool) (l : ℕ) : ℕ :=
  if s.getD l false then 3 ^ order (s.drop (l + 1)) * 2 ^ l else 0

theorem rhoTerm_append {s : List Bool} (b : Bool) {l : ℕ} (hl : l < s.length) :
    rhoTerm (s ++ [b]) l = 3 ^ (if b then 1 else 0) * rhoTerm s l := by
  unfold rhoTerm
  have hb : order [b] = if b then 1 else 0 := by cases b <;> simp [order]
  rw [List.getD_append _ _ _ _ hl, List.drop_append_of_le_length (by omega), order_append, hb]
  split_ifs <;> ring

/-- Lemma 5.3, the constant: rho = Σ_l e_l 3^(n - q_l) 2^l. -/
theorem rho_eq_sum (s : List Bool) :
    rho s = ∑ l ∈ Finset.range s.length, rhoTerm s l := by
  induction s using List.reverseRecOn with
  | nil => simp [rho, affineNum]
  | append_singleton s b ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
    have hlast : rhoTerm (s ++ [b]) s.length = if b then 2 ^ s.length else 0 := by
      unfold rhoTerm
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.drop_eq_nil_of_le (by simp)]
      simp [order]
    have hsum : ∑ l ∈ Finset.range s.length, rhoTerm (s ++ [b]) l =
        3 ^ (if b then 1 else 0) * ∑ l ∈ Finset.range s.length, rhoTerm s l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l hl => rhoTerm_append b (Finset.mem_range.mp hl)
    rw [hsum, hlast, ← ih]
    cases b
    · simp [rho_append_false]
    · simp [rho_append_true]

/-- The bits of c below 2^L: c % 2^L = Σ_{l<L} 2^l t_l. -/
theorem mod_eq_sum_bits (c L : ℕ) :
    c % 2 ^ L = ∑ l ∈ Finset.range L, 2 ^ l * (c / 2 ^ l % 2) := by
  induction L with
  | zero => simp [Nat.mod_one]
  | succ L ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ, Nat.mod_mul]

/-- Lemma 5.3, the walk: for c < 2^L, rho - λ c = Σ_l 2^l (e_l 3^(n - q_l) - λ t_l). -/
theorem walk (s : List Bool) {c : ℕ} (hc : c < 2 ^ s.length) (lam : ℚ) :
    (rho s : ℚ) - lam * c = ∑ l ∈ Finset.range s.length,
      2 ^ l * ((if s.getD l false then (3 : ℚ) ^ order (s.drop (l + 1)) else 0) -
        lam * ((c / 2 ^ l % 2 : ℕ) : ℚ)) := by
  have hr := rho_eq_sum s
  have hb := mod_eq_sum_bits c s.length
  rw [Nat.mod_eq_of_lt hc] at hb
  have hr' : (rho s : ℚ) = ∑ l ∈ Finset.range s.length, (rhoTerm s l : ℚ) := by
    rw [hr]; push_cast; rfl
  have hb' : (c : ℚ) = ∑ l ∈ Finset.range s.length, (2 : ℚ) ^ l * ((c / 2 ^ l % 2 : ℕ) : ℚ) := by
    conv_lhs => rw [hb]
    push_cast; rfl
  rw [hr', hb', Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold rhoTerm
  split_ifs <;> push_cast <;> ring

/-- The tail bound, by induction on the letters after the prefix: under the wall condition at
    each one, rho (p ++ t) + 3^(order t) R(order p) ≤ 3^(order t) rho p + R(order p + order t). -/
theorem tail_bound_of_steps (p t : List Bool)
    (H : ∀ k, (p ++ t)[k]? = some true → k + 1 ≤ p2_of (order ((p ++ t).take k))) :
    rho (p ++ t) + 3 ^ order t * rhoMax (order p) ≤
      3 ^ order t * rho p + rhoMax (order p + order t) := by
  induction t using List.reverseRecOn with
  | nil => simp [order]
  | append_singleton t b ih =>
    have Ht : ∀ k, (p ++ t)[k]? = some true → k + 1 ≤ p2_of (order ((p ++ t).take k)) := by
      intro k hk
      have hlt : k < (p ++ t).length := by
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at hk
        simp at hk
      have hk' : (p ++ (t ++ [b]))[k]? = some true := by
        rw [← List.append_assoc, List.getElem?_append_left hlt]
        exact hk
      have h := H k hk'
      rwa [← List.append_assoc, List.take_append_of_le_length hlt.le] at h
    have ih := ih Ht
    rw [← List.append_assoc]
    cases b with
    | false =>
      rw [rho_append_false, order_append_single]
      simpa using ih
    | true =>
      have hlast : (p ++ t).length + 1 ≤ p2_of (order (p ++ t)) := by
        have h := H (p ++ t).length (by rw [← List.append_assoc]; simp)
        rwa [← List.append_assoc, List.take_append_of_le_length le_rfl, List.take_length] at h
      have hpow : 2 ^ (p ++ t).length ≤ 2 ^ (p2_of (order (p ++ t)) - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [order_append] at hpow
      rw [rho_append_true, order_append_single]
      simp only [↓reduceIte]
      rw [← Nat.add_assoc, rhoMax_succ, pow_succ]
      nlinarith

/-- Corollary 3.3, the tail bound: for an admissible word p ++ t,
    rho + 3^(n-j) R(j) ≤ 3^(n-j) rho_p + R(n), with j = order p and n - j = order t. -/
theorem tail_bound {p t : List Bool} (hA : Admissible (p ++ t)) :
    rho (p ++ t) + 3 ^ order t * rhoMax (order p) ≤
      3 ^ order t * rho p + rhoMax (order (p ++ t)) := by
  rw [order_append]
  exact tail_bound_of_steps p t (admissible_step_le hA)

/-- Theorem 6.1, below a prefix: a member x ≥ r of the class of an admissible word p ++ t with a
    ratio above b/a satisfies r (2^L b - 3^n a) < (3^(n-j) rho_p + R(n) - 3^(n-j) R(j)) a. -/
theorem window_prefix {p t : List Bool} (hA : Admissible (p ++ t)) {x r a b : ℕ}
    (hx : tBits x (p ++ t).length = p ++ t) (hrx : r ≤ x)
    (hgap : 3 ^ order (p ++ t) * a < 2 ^ (p ++ t).length * b)
    (hab : b * x < a * tStep^[(p ++ t).length] x) :
    (r : ℤ) * (2 ^ (p ++ t).length * b - 3 ^ order (p ++ t) * a) <
      ((3 ^ order t * rho p + rhoMax (order (p ++ t)) : ℕ) -
        (3 ^ order t * rhoMax (order p) : ℕ)) * a := by
  set s := p ++ t with hs
  have h := affine s.length x
  rw [hx] at h
  have h' : (2 : ℤ) ^ s.length * (tStep^[s.length] x : ℤ) = 3 ^ order s * x + rho s := by
    exact_mod_cast h
  have hab' : (b : ℤ) * x < a * (tStep^[s.length] x : ℤ) := by exact_mod_cast hab
  have hT : ((rho s + 3 ^ order t * rhoMax (order p) : ℕ) : ℤ) ≤
      ((3 ^ order t * rho p + rhoMax (order s) : ℕ) : ℤ) := by exact_mod_cast tail_bound hA
  have hgap' : (3 : ℤ) ^ order s * a < 2 ^ s.length * b := by exact_mod_cast hgap
  have hrx' : (r : ℤ) ≤ x := by exact_mod_cast hrx
  push_cast at hT ⊢
  have h1 : (2 : ℤ) ^ s.length * (b * x) < 2 ^ s.length * (a * (tStep^[s.length] x : ℤ)) :=
    mul_lt_mul_of_pos_left hab' (by positivity)
  have h2 :
      (2 : ℤ) ^ s.length * (a * (tStep^[s.length] x : ℤ)) = a * (3 ^ order s * x + rho s) := by
    rw [← h']; ring
  have ha : (0 : ℤ) ≤ a := by positivity
  have h3 : (r : ℤ) * (2 ^ s.length * b - 3 ^ order s * a) ≤
      (x : ℤ) * (2 ^ s.length * b - 3 ^ order s * a) :=
    mul_le_mul_of_nonneg_right hrx' (by linarith)
  nlinarith

end AcceleratedCollatz.Best
