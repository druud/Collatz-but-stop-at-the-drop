-- SPDX-License-Identifier: MIT
import BestOfOrder.Bridge

/-!
  The meeting split (paper, Theorem C). Cut a word after a start part p (m letters, w ones) and
  let t be the drop part. Then rho (p ++ t) = 3^(order t) rho p + 2^m rho t (`rho_split`), and
  with y = T^m(c), 2^m y = 3^w c + rho p, so for every λ
  rho - λ c = rho p (3^(order t) + λ/3^w) + 2^m (rho t - λ y/3^w) (`split_identity`).
  x is in the class of p ++ t iff x is in the class of p and T^m(x) in that of t (`mem_split_iff`);
  conversely any y in the class of t with 3^w x + rho p = 2^m y gives a member x of p ++ t
  (`mem_of_meet`), and such an x exists iff 3^w divides 2^m y - rho p (`exists_start_iff`):
  the two parts meet in one congruence modulo 3^w.
-/

namespace BestOfOrder

open AcceleratedCollatz

/-- The constant of the cut word. -/
theorem rho_split (p t : List Bool) :
    rho (p ++ t) = 3 ^ order t * rho p + 2 ^ p.length * rho t :=
  rho_append p t

/-- Theorem C, the identity. -/
theorem split_identity (p t : List Bool) (lam c y : ℚ)
    (hy : 2 ^ p.length * y = 3 ^ order p * c + rho p) :
    (rho (p ++ t) : ℚ) - lam * c =
      rho p * (3 ^ order t + lam / 3 ^ order p) + 2 ^ p.length * (rho t - lam * y / 3 ^ order p) := by
  have h3 : (3 : ℚ) ^ order p ≠ 0 := by positivity
  have hc : c = (2 ^ p.length * y - rho p) / 3 ^ order p := by
    rw [eq_div_iff h3]
    linarith
  rw [rho_split]
  push_cast
  rw [hc]
  field_simp
  ring

/-- The class of p ++ t: the class of p, then that of t from T^m. -/
theorem mem_split_iff (p t : List Bool) (x : ℕ) :
    tBits x (p ++ t).length = p ++ t ↔
      tBits x p.length = p ∧ tBits (tStep^[p.length] x) t.length = t := by
  rw [List.length_append, tBits_add']
  constructor
  · intro h
    exact List.append_inj h (by rw [length_tBits'])
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- A member of p ++ t meets its drop part at y = T^m(x), with 3^w x + rho p = 2^m y. -/
theorem meet_of_mem {p t : List Bool} {x : ℕ} (hx : tBits x (p ++ t).length = p ++ t) :
    3 ^ order p * x + rho p = 2 ^ p.length * tStep^[p.length] x ∧
      tBits (tStep^[p.length] x) t.length = t := by
  obtain ⟨h1, h2⟩ := (mem_split_iff p t x).mp hx
  refine ⟨?_, h2⟩
  have h := affine p.length x
  rw [h1] at h
  exact h.symm

/-- Theorem C, conversely: a drop part y and a start x tied by 3^w x + rho p = 2^m y form a
    member of p ++ t. -/
theorem mem_of_meet {p t : List Bool} {x y : ℕ}
    (hxy : 3 ^ order p * x + rho p = 2 ^ p.length * y) (hy : tBits y t.length = t) :
    tBits x (p ++ t).length = p ++ t := by
  have h1 : tBits x p.length = p := (mem_class_iff p x).mpr ⟨y, hxy⟩
  have hT : tStep^[p.length] x = y := by
    have h := affine p.length x
    rw [h1, hxy] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  exact (mem_split_iff p t x).mpr ⟨h1, by rw [hT]; exact hy⟩

/-- The only tie: a start exists for y iff 3^w divides 2^m y - rho p. -/
theorem exists_start_iff (p : List Bool) (y : ℕ) (hy : rho p ≤ 2 ^ p.length * y) :
    (∃ x, 3 ^ order p * x + rho p = 2 ^ p.length * y) ↔
      3 ^ order p ∣ 2 ^ p.length * y - rho p := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, Nat.sub_eq_of_eq_add hx.symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have h := Nat.sub_add_cancel hy
    rw [hx] at h
    exact h

end BestOfOrder
