-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TCovering
import AcceleratedCollatz.TEncode
import AcceleratedCollatz.TSplitQ

/-!
  First-drop split of parity vectors: the q = 3 case of TSplitQ (`isSplitQ_three`).
  Every admissible s of Order ≥ 1 is 1 :: (A1 ++ ... ++ Ak) with every block Ai
  admissible (`exists_split`); the blocks are unique (`split_unique`, from
  `flatten_inj_of_admissible`); their Orders sum to order s - 1 (`order_split`).
  For q = 3 an Order-0 block "0" can only be the last block (`zero_block_last`).
-/

namespace AcceleratedCollatz

variable (s : List Bool)

/-- s = 1 :: flatten bs with admissible blocks. -/
structure IsSplit (s : List Bool) (bs : List (List Bool)) : Prop where
  /-- s is 1 followed by the blocks. -/
  eq : s = true :: bs.flatten
  /-- Every block is admissible. -/
  adm : ∀ b ∈ bs, Admissible b

/-- Blocks are admissible in the q-family at q = 3 iff they are admissible. -/
theorem forall_admissibleQ_three (bs : List (List Bool)) :
    (∀ b ∈ bs, AdmissibleQ 3 b) ↔ ∀ b ∈ bs, Admissible b := by
  simp only [admissibleQ_three]

/-- `IsSplit` is `IsSplitQ` at q = 3. -/
theorem isSplitQ_three (bs : List (List Bool)) : IsSplitQ 3 s bs ↔ IsSplit s bs := by
  constructor
  · intro h
    exact ⟨h.eq, (forall_admissibleQ_three bs).mp h.adm⟩
  · intro h
    exact ⟨h.eq, (forall_admissibleQ_three bs).mpr h.adm⟩

/-- Admissible blocks: 3^(order) ≤ 2^(length) for their concatenation. -/
theorem pow_le_of_admissible_blocks (bs : List (List Bool)) (h : ∀ b ∈ bs, Admissible b) :
    3 ^ order bs.flatten ≤ 2 ^ bs.flatten.length := by
  induction bs with
  | nil =>
    simp [order]
  | cons b t ih =>
    have hb : 3 ^ order b < 2 ^ b.length := (seqProduct_lt_one_iff b).mp (h b (by simp)).2
    have ht := ih (fun c hc => h c (by simp [hc]))
    rw [List.flatten_cons, order_append, List.length_append, pow_add, pow_add]
    exact Nat.mul_le_mul hb.le ht

/-- A factorization into admissible blocks is unique. -/
theorem flatten_inj_of_admissible :
    ∀ (bs bs' : List (List Bool)), (∀ b ∈ bs, Admissible b) → (∀ b ∈ bs', Admissible b) →
      bs.flatten = bs'.flatten → bs = bs' :=
  fun bs bs' h h' heq => flatten_inj_of_admissibleQ (q := 3) bs bs'
    ((forall_admissibleQ_three bs).mpr h) ((forall_admissibleQ_three bs').mpr h') heq

/-- Factorization of the remainder r of an admissible P ++ r (P ≠ []). -/
theorem exists_blocks : ∀ (n : ℕ) (P r : List Bool), r.length = n → Admissible (P ++ r) →
    P ≠ [] → ∃ bs : List (List Bool), r = bs.flatten ∧ ∀ b ∈ bs, Admissible b := by
  intro n P r hn hA hP
  obtain ⟨bs, hbs, hadm⟩ := exists_blocksQ (q := 3) (by decide) le_rfl n P r hn
    ((admissibleQ_three _).mpr hA) hP
  exact ⟨bs, hbs, (forall_admissibleQ_three bs).mp hadm⟩

/-- Every admissible s of Order ≥ 1 splits into admissible blocks. -/
theorem exists_split (hA : Admissible s) (hord : 1 ≤ order s) :
    ∃ bs, IsSplit s bs := by
  obtain ⟨bs, h⟩ := exists_splitQ (q := 3) (by decide) le_rfl ((admissibleQ_three s).mpr hA) hord
  exact ⟨bs, (isSplitQ_three s bs).mp h⟩

/-- The split is unique. -/
theorem split_unique (bs bs' : List (List Bool)) (h : IsSplit s bs)
    (h' : IsSplit s bs') : bs = bs' :=
  splitQ_unique ((isSplitQ_three s bs).mpr h) ((isSplitQ_three s bs').mpr h')

theorem order_split (bs : List (List Bool)) (h : IsSplit s bs) :
    order s = (bs.map order).sum + 1 :=
  order_splitQ ((isSplitQ_three s bs).mpr h)

/-- A block followed by another block has Order ≥ 1. -/
theorem zero_block_last (hA : Admissible s) (pre post : List (List Bool))
    (b : List Bool) (h : IsSplit s (pre ++ b :: post)) (hpost : post ≠ []) : 1 ≤ order b := by
  by_contra h0
  have hbA : Admissible b := h.adm b (by simp)
  have hb : b = [false] := admissible_order_zero b hbA (by omega)
  have hpreA : ∀ c ∈ pre, Admissible c := fun c hc => h.adm c (by simp [hc])
  have hbound := pow_le_of_admissible_blocks pre hpreA
  obtain ⟨c, ct, rfl⟩ : ∃ c ct, post = c :: ct := by
    cases post with
    | nil =>
      exact absurd rfl hpost
    | cons c ct =>
      exact ⟨c, ct, rfl⟩
  have hcA : Admissible c := h.adm c (by simp)
  have hcne : c ≠ [] := by
    intro hn
    rw [hn] at hcA
    exact not_admissible_nil hcA
  have hs : s = (true :: (pre.flatten ++ [false])) ++ (c ++ ct.flatten) := by
    rw [h.eq, hb]
    simp
  have hApow := (admissible_iff_pow s).mp hA
  have hQlen : (true :: (pre.flatten ++ [false])).length = pre.flatten.length + 2 := by
    simp
  have hslen : pre.flatten.length + 2 < s.length := by
    rw [hs, List.length_append, hQlen]
    have : 0 < (c ++ ct.flatten).length := by
      simp only [List.length_append, List.length_flatten, add_pos_iff]
      exact Or.inl (List.length_pos_iff.mpr hcne)
    omega
  have hp := hApow.1 (pre.flatten.length + 2) hslen (by omega)
  rw [hs, List.take_append_of_le_length (by rw [hQlen]), ← hQlen, List.take_length] at hp
  rw [hQlen, order_cons, order_append] at hp
  have ho : order [false] = 0 := by
    simp [order]
  simp only [ho, ↓reduceIte, add_zero] at hp
  have h4 : 2 ^ (pre.flatten.length + 2) = 2 ^ pre.flatten.length * 4 := by
    rw [pow_add]
    norm_num
  have h3 : 3 ^ (order pre.flatten + 1) = 3 ^ order pre.flatten * 3 := pow_succ _ _
  rw [h4, h3] at hp
  omega

end AcceleratedCollatz
