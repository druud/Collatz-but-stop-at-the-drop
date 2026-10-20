-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketOneQ
import AcceleratedCollatz.TChainQ

/-!
  One bracket per odd step does not determine the word, for every odd q ≥ 5. With
  L = p2Q q 2 and B = 1 0^(p2Q q 1 - 1) the word of Order 1, the words
  1 0 1 0^(L-3) = 1 | 0 | B | 0 ... 0 and 1 1 0^(L-2) = 1 | B | 0 ... 0 are admissible
  (`admissibleQ_clashLeft`, `admissibleQ_clashRight`), differ, and both have the one-bracket
  word [0, 2] (`bracketWordOneQ_clashLeft`, `bracketWordOneQ_clashRight`): the filler zeros add
  nothing to it (`bracketWordOneQ_chain`). So the one-bracket word is not one-to-one on the
  admissible words of Order 2 (`not_injOn_bracketWordOneQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- `LevelUpQ` as a comparison with p2Q, for odd q. -/
theorem levelUpQ_iff_lt (hodd : Odd q) (hq : 3 ≤ q) (os : List ℕ) :
    LevelUpQ q os ↔ 1 + (os.map (p2Q q)).sum < p2Q q (1 + os.sum) := by
  unfold LevelUpQ
  exact two_pow_lt_q_pow_iff hodd hq (by omega)

/-- For q ≥ 5 the word of Order 1 has at least three letters. -/
theorem two_lt_p2Q_one (hodd : Odd q) (hq : 5 ≤ q) : 2 < p2Q q 1 := by
  rw [← two_pow_lt_q_pow_iff hodd (by omega) le_rfl, pow_one]
  omega

/-- For q ≥ 5 the words of Order 2 are at least two letters longer than that of Order 1. -/
theorem p2Q_one_add_two_le (hodd : Odd q) (hq : 5 ≤ q) : p2Q q 1 + 2 ≤ p2Q q 2 := by
  have hq3 : 3 ≤ q := by
    omega
  have h3 := two_lt_p2Q_one hodd hq
  have hlo : 2 ^ (p2Q q 1 - 1) ≤ q := by
    have h := p2Q_spec_lower hq3 1
    rw [pow_one] at h
    exact h
  have hsq : 2 ^ (2 * (p2Q q 1 - 1)) ≤ q ^ 2 := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left hlo 2
  have hlt : 2 ^ (2 * (p2Q q 1 - 1)) < 2 ^ p2Q q 2 := lt_of_le_of_lt hsq (p2Q_spec hq3 2)
  have hk := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  omega

/-- The word of Order 1, 1 0^(p2Q q 1 - 1), as a 1 and filler zeros. -/
theorem order_one_word_eq (n : ℕ) :
    true :: (List.replicate n [false]).flatten = true :: List.replicate n false := by
  rw [List.flatten_replicate_singleton]

/-- Filler zeros are admissible. -/
theorem forall_admissibleQ_replicate_false (n : ℕ) :
    ∀ b ∈ List.replicate n [false], AdmissibleQ q b := by
  intro b hb
  rw [List.eq_of_mem_replicate hb]
  exact admissibleQ_singleton_false q

/-- The word of Order 1 is admissible. -/
theorem admissibleQ_order_one (hodd : Odd q) (hq : 3 ≤ q) :
    AdmissibleQ q (true :: List.replicate (p2Q q 1 - 1) false) := by
  have h2 : 1 < p2Q q 1 := by
    rw [← two_pow_lt_q_pow_iff hodd hq le_rfl]
    simp only [pow_one]
    omega
  rw [← order_one_word_eq,
    admissibleQ_iff_chainQ hodd hq _ (forall_admissibleQ_replicate_false _),
    levelUpQ_iff_lt hodd hq, levelUpQ_iff_lt hodd hq]
  have hmap :
      (List.replicate (p2Q q 1 - 1) [false]).map order = List.replicate (p2Q q 1 - 1) 0 := by
    rw [List.map_replicate]
    rfl
  rw [hmap, List.dropLast_replicate]
  simp only [List.map_replicate, List.sum_replicate, p2Q_zero, smul_eq_mul, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one]
  omega

/-- The order of the word of Order 1. -/
theorem order_order_one_word (n : ℕ) : order (true :: List.replicate n false) = 1 := by
  rw [order_cons, order_replicate_false]
  rfl

/-- The left word 1 0 1 0^(L-3) as a chain 1 | 0 | B | 0 ... 0. -/
theorem clashLeft_eq (z : ℕ) :
    [true, false, true] ++ List.replicate (p2Q q 1 - 1 + z) false =
      true :: ([false] :: (true :: List.replicate (p2Q q 1 - 1) false) ::
        List.replicate z [false]).flatten := by
  simp only [List.flatten_cons, List.flatten_replicate_singleton, List.replicate_add,
    List.cons_append, List.nil_append]

/-- The right word 1 1 0^(L-2) as a chain 1 | B | 0 ... 0. -/
theorem clashRight_eq (z : ℕ) :
    [true, true] ++ List.replicate (p2Q q 1 - 1 + z) false =
      true :: ((true :: List.replicate (p2Q q 1 - 1) false) ::
        List.replicate z [false]).flatten := by
  simp only [List.flatten_cons, List.flatten_replicate_singleton, List.replicate_add,
    List.cons_append, List.nil_append]

/-- The blocks of both chains are admissible. -/
theorem forall_admissibleQ_clash (hodd : Odd q) (hq : 3 ≤ q) (pre : List (List Bool))
    (hpre : ∀ b ∈ pre, AdmissibleQ q b) (z : ℕ) :
    ∀ b ∈ pre ++ (true :: List.replicate (p2Q q 1 - 1) false) :: List.replicate z [false],
      AdmissibleQ q b := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact hpre b h
  · rcases List.mem_cons.mp h with h1 | h1
    · rw [h1]
      exact admissibleQ_order_one hodd hq
    · exact forall_admissibleQ_replicate_false z b h1

/-- The left chain 1 | 0 | B | 0^z is admissible when p2Q q 2 = p2Q q 1 + 2 + z. -/
theorem admissibleQ_clashLeft_of (hodd : Odd q) (hq : 3 ≤ q) {z : ℕ}
    (hz : p2Q q 2 = p2Q q 1 + 2 + z) (h3 : 2 < p2Q q 1) :
    AdmissibleQ q (true :: ([false] :: (true :: List.replicate (p2Q q 1 - 1) false) ::
      List.replicate z [false]).flatten) := by
  have hbs := forall_admissibleQ_clash hodd hq [[false]]
    (forall_admissibleQ_replicate_false 1) z
  rw [List.singleton_append] at hbs
  rw [admissibleQ_iff_chainQ hodd hq _ hbs, levelUpQ_iff_lt hodd hq, levelUpQ_iff_lt hodd hq]
  have hmap : ([false] :: (true :: List.replicate (p2Q q 1 - 1) false) ::
      List.replicate z [false]).map order = 0 :: 1 :: List.replicate z 0 := by
    rw [List.map_cons, List.map_cons, order_order_one_word, List.map_replicate]
    rfl
  rw [hmap]
  constructor
  · rcases z with _ | z
    · have hd : (0 :: 1 :: List.replicate 0 0).dropLast = [0] := rfl
      rw [hd]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, p2Q_zero,
        Nat.add_zero]
      omega
    · have hd : (0 :: 1 :: List.replicate (z + 1) 0).dropLast = 0 :: 1 :: List.replicate z 0 := by
        rw [List.dropLast_cons_cons, List.dropLast_cons_of_ne_nil (by simp),
          List.dropLast_replicate]
        rfl
      rw [hd]
      simp only [List.map_cons, List.map_replicate, List.sum_cons, List.sum_replicate,
        p2Q_zero, smul_eq_mul, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
      have h2 : (1 + 1) = 2 := rfl
      rw [h2]
      omega
  · simp only [List.map_cons, List.map_replicate, List.sum_cons, List.sum_replicate,
      p2Q_zero, smul_eq_mul, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
    have h2 : (1 + 1) = 2 := rfl
    rw [h2]
    omega

/-- The right chain 1 | B | 0^(z+1) is admissible when p2Q q 2 = p2Q q 1 + 2 + z. -/
theorem admissibleQ_clashRight_of (hodd : Odd q) (hq : 3 ≤ q) {z : ℕ}
    (hz : p2Q q 2 = p2Q q 1 + 2 + z) :
    AdmissibleQ q (true :: ((true :: List.replicate (p2Q q 1 - 1) false) ::
      List.replicate (z + 1) [false]).flatten) := by
  have hbs := forall_admissibleQ_clash hodd hq [] (fun b hb => absurd hb List.not_mem_nil) (z + 1)
  rw [List.nil_append] at hbs
  rw [admissibleQ_iff_chainQ hodd hq _ hbs, levelUpQ_iff_lt hodd hq, levelUpQ_iff_lt hodd hq]
  have hmap : ((true :: List.replicate (p2Q q 1 - 1) false) ::
      List.replicate (z + 1) [false]).map order = 1 :: List.replicate (z + 1) 0 := by
    rw [List.map_cons, order_order_one_word, List.map_replicate]
    rfl
  rw [hmap]
  constructor
  · rw [List.dropLast_cons_of_ne_nil (by simp), List.dropLast_replicate]
    simp only [List.map_cons, List.map_replicate, List.sum_cons, List.sum_replicate,
      p2Q_zero, smul_eq_mul, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.add_sub_cancel]
    have h2 : (1 + 1) = 2 := rfl
    rw [h2]
    omega
  · simp only [List.map_cons, List.map_replicate, List.sum_cons, List.sum_replicate,
      p2Q_zero, smul_eq_mul, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
    have h2 : (1 + 1) = 2 := rfl
    rw [h2]
    omega

/-- A filler zero has the empty one-bracket word. -/
theorem bracketWordOneQ_false (q : ℕ) : bracketWordOneQ q [false] = [] := by
  rfl

/-- Filler zeros add nothing to a flattened list of one-bracket words. -/
theorem flatten_map_replicate_false (q z : ℕ) :
    ((List.replicate z [false]).map (bracketWordOneQ q)).flatten = [] := by
  rw [List.map_replicate, bracketWordOneQ_false, List.flatten_replicate_nil]

/-- The one-bracket word of the word of Order 1 is [1]. -/
theorem bracketWordOneQ_order_one (hodd : Odd q) (hq : 3 ≤ q) :
    bracketWordOneQ q (true :: List.replicate (p2Q q 1 - 1) false) = [1] := by
  have hA := admissibleQ_order_one hodd hq
  rw [← order_one_word_eq] at hA ⊢
  rw [bracketWordOneQ_chain hq (forall_admissibleQ_replicate_false _) hA,
    flatten_map_replicate_false]
  rfl

/-- The left word 1 0 1 0^(L-3), L = p2Q q 2, is admissible. -/
theorem admissibleQ_clashLeft (hodd : Odd q) (hq : 5 ≤ q) :
    AdmissibleQ q ([true, false, true] ++ List.replicate (p2Q q 2 - 3) false) := by
  have hL := p2Q_one_add_two_le hodd hq
  have h3 := two_lt_p2Q_one hodd hq
  have h3 := two_lt_p2Q_one hodd hq
  have hc : p2Q q 2 - 3 = p2Q q 1 - 1 + (p2Q q 2 - (p2Q q 1 + 2)) := by
    omega
  rw [hc, clashLeft_eq]
  exact admissibleQ_clashLeft_of hodd (by omega) (by omega) h3

/-- The right word 1 1 0^(L-2), L = p2Q q 2, is admissible. -/
theorem admissibleQ_clashRight (hodd : Odd q) (hq : 5 ≤ q) :
    AdmissibleQ q ([true, true] ++ List.replicate (p2Q q 2 - 2) false) := by
  have hL := p2Q_one_add_two_le hodd hq
  have h3 := two_lt_p2Q_one hodd hq
  have hc : p2Q q 2 - 2 = p2Q q 1 - 1 + (p2Q q 2 - (p2Q q 1 + 2) + 1) := by
    omega
  rw [hc, clashRight_eq]
  exact admissibleQ_clashRight_of hodd (by omega) (by omega)

/-- The one-bracket word of the left word is [0, 2]. -/
theorem bracketWordOneQ_clashLeft (hodd : Odd q) (hq : 5 ≤ q) :
    bracketWordOneQ q ([true, false, true] ++ List.replicate (p2Q q 2 - 3) false) = [0, 2] := by
  have hA := admissibleQ_clashLeft hodd hq
  have hL := p2Q_one_add_two_le hodd hq
  have h3 := two_lt_p2Q_one hodd hq
  have hc : p2Q q 2 - 3 = p2Q q 1 - 1 + (p2Q q 2 - (p2Q q 1 + 2)) := by
    omega
  rw [hc, clashLeft_eq] at hA ⊢
  have hbs := forall_admissibleQ_clash hodd (by omega) [[false]]
    (forall_admissibleQ_replicate_false 1) (p2Q q 2 - (p2Q q 1 + 2))
  rw [List.singleton_append] at hbs
  rw [bracketWordOneQ_chain (by omega) hbs hA, List.map_cons, List.map_cons,
    bracketWordOneQ_false, bracketWordOneQ_order_one hodd (by omega), List.flatten_cons,
    List.flatten_cons, flatten_map_replicate_false]
  rfl

/-- The one-bracket word of the right word is [0, 2]. -/
theorem bracketWordOneQ_clashRight (hodd : Odd q) (hq : 5 ≤ q) :
    bracketWordOneQ q ([true, true] ++ List.replicate (p2Q q 2 - 2) false) = [0, 2] := by
  have hA := admissibleQ_clashRight hodd hq
  have hL := p2Q_one_add_two_le hodd hq
  have h3 := two_lt_p2Q_one hodd hq
  have hc : p2Q q 2 - 2 = p2Q q 1 - 1 + (p2Q q 2 - (p2Q q 1 + 2) + 1) := by
    omega
  rw [hc, clashRight_eq] at hA ⊢
  have hbs := forall_admissibleQ_clash hodd (by omega) [] (fun b hb => absurd hb List.not_mem_nil)
    (p2Q q 2 - (p2Q q 1 + 2) + 1)
  rw [List.nil_append] at hbs
  rw [bracketWordOneQ_chain (by omega) hbs hA, List.map_cons,
    bracketWordOneQ_order_one hodd (by omega), List.flatten_cons, flatten_map_replicate_false]
  rfl

/-- For every odd q ≥ 5 the one-bracket word is not one-to-one on the admissible words of
    Order 2. -/
theorem not_injOn_bracketWordOneQ (hodd : Odd q) (hq : 5 ≤ q) :
    ¬Set.InjOn (bracketWordOneQ q) (admSetQ q 2 : Set (List Bool)) := by
  intro h
  have hord : ∀ (u : List Bool) (n : ℕ), order u = 2 → order (u ++ List.replicate n false) = 2 := by
    intro u n hu
    rw [order_append, order_replicate_false, hu]
  have h1 : [true, false, true] ++ List.replicate (p2Q q 2 - 3) false ∈ admSetQ q 2 :=
    (mem_admSetQ (by omega) 2 _).mpr ⟨admissibleQ_clashLeft hodd hq, hord _ _ rfl⟩
  have h2 : [true, true] ++ List.replicate (p2Q q 2 - 2) false ∈ admSetQ q 2 :=
    (mem_admSetQ (by omega) 2 _).mpr ⟨admissibleQ_clashRight hodd hq, hord _ _ rfl⟩
  have he := h h1 h2 ((bracketWordOneQ_clashLeft hodd hq).trans
    (bracketWordOneQ_clashRight hodd hq).symm)
  simp at he

end AcceleratedCollatz
