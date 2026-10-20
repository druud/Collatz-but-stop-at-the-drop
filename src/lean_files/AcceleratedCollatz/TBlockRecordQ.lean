-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TGridOrderQ

/-!
  Record Orders by the block factor, for odd q ≥ 3. The block factor of Order o is
  q^o / 2^p2Q(o) (`blockFactorQ`). p2Q is additive up to 1: p2Q(a + b) is p2Q(a) + p2Q(b)
  or one less (`p2Q_add_le`, `p2Q_add_le_succ`). The block factor of a + b is below that
  of a in the first case and, for b ≥ 1, above it in the second
  (`blockFactorQ_add_lt_iff`, `blockFactorQ_lt_add_iff`). The lower record Orders are the
  n with p2Q(n) = p2Q(a) + p2Q(n - a) for every 1 ≤ a < n (`lowerRecordQ_iff_add`): the
  Orders whose block factor is below every earlier one (`lowerRecordQ_iff_blockFactorQ`).
  The upper record Orders are the n with p2Q(n) + 1 = p2Q(a) + p2Q(n - a) for every
  1 ≤ a < n (`upperRecordQ_iff_add`): the Orders whose block factor is above every
  earlier one (`upperRecordQ_iff_blockFactorQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- p2Q(a + b) ≤ p2Q(a) + p2Q(b). -/
theorem p2Q_add_le (hq : 3 ≤ q) (a b : ℕ) : p2Q q (a + b) ≤ p2Q q a + p2Q q b := by
  rw [← q_pow_lt_two_pow_iff hq, pow_add, pow_add]
  exact Nat.mul_lt_mul'' (p2Q_spec hq a) (p2Q_spec hq b)

/-- p2Q(a) + p2Q(b) ≤ p2Q(a + b) + 1. -/
theorem p2Q_add_le_succ (hq : 3 ≤ q) (a b : ℕ) : p2Q q a + p2Q q b ≤ p2Q q (a + b) + 1 := by
  have h1 : 2 ^ (p2Q q a - 1) * 2 ^ (p2Q q b - 1) ≤ q ^ a * q ^ b :=
    Nat.mul_le_mul (p2Q_spec_lower hq a) (p2Q_spec_lower hq b)
  rw [← pow_add, ← pow_add] at h1
  have h2 : 2 ^ (p2Q q a - 1 + (p2Q q b - 1)) < 2 ^ p2Q q (a + b) :=
    lt_of_le_of_lt h1 (p2Q_spec hq (a + b))
  have h3 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  have ha := one_le_p2Q q a
  have hb := one_le_p2Q q b
  omega

/-- Block factor of Order o: q^o / 2^p2Q(o), the level change across a block. -/
def blockFactorQ (q o : ℕ) : ℚ := (q : ℚ) ^ o / 2 ^ p2Q q o

/-- Block factors compare like the cross products q^a 2^p2Q(c) and q^c 2^p2Q(a). -/
theorem blockFactorQ_lt_iff (q a c : ℕ) :
    blockFactorQ q a < blockFactorQ q c ↔ q ^ a * 2 ^ p2Q q c < q ^ c * 2 ^ p2Q q a := by
  unfold blockFactorQ
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

/-- The block factor falls from a to a + b exactly when p2Q is additive at (a, b). -/
theorem blockFactorQ_add_lt_iff (hq : 3 ≤ q) (a b : ℕ) :
    blockFactorQ q (a + b) < blockFactorQ q a ↔ p2Q q (a + b) = p2Q q a + p2Q q b := by
  have hle := p2Q_add_le hq a b
  rw [blockFactorQ_lt_iff, pow_add, mul_assoc, Nat.mul_lt_mul_left (pow_pos (by omega) _),
    q_pow_mul_lt_iff hq]
  omega

/-- For b ≥ 1 the block factor rises from a to a + b exactly when p2Q(a + b) is one
    less than p2Q(a) + p2Q(b). -/
theorem blockFactorQ_lt_add_iff (hodd : Odd q) (hq : 3 ≤ q) (a : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    blockFactorQ q a < blockFactorQ q (a + b) ↔ p2Q q (a + b) + 1 = p2Q q a + p2Q q b := by
  have hle := p2Q_add_le_succ hq a b
  rw [blockFactorQ_lt_iff, pow_add, mul_assoc, Nat.mul_lt_mul_left (pow_pos (by omega) _),
    lt_q_pow_mul_iff hodd hq hb]
  omega

/-- Lower record Orders: p2Q(n) = p2Q(a) + p2Q(n - a) at every split. -/
theorem lowerRecordQ_iff_add (hq : 3 ≤ q) (n : ℕ) :
    LowerRecordQ q n ↔ ∀ a, 1 ≤ a → a < n → p2Q q n = p2Q q a + p2Q q (n - a) := by
  constructor
  · intro hR a ha1 han
    obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have h1 := hR a ha1 han
    have h2 := hR b (by omega) (by omega)
    have hle := p2Q_add_le hq a b
    have hA := one_le_p2Q q a
    have hB := one_le_p2Q q b
    by_contra hne
    have hP : p2Q q (a + b) - 1 ≤ (p2Q q a - 1) + (p2Q q b - 1) := by
      omega
    have h3 := Nat.mul_le_mul_left (a + b) hP
    nlinarith
  · intro hB a ha1 han
    obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
    have h1 := hB a ha1 han
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : (p2Q q a - 1) * b < a * p2Q q b := p2Q_sub_one_mul_lt hq ha1
    have hA := one_le_p2Q q a
    have hP : p2Q q (a + b) - 1 = (p2Q q a - 1) + p2Q q b := by
      omega
    rw [hP]
    nlinarith

/-- Upper record Orders: p2Q(n) + 1 = p2Q(a) + p2Q(n - a) at every split. -/
theorem upperRecordQ_iff_add (hq : 3 ≤ q) (n : ℕ) :
    UpperRecordQ q n ↔ ∀ a, 1 ≤ a → a < n → p2Q q n + 1 = p2Q q a + p2Q q (n - a) := by
  constructor
  · intro hR a ha1 han
    obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have h1 := hR a ha1 han
    have h2 := hR b (by omega) (by omega)
    have hle := p2Q_add_le_succ hq a b
    by_contra hne
    have hP : p2Q q a + p2Q q b ≤ p2Q q (a + b) := by
      omega
    have h3 := Nat.mul_le_mul_left (a + b) hP
    nlinarith
  · intro hB a ha1 han
    obtain ⟨b, rfl⟩ : ∃ b, n = a + b := ⟨n - a, by omega⟩
    have h1 := hB a ha1 han
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : (p2Q q b - 1) * a < b * p2Q q a := p2Q_sub_one_mul_lt hq (by omega)
    have hB1 := one_le_p2Q q b
    have hP : p2Q q (a + b) = p2Q q a + (p2Q q b - 1) := by
      omega
    rw [hP]
    nlinarith

/-- Lower record Orders are the Orders whose block factor is below every earlier one. -/
theorem lowerRecordQ_iff_blockFactorQ (hq : 3 ≤ q) (n : ℕ) :
    LowerRecordQ q n ↔ ∀ a, 1 ≤ a → a < n → blockFactorQ q n < blockFactorQ q a := by
  rw [lowerRecordQ_iff_add hq]
  constructor
  · intro h a ha1 han
    have hb := blockFactorQ_add_lt_iff hq a (n - a)
    rw [Nat.add_sub_of_le han.le] at hb
    exact hb.mpr (h a ha1 han)
  · intro h a ha1 han
    have hb := blockFactorQ_add_lt_iff hq a (n - a)
    rw [Nat.add_sub_of_le han.le] at hb
    exact hb.mp (h a ha1 han)

/-- Upper record Orders are the Orders whose block factor is above every earlier one. -/
theorem upperRecordQ_iff_blockFactorQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    UpperRecordQ q n ↔ ∀ a, 1 ≤ a → a < n → blockFactorQ q a < blockFactorQ q n := by
  rw [upperRecordQ_iff_add hq]
  constructor
  · intro h a ha1 han
    have hb := blockFactorQ_lt_add_iff hodd hq a (b := n - a) (by omega)
    rw [Nat.add_sub_of_le han.le] at hb
    exact hb.mpr (h a ha1 han)
  · intro h a ha1 han
    have hb := blockFactorQ_lt_add_iff hodd hq a (b := n - a) (by omega)
    rw [Nat.add_sub_of_le han.le] at hb
    exact hb.mp (h a ha1 han)

end AcceleratedCollatz
