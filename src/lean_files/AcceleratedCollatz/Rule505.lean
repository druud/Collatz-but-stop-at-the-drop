-- SPDX-License-Identifier: MIT
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Rule 505 and the closed forms of A282798

Self-contained extract of the AcceleratedCollatz Lean 4 project; depends on
Mathlib only.

OEIS A282798 (Robert Price, 2017) reads the x-axis, from the left edge to the origin, of the
2-dimensional cellular automaton "Rule 505" on the 5-cell von Neumann neighbourhood, started
from a single ON cell, as a binary number. Colin Barker conjectured (2017)

  a(n) = 2^(n+1) - 1 for n even,  a(n) = 2 (2^n - 2) / 3 for n odd.

Both are proved here (`axisVal_even`, `axisVal_odd`), and with them the recurrence
a(n + 4) + 4 a(n) = 5 a(n + 2) (`axisVal_rec`).

The same numbers come from T(x) = x/2 (x even), (3x + 1)/2 (x odd): a(n) + 1 is the
T-preimage of 2^n of the reverse steps, the odd one (2^(n+1) - 1)/3 where there is one (n odd),
else 2^(n+1) (`axisVal_add_one`, `T_tPre`, `odd_preimage_iff`; A52 of the project).

A cell with value c and s ON neighbours (of 4) gets bit 2s + c of 505 (`rule`). Stage 0 is
the single ON cell at the origin (`ca`). The proof (A48 of the project, 4 Nov 2026) is an
invariant at odd stages n (`OddInv`):

* outside the cone, |i| + |j| > n, every cell is ON;
* every even cell (i + j even) is ON, except the origin, which is OFF;
* the odd cells on the axes inside the cone are OFF;
* the odd cells next to the axes, (±1, j) and (j, ±1) with j even, j ≠ 0, are ON.

It holds at stage 1 (`oddInv_one`) and passes from n to n + 2 (`oddInv_add_two`), through
what it gives at the even stage n + 1 between them. The rule and the start are symmetric under
i ↦ -i and the exchange of i and j, and so is every stage (`ca_neg`, `ca_swap`).
-/

namespace Rule505

/-- Rule 505: a cell with value c and s ON neighbours gets bit 2s + c of 505. -/
def rule (c : Bool) (s : ℕ) : Bool := Nat.testBit 505 (2 * s + c.toNat)

/-- The number of ON neighbours of the cell (i, j). -/
def nb (f : ℤ → ℤ → Bool) (i j : ℤ) : ℕ :=
  (f (i + 1) j).toNat + (f (i - 1) j).toNat + (f i (j + 1)).toNat + (f i (j - 1)).toNat

/-- One stage of the automaton. -/
def step (f : ℤ → ℤ → Bool) (i j : ℤ) : Bool := rule (f i j) (nb f i j)

/-- Stage n, from a single ON cell at the origin. -/
def ca : ℕ → ℤ → ℤ → Bool
  | 0 => fun i j => decide (i = 0 ∧ j = 0)
  | n + 1 => step (ca n)

/-- A282798(n): the x-axis at stage n, from the left edge (-n, 0) to the origin, in binary. -/
def axisVal (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (ca n (-(k : ℤ)) 0).toNat * 2 ^ k

/-! ## The rule table -/

theorem rule_four (c : Bool) : rule c 4 = !c := by cases c <;> decide

theorem rule_false_zero : rule false 0 = true := by decide
theorem rule_false_one : rule false 1 = false := by decide
theorem rule_false_three : rule false 3 = true := by decide

theorem rule_true_mid {s : ℕ} (h1 : 1 ≤ s) (h3 : s ≤ 3) : rule true s = true := by
  interval_cases s <;> decide

theorem rule_false_ge_two {s : ℕ} (h2 : 2 ≤ s) (h4 : s ≤ 4) : rule false s = true := by
  interval_cases s <;> decide

/-- The two steps on an even cell whose 4 odd neighbours each flip. -/
theorem rule_flip {s : ℕ} (h : s ≤ 4) : rule (rule true s) (4 - s) = true := by
  interval_cases s <;> decide

theorem toNat_not (b : Bool) : (!b).toNat = 1 - b.toNat := by cases b <;> rfl

theorem toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

/-! ## Symmetry -/

theorem ca_neg (n : ℕ) : ∀ i j, ca n (-i) j = ca n i j := by
  induction n with
  | zero => intro i j; simp [ca]
  | succ n ih =>
    intro i j
    simp only [ca, step, nb]
    rw [show -i + 1 = -(i - 1) by ring, show -i - 1 = -(i + 1) by ring, ih, ih, ih, ih, ih]
    congr 1
    omega

theorem ca_swap (n : ℕ) : ∀ i j, ca n j i = ca n i j := by
  induction n with
  | zero => intro i j; simp [ca, and_comm]
  | succ n ih =>
    intro i j
    simp only [ca, step, nb]
    rw [ih j i, ih (j + 1) i, ih (j - 1) i, ih j (i + 1), ih j (i - 1)]
    congr 1
    omega

theorem ca_neg' (n : ℕ) (i j : ℤ) : ca n i (-j) = ca n i j := by
  rw [ca_swap, ca_neg, ca_swap]

/-! ## The invariant at odd stages -/

/-- What holds at an odd stage n. -/
structure OddInv (n : ℕ) : Prop where
  out : ∀ i j : ℤ, (n < i + j ∨ n < i - j ∨ n < -i + j ∨ n < -i - j) → ca n i j = true
  even : ∀ i j : ℤ, (i + j) % 2 = 0 → ¬(i = 0 ∧ j = 0) → ca n i j = true
  origin : ca n 0 0 = false
  axis : ∀ j : ℤ, j % 2 = 1 → j ≤ n → -j ≤ n → ca n 0 j = false
  near : ∀ j : ℤ, j % 2 = 0 → j ≠ 0 → ca n 1 j = true

section Stage

variable {n : ℕ} (h : OddInv n)
include h

theorem OddInv.axis' {j : ℤ} (h1 : j % 2 = 1) (h2 : j ≤ n) (h3 : -j ≤ n) : ca n j 0 = false := by
  rw [ca_swap]; exact h.axis j h1 h2 h3

theorem OddInv.near_neg {j : ℤ} (h1 : j % 2 = 0) (h2 : j ≠ 0) : ca n (-1) j = true := by
  rw [ca_neg]; exact h.near j h1 h2

/-! ### The even stage n + 1 -/

theorem OddInv.g_out {i j : ℤ} (ho : (n : ℤ) + 1 < i + j ∨ (n : ℤ) + 1 < i - j ∨
    (n : ℤ) + 1 < -i + j ∨ (n : ℤ) + 1 < -i - j) : ca (n + 1) i j = false := by
  change rule _ _ = false
  simp only [nb]
  rw [h.out i j (by omega), h.out (i + 1) j (by omega), h.out (i - 1) j (by omega),
    h.out i (j + 1) (by omega), h.out i (j - 1) (by omega)]
  rfl

/-- An odd cell not next to the origin flips: its 4 even neighbours are ON. -/
theorem OddInv.g_odd {i j : ℤ} (hp : (i + j) % 2 = 1) (h1 : ¬((i = 1 ∨ i = -1) ∧ j = 0))
    (h2 : ¬(i = 0 ∧ (j = 1 ∨ j = -1))) : ca (n + 1) i j = !ca n i j := by
  change rule _ _ = _
  simp only [nb]
  rw [h.even (i + 1) j (by omega) (by omega), h.even (i - 1) j (by omega) (by omega),
    h.even i (j + 1) (by omega) (by omega), h.even i (j - 1) (by omega) (by omega)]
  exact rule_four _

theorem OddInv.g_adj (h1 : 1 ≤ n) : ca (n + 1) 1 0 = true := by
  change rule _ _ = true
  simp only [nb]
  rw [h.axis' (j := 1) (by decide) (by omega) (by omega),
    h.even (1 + 1) 0 (by decide) (by decide), show (1 : ℤ) - 1 = 0 by norm_num, h.origin,
    h.even 1 (0 + 1) (by decide) (by decide), h.even 1 (0 - 1) (by decide) (by decide)]
  exact rule_false_three

theorem OddInv.g_origin (h1 : 1 ≤ n) : ca (n + 1) 0 0 = true := by
  change rule _ _ = true
  simp only [nb, zero_add, zero_sub]
  rw [h.origin, h.axis' (j := 1) (by decide) (by omega) (by omega),
    h.axis' (j := -1) (by decide) (by omega) (by omega),
    h.axis 1 (by decide) (by omega) (by omega), h.axis (-1) (by decide) (by omega) (by omega)]
  exact rule_false_zero

/-- An even cell on the axis, inside the cone of n + 1, is ON: next to it (±1, j) are ON, and
  (0, j ± 1) on the side of the origin is OFF. -/
theorem OddInv.g_axis {j : ℤ} (hp : j % 2 = 0) (h0 : j ≠ 0) (h2 : j ≤ n + 1) (h3 : -j ≤ n + 1) :
    ca (n + 1) 0 j = true := by
  change rule _ _ = true
  simp only [nb, zero_add, zero_sub]
  rw [h.even 0 j (by omega) (by omega), h.near j hp h0, h.near_neg hp h0]
  apply rule_true_mid
  · simp; omega
  · rcases lt_or_gt_of_ne h0 with hj | hj
    · rw [h.axis (j + 1) (by omega) (by omega) (by omega)]
      have := toNat_le_one (ca n 0 (j - 1)); simp; omega
    · rw [h.axis (j - 1) (by omega) (by omega) (by omega)]
      have := toNat_le_one (ca n 0 (j + 1)); simp; omega

/-- An even cell next to the axis, inside the cone of n, is ON: (0, j) is OFF, and (1, j ± 1)
  away from the axis' cell (1, 0) is ON. -/
theorem OddInv.g_near {j : ℤ} (hp : j % 2 = 1) (h2 : j ≤ n) (h3 : -j ≤ n) :
    ca (n + 1) 1 j = true := by
  change rule _ _ = true
  simp only [nb, show (1 : ℤ) - 1 = 0 by norm_num]
  rw [h.even 1 j (by omega) (by omega), h.axis j hp h2 h3]
  apply rule_true_mid
  · by_cases hj : 0 < j
    · rw [h.near (j + 1) (by omega) (by omega)]; simp; omega
    · rw [h.near (j - 1) (by omega) (by omega)]; simp
  · have := toNat_le_one (ca n 2 j)
    have := toNat_le_one (ca n 1 (j + 1))
    have := toNat_le_one (ca n 1 (j - 1))
    simp; omega

/-! ### Stage n + 2 -/

theorem OddInv.g_adj_neg (h1 : 1 ≤ n) : ca (n + 1) (-1) 0 = true := by
  rw [ca_neg]; exact h.g_adj h1

theorem OddInv.g_adj_swap (h1 : 1 ≤ n) : ca (n + 1) 0 1 = true := by
  rw [ca_swap]; exact h.g_adj h1

theorem OddInv.g_adj_swap_neg (h1 : 1 ≤ n) : ca (n + 1) 0 (-1) = true := by
  rw [ca_neg', ca_swap]; exact h.g_adj h1

theorem OddInv.h_out {i j : ℤ} (ho : (n : ℤ) + 2 < i + j ∨ (n : ℤ) + 2 < i - j ∨
    (n : ℤ) + 2 < -i + j ∨ (n : ℤ) + 2 < -i - j) : ca (n + 2) i j = true := by
  change rule _ _ = true
  simp only [nb]
  rw [h.g_out (i := i) (j := j) (by omega), h.g_out (i := i + 1) (j := j) (by omega),
    h.g_out (i := i - 1) (j := j) (by omega), h.g_out (i := i) (j := j + 1) (by omega),
    h.g_out (i := i) (j := j - 1) (by omega)]
  exact rule_false_zero

theorem OddInv.h_origin (h1 : 1 ≤ n) : ca (n + 2) 0 0 = false := by
  change rule _ _ = false
  simp only [nb, zero_add, zero_sub]
  rw [h.g_origin h1, h.g_adj h1, h.g_adj_neg h1, h.g_adj_swap h1, h.g_adj_swap_neg h1]
  rfl

/-- An even cell with no neighbour next to the origin: each of its 4 odd neighbours flips. -/
theorem OddInv.h_even_far {i j : ℤ} (hp : (i + j) % 2 = 0)
    (hf : 2 < i + j ∨ 2 < i - j ∨ 2 < -i + j ∨ 2 < -i - j) : ca (n + 2) i j = true := by
  change rule (ca (n + 1) i j) (nb (ca (n + 1)) i j) = true
  have hc : ca (n + 1) i j = rule true (nb (ca n) i j) := by
    change rule _ _ = _
    rw [h.even i j hp (by omega)]
  rw [hc]
  simp only [nb]
  rw [h.g_odd (i := i + 1) (j := j) (by omega) (by omega) (by omega),
    h.g_odd (i := i - 1) (j := j) (by omega) (by omega) (by omega),
    h.g_odd (i := i) (j := j + 1) (by omega) (by omega) (by omega),
    h.g_odd (i := i) (j := j - 1) (by omega) (by omega) (by omega)]
  simp only [toNat_not]
  have := toNat_le_one (ca n (i + 1) j)
  have := toNat_le_one (ca n (i - 1) j)
  have := toNat_le_one (ca n i (j + 1))
  have := toNat_le_one (ca n i (j - 1))
  have key := rule_flip (s := (ca n (i + 1) j).toNat + (ca n (i - 1) j).toNat +
    (ca n i (j + 1)).toNat + (ca n i (j - 1)).toNat) (by omega)
  convert key using 2
  omega

theorem OddInv.f21 : ca n 2 1 = true := by
  rw [ca_swap]; exact h.near 2 (by decide) (by decide)

theorem OddInv.f2m : ca n 2 (-1) = true := by
  rw [ca_neg']; exact h.f21

theorem OddInv.h_two (h1 : 1 ≤ n) : ca (n + 2) 2 0 = true := by
  have hc : ca (n + 1) 2 0 = true := by
    change rule _ _ = true
    simp only [nb, zero_add, zero_sub, show (2 : ℤ) + 1 = 3 by norm_num,
      show (2 : ℤ) - 1 = 1 by norm_num]
    rw [h.even 2 0 (by decide) (by decide), h.axis' (j := 1) (by decide) (by omega) (by omega),
      h.f21, h.f2m]
    have := toNat_le_one (ca n 3 0)
    apply rule_true_mid <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> omega
  change rule _ _ = true
  simp only [nb, zero_add, zero_sub, show (2 : ℤ) + 1 = 3 by norm_num,
    show (2 : ℤ) - 1 = 1 by norm_num]
  rw [hc, h.g_odd (i := 3) (j := 0) (by decide) (by decide) (by decide), h.g_adj h1,
    h.g_odd (i := 2) (j := 1) (by decide) (by decide) (by decide),
    h.g_odd (i := 2) (j := -1) (by decide) (by decide) (by decide), h.f21, h.f2m, toNat_not]
  have := toNat_le_one (ca n 3 0)
  apply rule_true_mid <;> simp only [Bool.not_true, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem OddInv.h_one_one (h1 : 1 ≤ n) : ca (n + 2) 1 1 = true := by
  have f12 : ca n 1 2 = true := h.near 2 (by decide) (by decide)
  have f01 : ca n 0 1 = false := h.axis 1 (by decide) (by omega) (by omega)
  have f10 : ca n 1 0 = false := h.axis' (j := 1) (by decide) (by omega) (by omega)
  have hc : ca (n + 1) 1 1 = true := by
    change rule _ _ = true
    simp only [nb, show (1 : ℤ) + 1 = 2 by norm_num, sub_self]
    rw [h.even 1 1 (by decide) (by decide), h.f21, f01, f12, f10]
    rfl
  change rule _ _ = true
  simp only [nb, show (1 : ℤ) + 1 = 2 by norm_num, sub_self]
  rw [hc, h.g_odd (i := 2) (j := 1) (by decide) (by decide) (by decide),
    h.g_adj_swap h1, h.g_odd (i := 1) (j := 2) (by decide) (by decide) (by decide),
    h.g_adj h1, h.f21, f12]
  rfl

theorem OddInv.h_even (h1 : 1 ≤ n) {i j : ℤ} (hp : (i + j) % 2 = 0) (hz : ¬(i = 0 ∧ j = 0)) :
    ca (n + 2) i j = true := by
  by_cases hf : 2 < i + j ∨ 2 < i - j ∨ 2 < -i + j ∨ 2 < -i - j
  · exact h.h_even_far hp hf
  have : (i = 2 ∧ j = 0) ∨ (i = -2 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = -2) ∨
      (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = -1) ∨ (i = -1 ∧ j = 1) ∨ (i = -1 ∧ j = -1) := by omega
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.h_two h1
  · rw [ca_neg]; exact h.h_two h1
  · rw [ca_swap]; exact h.h_two h1
  · rw [ca_neg', ca_swap]; exact h.h_two h1
  · exact h.h_one_one h1
  · rw [ca_neg']; exact h.h_one_one h1
  · rw [ca_neg]; exact h.h_one_one h1
  · rw [ca_neg, ca_neg']; exact h.h_one_one h1

theorem OddInv.h_axis (h1 : 1 ≤ n) (hn : n % 2 = 1) {j : ℤ} (hp : j % 2 = 1)
    (h2 : j ≤ n + 2) (h3 : -j ≤ n + 2) : ca (n + 2) 0 j = false := by
  change rule _ _ = false
  simp only [nb, zero_add, zero_sub]
  by_cases hin : j ≤ n ∧ -j ≤ n
  · have hc : ca (n + 1) 0 j = true := by
      by_cases hj1 : j = 1
      · subst hj1; exact h.g_adj_swap h1
      by_cases hj2 : j = -1
      · subst hj2; exact h.g_adj_swap_neg h1
      rw [h.g_odd (by omega) (by omega) (by omega), h.axis j hp hin.1 hin.2]; rfl
    have hu : ca (n + 1) 0 (j + 1) = true := by
      by_cases hz : j + 1 = 0
      · rw [hz]; exact h.g_origin h1
      exact h.g_axis (by omega) hz (by omega) (by omega)
    have hd : ca (n + 1) 0 (j - 1) = true := by
      by_cases hz : j - 1 = 0
      · rw [hz]; exact h.g_origin h1
      exact h.g_axis (by omega) hz (by omega) (by omega)
    have hr : ca (n + 1) 1 j = true := h.g_near hp hin.1 hin.2
    have hl : ca (n + 1) (-1) j = true := by rw [ca_neg]; exact hr
    rw [hc, hr, hl, hu, hd]
    rfl
  · have hc : ca (n + 1) 0 j = false := h.g_out (by omega)
    have hr : ca (n + 1) 1 j = false := h.g_out (by omega)
    have hl : ca (n + 1) (-1) j = false := h.g_out (by omega)
    rcases (show j = n + 2 ∨ j = -(n + 2) by omega) with hj | hj
    · rw [hc, hr, hl, h.g_out (i := 0) (j := j + 1) (by omega),
        h.g_axis (j := j - 1) (by omega) (by omega) (by omega) (by omega)]
      rfl
    · rw [hc, hr, hl, h.g_out (i := 0) (j := j - 1) (by omega),
        h.g_axis (j := j + 1) (by omega) (by omega) (by omega) (by omega)]
      rfl

theorem OddInv.h_near {j : ℤ} (hp : j % 2 = 0) (h0 : j ≠ 0) : ca (n + 2) 1 j = true := by
  by_cases hin : j ≤ n + 1 ∧ -j ≤ n + 1
  swap
  · exact h.h_out (by omega)
  change rule _ _ = true
  simp only [nb, show (1 : ℤ) + 1 = 2 by norm_num, sub_self]
  rw [h.g_odd (i := 1) (j := j) (by omega) (by omega) (by omega), h.near j hp h0,
    h.g_axis hp h0 hin.1 hin.2]
  have := toNat_le_one (ca (n + 1) 2 j)
  have := toNat_le_one (ca (n + 1) 1 (j + 1))
  have := toNat_le_one (ca (n + 1) 1 (j - 1))
  apply rule_false_ge_two
  · by_cases hj : 0 < j
    · rw [h.g_near (j := j - 1) (by omega) (by omega) (by omega)]; simp; omega
    · rw [h.g_near (j := j + 1) (by omega) (by omega) (by omega)]; simp; omega
  · simp; omega

theorem OddInv.add_two (h1 : 1 ≤ n) (hn : n % 2 = 1) : OddInv (n + 2) where
  out i j ho := h.h_out (by push_cast at ho; omega)
  even i j hp hz := h.h_even h1 hp hz
  origin := h.h_origin h1
  axis j hp h2 h3 := h.h_axis h1 hn hp (by push_cast at h2; omega) (by push_cast at h3; omega)
  near j hp h0 := h.h_near hp h0

end Stage

/-! ## Stage 1 and every odd stage -/

theorem ca_one_far {i j : ℤ} (hf : 1 < i + j ∨ 1 < i - j ∨ 1 < -i + j ∨ 1 < -i - j) :
    ca 1 i j = true := by
  change rule (decide (i = 0 ∧ j = 0)) ((decide (i + 1 = 0 ∧ j = 0)).toNat +
    (decide (i - 1 = 0 ∧ j = 0)).toNat + (decide (i = 0 ∧ j + 1 = 0)).toNat +
    (decide (i = 0 ∧ j - 1 = 0)).toNat) = true
  rw [decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_false (by omega),
    decide_eq_false (by omega), decide_eq_false (by omega)]
  rfl

theorem oddInv_one : OddInv 1 where
  out i j ho := ca_one_far (by push_cast at ho; omega)
  even i j hp hz := ca_one_far (by omega)
  origin := by decide
  axis j hp h2 h3 := by
    rcases (show j = 1 ∨ j = -1 by push_cast at h2 h3; omega) with rfl | rfl <;> decide
  near j hp h0 := ca_one_far (by omega)

theorem oddInv_odd (m : ℕ) : OddInv (2 * m + 1) := by
  induction m with
  | zero => exact oddInv_one
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring]
    exact ih.add_two (by omega) (by omega)

/-! ## The x-axis -/

/-- At an odd stage the x-axis reads 0101...0100: ON exactly at the even k ≠ 0. -/
theorem axis_odd (m k : ℕ) (hk : k ≤ 2 * m + 1) :
    ca (2 * m + 1) (-(k : ℤ)) 0 = decide (k % 2 = 0 ∧ k ≠ 0) := by
  have h := oddInv_odd m
  rw [ca_neg]
  by_cases h0 : k = 0
  · subst h0; simpa using h.origin
  by_cases he : k % 2 = 0
  · rw [h.even k 0 (by omega) (by omega)]; simp [he, h0]
  · rw [h.axis' (j := k) (by omega) (by push_cast; omega) (by push_cast; omega)]; simp [he]

/-- At an even stage the x-axis is all ON, from the left edge to the origin. -/
theorem axis_even (m k : ℕ) (hk : k ≤ 2 * m) : ca (2 * m) (-(k : ℤ)) 0 = true := by
  rw [ca_neg]
  rcases m with _ | m
  · have : k = 0 := by omega
    subst this; decide
  have h := oddInv_odd m
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
  by_cases h0 : k = 0
  · subst h0; exact h.g_origin (by omega)
  by_cases h1 : k = 1
  · subst h1; exact h.g_adj (by omega)
  by_cases he : k % 2 = 0
  · rw [ca_swap]; exact h.g_axis (by omega) (by omega) (by push_cast; omega) (by push_cast; omega)
  · rw [h.g_odd (by omega) (by omega) (by omega),
      h.axis' (j := k) (by omega) (by push_cast; omega) (by push_cast; omega)]
    rfl

theorem sum_two_pow (N : ℕ) : ∑ k ∈ Finset.range N, 2 ^ k + 1 = 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem sum_even_pow (m : ℕ) :
    3 * ∑ k ∈ Finset.range (2 * m + 2), (if k % 2 = 0 ∧ k ≠ 0 then 1 else 0) * 2 ^ k + 4 =
      4 ^ (m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2 * (m + 1) + 2 = 2 * m + 2 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have e1 : (2 * m + 2) % 2 = 0 ∧ 2 * m + 2 ≠ 0 := by omega
    have e2 : ¬((2 * m + 2 + 1) % 2 = 0 ∧ 2 * m + 2 + 1 ≠ 0) := by omega
    have e3 : 2 ^ (2 * m + 2) = 4 ^ (m + 1) := by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; norm_num
    rw [ite_eq_left e1, ite_eq_right e2, e3, pow_succ 4 (m + 1)]
    omega

/-- Barker's closed form for even n: a(n) = 2^(n+1) - 1. -/
theorem axisVal_even (m : ℕ) : axisVal (2 * m) = 2 ^ (2 * m + 1) - 1 := by
  have := sum_two_pow (2 * m + 1)
  have hs : axisVal (2 * m) = ∑ k ∈ Finset.range (2 * m + 1), 2 ^ k := by
    unfold axisVal
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [axis_even m k (by simp at hk; omega)]; simp
  omega

/-- For odd n, 3 a(n) + 4 = 2^(n+1). -/
theorem axisVal_odd' (m : ℕ) : 3 * axisVal (2 * m + 1) + 4 = 2 ^ (2 * m + 2) := by
  have hs : axisVal (2 * m + 1) = ∑ k ∈ Finset.range (2 * m + 2),
      (if k % 2 = 0 ∧ k ≠ 0 then 1 else 0) * 2 ^ k := by
    unfold axisVal
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [axis_odd m k (by simp at hk; omega)]
    by_cases hc : k % 2 = 0 ∧ k ≠ 0 <;> simp [hc]
  rw [hs, sum_even_pow, show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]
  norm_num

/-- Barker's closed form for odd n: a(n) = 2 (2^n - 2) / 3. -/
theorem axisVal_odd (m : ℕ) : axisVal (2 * m + 1) = 2 * (2 ^ (2 * m + 1) - 2) / 3 := by
  have h := axisVal_odd' m
  rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring, pow_succ] at h
  omega

/-- A282798(n) = 2^(n+1) - 1 for n even, 2 (2^n - 2) / 3 for n odd. -/
theorem axisVal_eq (n : ℕ) :
    axisVal n = if n % 2 = 0 then 2 ^ (n + 1) - 1 else 2 * (2 ^ n - 2) / 3 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [ite_eq_left (by omega)]; exact axisVal_even m
  · rw [ite_eq_right (by omega)]; exact axisVal_odd m

/-- Barker's recurrence: a(n + 4) + 4 a(n) = 5 a(n + 2). -/
theorem axisVal_rec (n : ℕ) : axisVal (n + 4) + 4 * axisVal n = 5 * axisVal (n + 2) := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [show 2 * m + 4 = 2 * (m + 2) by ring, show 2 * m + 2 = 2 * (m + 1) by ring,
      axisVal_even, axisVal_even, axisVal_even]
    have : 2 ^ (2 * (m + 2) + 1) = 16 * 2 ^ (2 * m + 1) := by ring
    have : 2 ^ (2 * (m + 1) + 1) = 4 * 2 ^ (2 * m + 1) := by ring
    have : 0 < 2 ^ (2 * m + 1) := by positivity
    omega
  · have h0 := axisVal_odd' m
    have h1 := axisVal_odd' (m + 1)
    have h2 := axisVal_odd' (m + 2)
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring] at h1
    rw [show 2 * (m + 2) + 1 = 2 * m + 1 + 4 by ring] at h2
    have : 2 ^ (2 * (m + 1) + 2) = 4 * 2 ^ (2 * m + 2) := by ring
    have : 2 ^ (2 * (m + 2) + 2) = 16 * 2 ^ (2 * m + 2) := by ring
    omega

/-! ## The link to T

A282798(n) + 1 is the T-preimage of 2^n that the reverse steps take: the odd one,
(2^(n+1) - 1)/3, where there is one (n odd), else 2^(n+1) (`axisVal_add_one`). -/

/-- The Collatz map T: x/2 for even x, (3x + 1)/2 for odd x. -/
def T (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- The odd T-preimage of 2^e, (2^(e+1) - 1)/3, where there is one; else 2^(e+1). -/
def tPre (e : ℕ) : ℕ :=
  if (2 ^ (e + 1) - 1) % 3 = 0 then (2 ^ (e + 1) - 1) / 3 else 2 ^ (e + 1)

theorem four_pow_mod (m : ℕ) : 4 ^ m % 3 = 1 := by simp [Nat.pow_mod]

theorem two_pow_even (m : ℕ) : 2 ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num

/-- For even e there is no odd preimage: tPre e = 2^(e+1). -/
theorem tPre_even (m : ℕ) : tPre (2 * m) = 2 ^ (2 * m + 1) := by
  have h4 := four_pow_mod m
  have h : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by rw [pow_succ, two_pow_even]; ring
  unfold tPre
  rw [h, ite_eq_right (by omega)]

/-- For odd e, tPre e is the odd preimage: 3 tPre e + 1 = 2^(e+1). -/
theorem tPre_odd (m : ℕ) : 3 * tPre (2 * m + 1) + 1 = 2 ^ (2 * m + 2) := by
  have h4 := four_pow_mod m
  have h : 2 ^ (2 * m + 2) = 4 * 4 ^ m := by
    rw [show 2 * m + 2 = 2 * (m + 1) by ring, two_pow_even, pow_succ]; ring
  unfold tPre
  rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, h, ite_eq_left (by omega)]
  omega

/-- tPre e is a T-preimage of 2^e. -/
theorem T_tPre (e : ℕ) : T (tPre e) = 2 ^ e := by
  rcases Nat.even_or_odd' e with ⟨m, rfl | rfl⟩
  · have h : 2 ^ (2 * m + 1) = 2 * 2 ^ (2 * m) := by ring
    rw [tPre_even, T, h, ite_eq_left (by omega)]
    omega
  · have h := tPre_odd m
    have h2 : 2 ^ (2 * m + 2) = 2 * 2 ^ (2 * m + 1) := by ring
    unfold T
    rw [ite_eq_right (by omega)]
    omega

/-- An odd x has T x = 2^e exactly when e is odd and x = tPre e. -/
theorem odd_preimage_iff {e x : ℕ} (hx : x % 2 = 1) : T x = 2 ^ e ↔ e % 2 = 1 ∧ x = tPre e := by
  constructor
  · intro hT
    unfold T at hT
    rw [ite_eq_right (by omega)] at hT
    rcases Nat.even_or_odd' e with ⟨m, rfl | rfl⟩
    · have h4 := four_pow_mod m
      rw [two_pow_even] at hT
      omega
    · have h := tPre_odd m
      have h2 : 2 ^ (2 * m + 2) = 2 * 2 ^ (2 * m + 1) := by ring
      omega
  · rintro ⟨-, rfl⟩
    exact T_tPre e

/-- A282798(n) + 1 = tPre n, the T-preimage of 2^n of the reverse steps. -/
theorem axisVal_add_one (n : ℕ) : axisVal n + 1 = tPre n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [axisVal_even, tPre_even]
    have : 0 < 2 ^ (2 * m + 1) := by positivity
    omega
  · have h := axisVal_odd' m
    have h' := tPre_odd m
    omega

end Rule505
