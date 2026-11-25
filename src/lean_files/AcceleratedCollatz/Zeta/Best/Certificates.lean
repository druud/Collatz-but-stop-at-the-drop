-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.Zeta.Best.Window
import AcceleratedCollatz.Zeta.Best.CertData
import Mathlib.Data.Nat.Log

/-!
  The certificate rows (paper, Remark 6.7; `data/best_cert_378.txt`). A row (n, c, d, W) says:
  the word of the first L = p2(n) steps of c is a word of Order n, c is the smallest member of
  its class that drops, d = T^L(c) < c, and every member x of a class of Order n with a higher
  ratio than d/c is below W (Theorem B with the ratio d/c). `cert_rows` proves this for every row
  of `certRows` (Orders 1..378), by a check the kernel runs (`decide +kernel`): no
  `native_decide`, so no trust in the compiler.

  What the rows do not say: that no start below W has a higher ratio. That is the search
  (`scripts/boo_scan.cpp`, `scripts/boo.py`), which is not checked in Lean.
-/

namespace AcceleratedCollatz.Best

/-- One pass over the first l steps of c: (T^l(c), 3^(ones so far), 2^m < 3^(ones of the first
    m steps) for every 1 ≤ m ≤ l). -/
def scan (c : ℕ) : ℕ → ℕ × ℕ × Bool
  | 0 => (c, 1, true)
  | l + 1 =>
    (tStep (scan c l).1,
     if (scan c l).1 % 2 = 1 then 3 * (scan c l).2.1 else (scan c l).2.1,
     (scan c l).2.2 &&
       decide (2 ^ (l + 1) < if (scan c l).1 % 2 = 1 then 3 * (scan c l).2.1 else (scan c l).2.1))

theorem tBits_succ_last (c l : ℕ) :
    tBits c (l + 1) = tBits c l ++ [decide (tStep^[l] c % 2 = 1)] := by
  rw [tBits_add' c l 1]
  rfl

theorem scan_spec (c l : ℕ) :
    (scan c l).1 = tStep^[l] c ∧ (scan c l).2.1 = 3 ^ order (tBits c l) ∧
      ((scan c l).2.2 = true → ∀ m, 1 ≤ m → m ≤ l → 2 ^ m < 3 ^ order (tBits c m)) := by
  induction l with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    intro _ m h1 h2
    omega
  | succ l ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hP : (if (scan c l).1 % 2 = 1 then 3 * (scan c l).2.1 else (scan c l).2.1) =
        3 ^ order (tBits c (l + 1)) := by
      rw [tBits_succ_last, order_append, h1, h2]
      by_cases h : tStep^[l] c % 2 = 1
      · simp [h, order, pow_succ, mul_comm]
      · simp [h, order]
    refine ⟨?_, hP, ?_⟩
    · change tStep (scan c l).1 = _
      rw [h1, Function.iterate_succ_apply']
    · intro hok m hm1 hml
      have hok' :
          ((scan c l).2.2 && decide (2 ^ (l + 1) < 3 ^ order (tBits c (l + 1)))) = true := by
        rw [← hP]
        exact hok
      rw [Bool.and_eq_true, decide_eq_true_eq] at hok'
      rcases Nat.lt_or_ge m (l + 1) with h | h
      · exact h3 hok'.1 m hm1 (by omega)
      · have hm : m = l + 1 := by omega
        subst hm
        exact hok'.2

/-- R(n), with the kernel's own base 2 logarithm. -/
def wallC : ℕ → ℕ
  | 0 => 0
  | o + 1 => 3 * wallC o + 2 ^ Nat.log2 (3 ^ o)

theorem wallC_eq (n : ℕ) : wallC n = rhoMax n := by
  induction n with
  | zero => rfl
  | succ o ih =>
    rw [wallC, ih, rhoMax_succ, Nat.log2_eq_log_two]
    simp [p2_of]

/-- The word length of Order n, with the kernel's own base 2 logarithm. -/
def wordLen (n : ℕ) : ℕ := Nat.log2 (3 ^ n) + 1

/-- What the kernel checks for a row. The last line: c is below 2^L, or the row is that of
    Order 1, whose class holds 1, which does not fall below itself. -/
def RowOk (n c d W : ℕ) : Prop :=
  (scan c (wordLen n - 1)).2.2 = true ∧ (scan c (wordLen n)).2.1 = 3 ^ n ∧
    3 ^ n < 2 ^ wordLen n ∧ (scan c (wordLen n)).1 = d ∧ 0 < c ∧ d < c ∧
    3 ^ n * c < 2 ^ wordLen n * d ∧
    wallC n * c ≤ W * (2 ^ wordLen n * d - 3 ^ n * c) ∧
    (c ≤ 2 ^ wordLen n ∨ (n = 1 ∧ c = 5))

instance (n c d W : ℕ) : Decidable (RowOk n c d W) := by
  unfold RowOk
  infer_instance

/-- What a certificate row says. -/
structure Cert (n c d W : ℕ) : Prop where
  /-- The word of c's first p2(n) steps is admissible. -/
  adm : Admissible (tBits c (p2_of n))
  /-- It has Order n. -/
  order_eq : order (tBits c (p2_of n)) = n
  /-- d is the drop value of c. -/
  drop : tStep^[p2_of n] c = d
  /-- c drops. -/
  drops : d < c
  /-- No smaller member of the class of c drops. -/
  least : ∀ x, 0 < x → x < c → tBits x (p2_of n) = tBits c (p2_of n) → x ≤ tStep^[p2_of n] x
  /-- Theorem B with the ratio d/c: a member of a class of Order n with a higher ratio is
      below W. -/
  window : ∀ s : List Bool, Admissible s → order s = n → ∀ x, tBits x s.length = s →
    d * x < c * tStep^[s.length] x → x < W

theorem order_one_least : ∀ x < 5, 0 < x → tBits x 2 = tBits 5 2 → x ≤ tStep^[2] x := by
  decide

theorem cert_of_rowOk {n c d W : ℕ} (h : RowOk n c d W) : Cert n c d W := by
  obtain ⟨hok, hP, hlt, hd, hc0, hdc, hpos, hW, hle⟩ := h
  obtain ⟨-, -, h3⟩ := scan_spec c (wordLen n - 1)
  obtain ⟨h1, h2, -⟩ := scan_spec c (wordLen n)
  have hord : order (tBits c (wordLen n)) = n :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ _ = 3 ^ n by rw [← h2, hP])
  have hA : Admissible (tBits c (wordLen n)) := by
    rw [admissible_iff_pow, length_tBits', hord]
    refine ⟨?_, hlt⟩
    intro m hm h1m
    rw [tBits_take' c (wordLen n) m hm.le]
    exact h3 hok m h1m (by omega)
  have hL : wordLen n = p2_of n := by
    have := admissible_length' _ hA
    rw [length_tBits', hord] at this
    exact this
  have hdrop : tStep^[wordLen n] c = d := by rw [← h1, hd]
  have hsub : ((2 ^ wordLen n * d - 3 ^ n * c : ℕ) : ℤ) = 2 ^ wordLen n * d - 3 ^ n * c := by
    rw [Nat.cast_sub hpos.le]
    push_cast
    ring
  have hpos' : (0 : ℤ) < 2 ^ wordLen n * d - 3 ^ n * c := by
    have : ((3 ^ n * c : ℕ) : ℤ) < ((2 ^ wordLen n * d : ℕ) : ℤ) := by exact_mod_cast hpos
    push_cast at this
    linarith
  rw [hL] at hA hord hdrop
  refine ⟨hA, hord, hdrop, hdc, ?_, ?_⟩
  · intro x hx0 hxc hx
    rcases hle with hle | ⟨rfl, rfl⟩
    · exfalso
      rw [hL] at hle
      have := eq_of_tBits_eq_pos x c (p2_of n) hx0 hc0 (hxc.le.trans hle) hle hx
      omega
    · have h2' : p2_of 1 = 2 := by rw [← hL]; decide
      rw [h2'] at hx ⊢
      exact order_one_least x hxc hx0 hx
  · intro s hs ho x hx hab
    have hw := window hs hx hab
    have hlen : s.length = wordLen n := by rw [admissible_length' s hs, ho, hL]
    rw [hlen, ho, ← wallC_eq] at hw
    have hW' : (wallC n : ℤ) * c ≤ W * (2 ^ wordLen n * d - 3 ^ n * c) := by
      rw [← hsub]
      exact_mod_cast hW
    have hlt' : (x : ℤ) * (2 ^ wordLen n * d - 3 ^ n * c) < W * (2 ^ wordLen n * d - 3 ^ n * c) :=
      lt_of_lt_of_le hw hW'
    exact_mod_cast lt_of_mul_lt_mul_right hlt' hpos'.le

/-- Every row of the certificate file passes the check; the kernel evaluates it. -/
theorem certRows_ok : ∀ r ∈ certRows, RowOk r.1 r.2.1 r.2.2.1 r.2.2.2 := by
  decide +kernel

/-- Every row of the certificate file (Orders 1..378) is a certificate. -/
theorem cert_rows : ∀ r ∈ certRows, Cert r.1 r.2.1 r.2.2.1 r.2.2.2 :=
  fun r hr => cert_of_rowOk (certRows_ok r hr)

end AcceleratedCollatz.Best
