-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBlockRecord

/-!
  The three gaps of the floors (the floors paper, Theorem 3.1), in exact rationals.

  The floor of Order n is θ(n) = 3^n / 2^p2(n) = `blockFactor n`, in [1/2, 1), above 1/2 for
  n ≥ 1 (`half_le_blockFactor`, `half_lt_blockFactor`, `blockFactor_lt_one`). The product rule:
  θ(x + y) is θ(x) θ(y) or 2 θ(x) θ(y) (`blockFactor_add`). On the octave as a circle, the end
  ratio from a floor x up to a floor y is `fwd x y` = y/x when x < y, else 2y/x. It depends on the
  Orders only by their difference: the floor k Orders on is 2 θ(k) up (`fwd_add`), the floor k
  Orders back is 1/θ(k) up (`fwd_add'`).

  Let N ≥ 1, θ(a) the lowest and θ(b) the highest of θ(1), ..., θ(N). Then a + b ≥ N + 1
  (`add_ge_of_extremes`), and for 0 ≤ m ≤ N the next floor above θ(m) among θ(0), ..., θ(N)
  (the least end ratio from θ(m)) is
  * θ(m + a), at the end ratio 2θ(a), for m ≤ N - a (`gap_up`);
  * θ(m - b), at 1/θ(b), for m ≥ b (`gap_down`);
  * θ(m + a - b), at 2θ(a)/θ(b), for N - a < m < b (`gap_mid`).
  The three ranges of m have N - a + 1, N - b + 1 and a + b - N - 1 members.
  The proof uses the product rule and the two extremes only (the argument of Surányi 1958, read
  on the floors).
-/

namespace AcceleratedCollatz

theorem blockFactor_pos (n : ℕ) : 0 < blockFactor n := by
  rw [blockFactor_eq]; exact div_pos (pow_pos (by norm_num) n) (pow_pos (by norm_num) _)

theorem one_le_p2_of (n : ℕ) : 1 ≤ p2_of n := by unfold p2_of; omega

theorem blockFactor_lt_one (n : ℕ) : blockFactor n < 1 := by
  rw [blockFactor_eq, div_lt_iff₀ (pow_pos (by norm_num) _), one_mul]
  exact_mod_cast p2_of_spec n

theorem half_le_blockFactor (n : ℕ) : 1 / 2 ≤ blockFactor n := by
  rw [blockFactor_eq, le_div_iff₀ (by positivity)]
  have h := p2_of_spec_lower n
  have hp : p2_of n = p2_of n - 1 + 1 := by have := one_le_p2_of n; omega
  have h' : ((2 : ℚ) ^ (p2_of n - 1)) ≤ 3 ^ n := by exact_mod_cast h
  rw [hp, pow_succ]
  linarith

theorem half_lt_blockFactor {n : ℕ} (hn : 1 ≤ n) : 1 / 2 < blockFactor n := by
  rcases (half_le_blockFactor n).lt_or_eq with h | h
  · exact h
  · exfalso
    have hp : p2_of n = p2_of n - 1 + 1 := by have := one_le_p2_of n; omega
    have h2 : (3 : ℚ) ^ n * 2 = 2 ^ p2_of n := by
      rw [blockFactor_eq] at h
      field_simp at h
      linarith
    rw [hp, pow_succ] at h2
    have h3 : (3 : ℕ) ^ n = 2 ^ (p2_of n - 1) := by
      have : (3 : ℚ) ^ n = 2 ^ (p2_of n - 1) := by linarith
      exact_mod_cast this
    have hl : 1 ≤ p2_of n - 1 := by
      have h3n : 3 ≤ 3 ^ n := Nat.le_self_pow (by omega) 3
      have hs := p2_of_spec n
      by_contra hc
      have : 2 ^ p2_of n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hev : 2 ∣ 3 ^ n := by
      rw [h3]; exact dvd_pow_self 2 (by omega)
    have hodd : (3 ^ n) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
    omega

/-- p2(x + y) is p2(x) + p2(y) or one less. -/
theorem p2_of_add (x y : ℕ) :
    p2_of (x + y) = p2_of x + p2_of y ∨ p2_of (x + y) + 1 = p2_of x + p2_of y := by
  have hx := p2_of_spec x
  have hy := p2_of_spec y
  have hxl := p2_of_spec_lower x
  have hyl := p2_of_spec_lower y
  have hs := p2_of_spec (x + y)
  have hsl := p2_of_spec_lower (x + y)
  have h1x := one_le_p2_of x
  have h1y := one_le_p2_of y
  have h1s := one_le_p2_of (x + y)
  have up : 3 ^ (x + y) < 2 ^ (p2_of x + p2_of y) := by
    rw [pow_add, pow_add]; exact Nat.mul_lt_mul'' hx hy
  have lo : 2 ^ (p2_of x - 1 + (p2_of y - 1)) ≤ 3 ^ (x + y) := by
    rw [pow_add, pow_add]; exact Nat.mul_le_mul hxl hyl
  have a1 : p2_of (x + y) - 1 < p2_of x + p2_of y :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt hsl up)
  have a2 : p2_of x - 1 + (p2_of y - 1) < p2_of (x + y) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt lo hs)
  have a3 : p2_of (x + y) ≤ p2_of x + p2_of y := by
    by_contra hc
    have : p2_of x + p2_of y ≤ p2_of (x + y) - 1 := by omega
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
    omega
  omega

/-- The product rule: θ(x + y) is θ(x) θ(y) or 2 θ(x) θ(y). -/
theorem blockFactor_add (x y : ℕ) :
    blockFactor (x + y) = blockFactor x * blockFactor y ∨
      blockFactor (x + y) = 2 * blockFactor x * blockFactor y := by
  simp only [blockFactor_eq]
  rcases p2_of_add x y with h | h
  · left; rw [h, pow_add, pow_add]; field_simp
  · right
    have hq : (2 : ℚ) ^ p2_of (x + y) = 2 ^ p2_of x * 2 ^ p2_of y / 2 := by
      rw [← pow_add, ← h, pow_succ]; ring
    rw [hq, pow_add]; field_simp

/-- The end ratio on the octave circle from the floor x up to the floor y. -/
def fwd (x y : ℚ) : ℚ := if x < y then y / x else 2 * y / x

/-- The floor k Orders on lies 2θ(k) up. -/
theorem fwd_add (m : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    fwd (blockFactor m) (blockFactor (m + k)) = 2 * blockFactor k := by
  have hm := blockFactor_pos m
  have hk1 := blockFactor_lt_one k
  have hk2 := half_lt_blockFactor hk
  unfold fwd
  rcases blockFactor_add m k with h | h <;> rw [h] <;> split_ifs <;>
    first | (exfalso; nlinarith) | field_simp

/-- The floor k Orders back lies 1/θ(k) up. -/
theorem fwd_add' (j : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    fwd (blockFactor (j + k)) (blockFactor j) = 1 / blockFactor k := by
  have hj := blockFactor_pos j
  have hk0 := blockFactor_pos k
  have hk1 := blockFactor_lt_one k
  have hk2 := half_lt_blockFactor hk
  unfold fwd
  rcases blockFactor_add j k with h | h <;> rw [h] <;> split_ifs <;>
    first | (exfalso; nlinarith) | field_simp

section Gaps

variable {N a b : ℕ} (ha1 : 1 ≤ a) (haN : a ≤ N) (hb1 : 1 ≤ b) (hbN : b ≤ N)
  (hmin : ∀ k, 1 ≤ k → k ≤ N → blockFactor a ≤ blockFactor k)
  (hmax : ∀ k, 1 ≤ k → k ≤ N → blockFactor k ≤ blockFactor b)
include ha1 haN hb1 hbN hmin hmax

omit haN hbN in
/-- The lowest and highest floor Orders up to N add up to more than N. -/
theorem add_ge_of_extremes : N + 1 ≤ a + b := by
  by_contra hc
  have hab : a + b ≤ N := by omega
  have ha := blockFactor_pos a
  have hb1' := blockFactor_lt_one b
  have ha2 := half_lt_blockFactor ha1
  rcases blockFactor_add a b with h | h
  · have := hmin (a + b) (by omega) hab; rw [h] at this; nlinarith [blockFactor_pos b]
  · have := hmax (a + b) (by omega) hab; rw [h] at this; nlinarith [blockFactor_pos b]

omit haN hb1 hbN hmax in
/-- For m ≤ N - a the next floor above θ(m) is θ(m + a), at the end ratio 2θ(a). -/
theorem gap_up {m : ℕ} (hm : m + a ≤ N) :
    fwd (blockFactor m) (blockFactor (m + a)) = 2 * blockFactor a ∧
      ∀ j, j ≤ N → j ≠ m → 2 * blockFactor a ≤ fwd (blockFactor m) (blockFactor j) := by
  refine ⟨fwd_add m ha1, fun j hj hjm => ?_⟩
  rcases Nat.lt_or_gt_of_ne hjm with hlt | hgt
  · obtain ⟨k, rfl⟩ : ∃ k, m = j + k := ⟨m - j, by omega⟩
    have hk : 1 ≤ k := by omega
    rw [fwd_add' j hk]
    have hk0 := blockFactor_pos k
    have ha0 := blockFactor_pos a
    rcases blockFactor_add a k with h | h
    · have := hmin (a + k) (by omega) (by omega)
      rw [h] at this; nlinarith [blockFactor_lt_one k]
    · have := blockFactor_lt_one (a + k)
      rw [h] at this
      rw [le_div_iff₀ hk0]; linarith
  · obtain ⟨k, rfl⟩ : ∃ k, j = m + k := ⟨j - m, by omega⟩
    have hk : 1 ≤ k := by omega
    rw [fwd_add m hk]
    linarith [hmin k hk (by omega)]

omit ha1 haN hbN hmin in
/-- For m = i + b ≤ N the next floor above θ(m) is θ(i) = θ(m - b), at the end ratio 1/θ(b). -/
theorem gap_down {i : ℕ} (hi : i + b ≤ N) :
    fwd (blockFactor (i + b)) (blockFactor i) = 1 / blockFactor b ∧
      ∀ j, j ≤ N → j ≠ i + b → 1 / blockFactor b ≤ fwd (blockFactor (i + b)) (blockFactor j) := by
  refine ⟨fwd_add' i hb1, fun j hj hjm => ?_⟩
  rcases Nat.lt_or_gt_of_ne hjm with hlt | hgt
  · obtain ⟨k, hk'⟩ : ∃ k, i + b = j + k := ⟨i + b - j, by omega⟩
    have hk : 1 ≤ k := by omega
    rw [hk', fwd_add' j hk]
    rw [div_le_div_iff₀ (blockFactor_pos b) (blockFactor_pos k)]
    linarith [hmax k hk (by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k, j = i + b + k := ⟨j - (i + b), by omega⟩
    have hk : 1 ≤ k := by omega
    rw [fwd_add (i + b) hk]
    have hb0 := blockFactor_pos b
    have hk2 := half_lt_blockFactor hk
    rw [div_le_iff₀ hb0]
    rcases blockFactor_add b k with h | h
    · have := half_le_blockFactor (b + k); rw [h] at this; linarith
    · have := hmax (b + k) (by omega) (by omega); rw [h] at this; nlinarith

/-- For N - a < m < b the next floor above θ(m) is θ(m + a - b), at the end ratio 2θ(a)/θ(b). -/
theorem gap_mid {m : ℕ} (h1 : N < m + a) (h2 : m < b) :
    m + a - b ≤ N ∧
    fwd (blockFactor m) (blockFactor (m + a - b)) = 2 * blockFactor a / blockFactor b ∧
      ∀ j, j ≤ N → j ≠ m →
        2 * blockFactor a / blockFactor b ≤ fwd (blockFactor m) (blockFactor j) := by
  have ha0 := blockFactor_pos a
  have hb0 := blockFactor_pos b
  have ha2 := half_lt_blockFactor ha1
  have hb2 := half_lt_blockFactor hb1
  refine ⟨by omega, ?_, fun j hj hjm => ?_⟩
  · rcases lt_trichotomy b a with hba | hab | hab
    · obtain ⟨d, hd⟩ : ∃ d, a = d + b := ⟨a - b, by omega⟩
      have hd1 : 1 ≤ d := by omega
      have hs : m + a - b = m + d := by omega
      rw [hs, fwd_add m hd1]
      have hd0 := blockFactor_pos d
      rcases blockFactor_add d b with h | h
      · rw [← hd] at h; rw [h]; field_simp
      · exfalso
        have := hmin d hd1 (by omega)
        rw [← hd] at h; rw [h] at this; nlinarith
    · exfalso
      subst hab
      have hN2 : 2 ≤ N := by omega
      have e1 : blockFactor 1 = 3 / 4 := by
        have : Nat.log 2 3 = 1 := by rw [Nat.log_eq_iff (by norm_num)]; norm_num
        rw [blockFactor_eq]; norm_num [p2_of, this]
      have e2 : blockFactor 2 = 9 / 16 := by
        rw [blockFactor_eq]
        have : Nat.log 2 9 = 3 := by
          rw [Nat.log_eq_iff (by norm_num)]; norm_num
        norm_num [p2_of, this]
      have := hmin 2 (by norm_num) hN2
      have := hmax 1 le_rfl (by omega)
      linarith
    · obtain ⟨d, hd⟩ : ∃ d, b = d + a := ⟨b - a, by omega⟩
      have hd1 : 1 ≤ d := by omega
      obtain ⟨s, hs⟩ : ∃ s, m + a - b = s := ⟨_, rfl⟩
      have hm' : m = s + d := by omega
      rw [hs, hm', fwd_add' s hd1]
      have hd0 := blockFactor_pos d
      rcases blockFactor_add d a with h | h
      · exfalso
        have := hmax d hd1 (by omega)
        rw [← hd] at h; rw [h] at this; nlinarith [blockFactor_lt_one a]
      · rw [← hd] at h; rw [h]; field_simp
  · rcases Nat.lt_or_gt_of_ne hjm with hlt | hgt
    · obtain ⟨k, rfl⟩ : ∃ k, m = j + k := ⟨m - j, by omega⟩
      have hk : 1 ≤ k := by omega
      rw [fwd_add' j hk]
      have hk0 := blockFactor_pos k
      rw [div_le_div_iff₀ hb0 hk0, one_mul]
      obtain ⟨e, he⟩ : ∃ e, b = k + e := ⟨b - k, by omega⟩
      have he1 : 1 ≤ e := by omega
      rcases blockFactor_add k e with h | h
      · exfalso
        have := hmax k hk (by omega)
        rw [← he] at h; rw [h] at this; nlinarith [blockFactor_lt_one e, blockFactor_pos e]
      · rw [← he] at h; rw [h]
        have := hmin e he1 (by omega)
        nlinarith
    · obtain ⟨k, rfl⟩ : ∃ k, j = m + k := ⟨j - m, by omega⟩
      have hk : 1 ≤ k := by omega
      rw [fwd_add m hk]
      have hk0 := blockFactor_pos k
      rw [div_le_iff₀ hb0]
      obtain ⟨e, he⟩ : ∃ e, a = k + e := ⟨a - k, by omega⟩
      have he1 : 1 ≤ e := by omega
      rcases blockFactor_add k e with h | h
      · rw [← he] at h; rw [h]
        have := hmax e he1 (by omega)
        nlinarith
      · exfalso
        have := hmin k hk (by omega)
        have he2 := half_lt_blockFactor he1
        rw [← he] at h; rw [h] at this; nlinarith

end Gaps

/-- Distinct Orders have distinct floors. -/
theorem blockFactor_inj {j k : ℕ} (h : blockFactor j = blockFactor k) : j = k := by
  rw [blockFactor_eq, blockFactor_eq, div_eq_div_iff (by positivity) (by positivity)] at h
  have hN : 3 ^ j * 2 ^ p2_of k = 3 ^ k * 2 ^ p2_of j := by exact_mod_cast h
  have d1 : 3 ^ j ∣ 3 ^ k := by
    have : 3 ^ j ∣ 3 ^ k * 2 ^ p2_of j := ⟨2 ^ p2_of k, by rw [← hN]⟩
    exact (Nat.Coprime.pow _ _ (by decide : Nat.Coprime 3 2)).dvd_of_dvd_mul_right this
  have d2 : 3 ^ k ∣ 3 ^ j := by
    have : 3 ^ k ∣ 3 ^ j * 2 ^ p2_of k := ⟨2 ^ p2_of j, by rw [hN]⟩
    exact (Nat.Coprime.pow _ _ (by decide : Nat.Coprime 3 2)).dvd_of_dvd_mul_right this
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp d1
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp d2
  omega

/-- One step on: if θ(a), θ(b) are the lowest and highest of θ(1), ..., θ(n - 1) and
    n < a + b, then θ(n) lies between them. -/
theorem between_of_lt_add {n a b : ℕ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (han : a < n) (hbn : b < n)
    (hn : n < a + b)
    (hmin : ∀ k, 1 ≤ k → k < n → blockFactor a ≤ blockFactor k)
    (hmax : ∀ k, 1 ≤ k → k < n → blockFactor k ≤ blockFactor b) :
    blockFactor a ≤ blockFactor n ∧ blockFactor n ≤ blockFactor b := by
  have ha0 := blockFactor_pos a
  have hb0 := blockFactor_pos b
  have ha2 := half_lt_blockFactor ha1
  have hb2 := half_lt_blockFactor hb1
  obtain ⟨u, hu⟩ : ∃ u, n = u + a := ⟨n - a, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, n = v + b := ⟨n - b, by omega⟩
  have hu1 : 1 ≤ u := by omega
  have hv1 : 1 ≤ v := by omega
  have hu0 := blockFactor_pos u
  have hv0 := blockFactor_pos v
  have hu2 := half_lt_blockFactor hu1
  have hv2 := half_lt_blockFactor hv1
  have hminu := hmin u hu1 (by omega)
  have hmaxu := hmax u hu1 (by omega)
  have hminv := hmin v hv1 (by omega)
  have hmaxv := hmax v hv1 (by omega)
  have hab := hmin b hb1 hbn
  have hU := blockFactor_add u a
  have hV := blockFactor_add v b
  rw [← hu] at hU
  rw [← hv] at hV
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    rcases hU with h | h
    · rcases hV with g | g
      · have h1 : blockFactor u = blockFactor b := by
          apply le_antisymm hmaxu
          have : blockFactor a * blockFactor b ≤ blockFactor u * blockFactor a := by
            rw [← h, g]; nlinarith
          nlinarith
        have := blockFactor_inj h1
        omega
      · rw [g] at hlt; nlinarith
    · rw [h] at hlt; nlinarith
  · by_contra hlt
    rw [not_le] at hlt
    rcases hV with g | g
    · rw [g] at hlt; nlinarith [blockFactor_lt_one v]
    · rcases hU with h | h
      · rw [h] at hlt; nlinarith [blockFactor_lt_one u]
      · have h1 : blockFactor v = blockFactor a := by
          apply le_antisymm _ hminv
          have : 2 * blockFactor v * blockFactor b ≤ 2 * blockFactor a * blockFactor b := by
            rw [← g, h]; nlinarith
          nlinarith
        have := blockFactor_inj h1
        omega

section Next

variable {N a b : ℕ} (ha1 : 1 ≤ a) (haN : a ≤ N) (hb1 : 1 ≤ b) (hbN : b ≤ N)
  (hmin : ∀ k, 1 ≤ k → k ≤ N → blockFactor a ≤ blockFactor k)
  (hmax : ∀ k, 1 ≤ k → k ≤ N → blockFactor k ≤ blockFactor b)
include ha1 haN hb1 hbN hmin hmax

/-- θ(a) and θ(b) stay the lowest and highest floors up to Order a + b - 1. -/
theorem extremes_until {n : ℕ} (hn1 : 1 ≤ n) (hn : n < a + b) :
    blockFactor a ≤ blockFactor n ∧ blockFactor n ≤ blockFactor b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hnN : n ≤ N
    · exact ⟨hmin n hn1 hnN, hmax n hn1 hnN⟩
    · exact between_of_lt_add ha1 hb1 (by omega) (by omega) hn
        (fun k hk1 hk => (ih k hk hk1 (by omega)).1) (fun k hk1 hk => (ih k hk hk1 (by omega)).2)

/-- a + b is the next record Order after N: no Order from N + 1 to a + b - 1 is a lower or
    an upper record Order, and a + b is one of the two. -/
theorem next_record :
    (∀ n, N < n → n < a + b → ¬ LowerRecord n ∧ ¬ UpperRecord n) ∧
      (LowerRecord (a + b) ∨ UpperRecord (a + b)) := by
  constructor
  · intro n hNn hn
    have hn1 : 1 ≤ n := by omega
    obtain ⟨h1, h2⟩ := extremes_until ha1 haN hb1 hbN hmin hmax hn1 hn
    rw [lowerRecord_iff_blockFactor, upperRecord_iff_blockFactor]
    constructor
    · intro hL; have := hL a ha1 (by omega); linarith
    · intro hU; have := hU b hb1 (by omega); linarith
  · have ha0 := blockFactor_pos a
    have hb2 := half_lt_blockFactor hb1
    have ha2 := half_lt_blockFactor ha1
    rw [lowerRecord_iff_blockFactor, upperRecord_iff_blockFactor]
    rcases blockFactor_add a b with h | h
    · left
      intro k hk1 hk
      have := (extremes_until ha1 haN hb1 hbN hmin hmax hk1 hk).1
      rw [h]; nlinarith [blockFactor_lt_one b]
    · right
      intro k hk1 hk
      have := (extremes_until ha1 haN hb1 hbN hmin hmax hk1 hk).2
      rw [h]; nlinarith [blockFactor_pos b]

end Next

end AcceleratedCollatz
