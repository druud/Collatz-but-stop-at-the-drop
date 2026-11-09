-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TGapRatio
import AcceleratedCollatz.TWidthBound
import AcceleratedCollatz.TSieve
import AcceleratedCollatz.TA399760

/-!
  OEIS A398772, the record lows of the gap ratio g(x) = (x - y)/x at the drop (A93, 9 Nov 2026).

  * The factored form: for x with admissible T-parity word s (k = order s, L = |s|) that
    drops at L, g(x) = (1 - 3^k/2^L) (1 - p/x) with p = rho s / (2^L - 3^k), fixed by s
    (`gap_ratio_eq`). So of two starts with the same word the smaller has the smaller g
    (`gap_mul_le_of_lt`; strict when k > 0: `gap_mul_lt_of_lt` in `TGapRatio`), and each
    record is the least start of its word.
  * The sieve of `OEIS/a398772.gp` (`prows`): after the scan of 2..2^s, only the residues
    m mod 2^s whose coefficient 3^k/2^j stays above 1 for j = 1..s are scanned. A skipped
    x = o + m (o >= 2^s) has an admissible prefix tBits x j, j <= s, the one of m
    (`admissible_tBits_of_modEq`). Then x first drops at j, and some x' with 1 < x' <= 2^s
    and the same word drops at j with g(x') <= g(x): x is no record (`sieve_skip`). It needs
    ClassDrops at the Order of that word (the class id drops), which holds unconditionally up
    to Order 10 (`classDropsAt_le_10`, from the x <= 31), so for s <= 16 the sieve is sound
    with no hypothesis (`sieve_skip_16`; prows's default s is 16).
-/

namespace AcceleratedCollatz

/-- g(x) = (1 - 3^k/2^L) (1 - p/x), p = rho s / (2^L - 3^k), for x with the admissible word s
  that does not rise at L. -/
theorem gap_ratio_eq (s : List Bool) (x : ℕ) (hA : Admissible s) (hs : tBits x s.length = s)
    (hx : 0 < x) (hy : tStep^[s.length] x ≤ x) :
    ((x : ℚ) - (tStep^[s.length] x : ℕ)) / x
      = (1 - (3 : ℚ) ^ order s / 2 ^ s.length)
        * (1 - ((rho s : ℚ) / ((2 : ℚ) ^ s.length - 3 ^ order s)) / x) := by
  have e := gap_identity s x hA hs hy
  have hd : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have hdq : (3 : ℚ) ^ order s < 2 ^ s.length := by exact_mod_cast hd
  have e' : (2 : ℚ) ^ s.length * ((x : ℚ) - (tStep^[s.length] x : ℕ)) + rho s
      = ((2 : ℚ) ^ s.length - 3 ^ order s) * x := by
    have := congrArg (fun n : ℕ => (n : ℚ)) e
    simp only [d_23] at this
    push_cast [Nat.cast_sub hy, Nat.cast_sub hd.le] at this
    exact this
  have hx' : (x : ℚ) ≠ 0 := by positivity
  have hdn : (2 : ℚ) ^ s.length - 3 ^ order s ≠ 0 := by linarith
  have h2 : (2 : ℚ) ^ s.length ≠ 0 := by positivity
  field_simp
  linear_combination e'

/-- Two starts x' < x with the same admissible word s, x' dropping at |s|: x drops at |s|
  and g(x') <= g(x), cross-multiplied (any Order; < when Order > 0, `gap_mul_lt_of_lt`). -/
theorem gap_mul_le_of_lt (s : List Bool) (x x' : ℕ) (hA : Admissible s)
    (hs : tBits x s.length = s) (hs' : tBits x' s.length = s) (hlt : x' < x)
    (hy' : tStep^[s.length] x' < x') :
    tStep^[s.length] x < x ∧
      (x' - tStep^[s.length] x') * x ≤ (x - tStep^[s.length] x) * x' := by
  have h1 := (drop_iff_rho s x' hA hs').mp hy'
  have hy : tStep^[s.length] x < x :=
    (drop_iff_rho s x hA hs).mpr (lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ hlt.le))
  refine ⟨hy, ?_⟩
  have e := gap_identity s x hA hs hy.le
  have e' := gap_identity s x' hA hs' hy'.le
  zify [hy.le, hy'.le] at e e' ⊢
  have key : ((2 : ℤ) ^ s.length) * (((x : ℤ) - (tStep^[s.length] x : ℕ)) * x'
      - ((x' : ℤ) - (tStep^[s.length] x' : ℕ)) * x) = (rho s : ℤ) * (x - x') := by
    linear_combination (x' : ℤ) * e - (x : ℤ) * e'
  have hpos : (0 : ℤ) ≤ (rho s : ℤ) * (x - x') := by
    have : (x' : ℤ) < x := by exact_mod_cast hlt
    have : (0 : ℤ) ≤ rho s := by positivity
    nlinarith
  have hp' : (0 : ℤ) < 2 ^ s.length := by positivity
  nlinarith

/-- The skipped residues: x == m (mod 2^s) and j <= s share the prefix of length j. -/
theorem admissible_tBits_of_modEq {x m s j : ℕ} (h : x ≡ m [MOD 2 ^ s]) (hj : j ≤ s)
    (hA : Admissible (tBits m j)) : Admissible (tBits x j) := by
  have h' : x ≡ m [MOD 2 ^ j] := Nat.ModEq.of_dvd (pow_dvd_pow 2 hj) h
  rwa [tBits_congr x m j h']

/-- The coefficient stopping time of x, searched below 64 (0 if none). -/
def cstop (x : ℕ) : ℕ :=
  ((List.range 64).find? fun m => decide (1 ≤ m ∧ 3 ^ order (tBits x m) < 2 ^ m)).getD 0

/-- For 1 < x <= 31: tBits x (cstop x) is admissible (in powers), and x drops there when its
  Order is at most 10 (27 and 31, of Orders 37 and 35, do not drop before 59 and 56). -/
theorem check_31 : ∀ x < 32, 1 < x →
    ((∀ m < (tBits x (cstop x)).length, 1 ≤ m →
        2 ^ m < 3 ^ order ((tBits x (cstop x)).take m)) ∧
      3 ^ order (tBits x (cstop x)) < 2 ^ (tBits x (cstop x)).length) ∧
    (order (tBits x (cstop x)) ≤ 10 → tStep^[cstop x] x < x) := by
  decide +kernel

/-- widthBound n <= 31 for n <= 10 (its largest, 31, at n = 5). -/
theorem widthBound_le_31 : ∀ n < 11, widthBound n ≤ 31 := by
  decide

/-- ClassDrops at every Order up to 10, unconditionally. -/
theorem classDropsAt_le_10 (n : ℕ) (hn : n ≤ 10) : ClassDropsAt n := by
  apply classDropsAt_of_width n
  intro x hx1 hxb m hA hord
  have hx31 : x ≤ 31 := hxb.trans (widthBound_le_31 n (by omega))
  obtain ⟨hp, hd⟩ := check_31 x (by omega) hx1
  have hA0 : Admissible (tBits x (cstop x)) := (admissible_iff_pow _).mpr hp
  have hm := eq_of_admissible_tBits hA hA0
  subst hm
  exact hd (by omega)

/-- The sieve is sound: a skipped x > 2^s (s >= 3), with an admissible prefix of length j <= s,
  first drops at j, and some x' with 1 < x' <= 2^s and the same word drops at j with
  g(x') <= g(x). Needs ClassDrops at the Order of the word. -/
theorem sieve_skip (s j x : ℕ) (hs3 : 3 ≤ s) (hj : j ≤ s) (hx : 2 ^ s < x)
    (hA : Admissible (tBits x j)) (hCD : ClassDropsAt (order (tBits x j))) :
    (∀ m, 1 ≤ m → m < j → x < tStep^[m] x) ∧ tStep^[j] x < x ∧
      ∃ x', 1 < x' ∧ x' ≤ 2 ^ s ∧ tBits x' j = tBits x j ∧ tStep^[j] x' < x' ∧
        (x' - tStep^[j] x') * x ≤ (x - tStep^[j] x) * x' := by
  set w := tBits x j with hw
  have hlen : w.length = j := length_tBits x j
  have hws : tBits x w.length = w := by rw [hlen]
  have hx0 : 0 < x := Nat.lt_of_le_of_lt (Nat.zero_le _) hx
  have hnd : ∀ m, 1 ≤ m → m < j → x < tStep^[m] x := by
    intro m hm1 hmj
    exact no_drop_before w x hA hws hx0 m hm1 (by omega)
  have h2j : 2 ^ j ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hj
  have h8 : 8 ≤ 2 ^ s := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
  -- a scanned x' with the word w that drops at j
  obtain ⟨x', hx'1, hx's, hbits', hdrop'⟩ :
      ∃ x', 1 < x' ∧ x' ≤ 2 ^ s ∧ tBits x' j = w ∧ tStep^[j] x' < x' := by
    have hc1 := classId_pos w
    have hcle : classId w ≤ 2 ^ j := by have := classId_le w; rwa [hlen] at this
    have hcb : tBits (classId w) w.length = w := tBits_classId w
    rcases Nat.lt_or_ge 1 (classId w) with hc | hc
    · refine ⟨classId w, hc, hcle.trans h2j, by rwa [hlen] at hcb, ?_⟩
      have := (drop_iff_rho w (classId w) hA hcb).mpr (hCD w hA rfl hc)
      rwa [hlen] at this
    · -- the class id is 1: w = tBits 1 j is [true, false], j = 2, and x' = 5
      have hc1' : classId w = 1 := by omega
      have h1 : tBits 1 j = w := by rw [← hc1', ← hlen]; exact hcb
      have hA1 : Admissible (tBits 1 j) := by rw [h1]; exact hA
      have hA2 : Admissible (tBits 1 2) := (admissible_iff_pow _).mpr (by decide)
      have hj2 : j = 2 := eq_of_admissible_tBits hA1 hA2
      subst hj2
      refine ⟨5, by norm_num, by omega, ?_, by decide⟩
      rw [← h1]
      decide
  have hlt : x' < x := by omega
  have hb' : tBits x' w.length = w := by rw [hlen]; exact hbits'
  obtain ⟨hy, hg⟩ := gap_mul_le_of_lt w x x' hA hws hb' hlt (by rw [hlen]; exact hdrop')
  rw [hlen] at hy hg
  exact ⟨hnd, hy, x', hx'1, hx's, hbits', hdrop', hg⟩

/-- An admissible prefix of length j <= 16 has Order at most 10 (3^11 > 2^16). -/
theorem order_le_10_of_admissible {x j : ℕ} (hj : j ≤ 16) (hA : Admissible (tBits x j)) :
    order (tBits x j) ≤ 10 := by
  have hd := (seqProduct_lt_one_iff _).mp hA.lt_one
  rw [length_tBits] at hd
  by_contra h
  have h1 : 3 ^ 11 ≤ 3 ^ order (tBits x j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ j ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) hj
  have : (3 : ℕ) ^ 11 = 177147 := by norm_num
  have : (2 : ℕ) ^ 16 = 65536 := by norm_num
  omega

/-- The sieve of prows for 3 <= s <= 16, with no hypothesis. -/
theorem sieve_skip_16 (s j x : ℕ) (hs3 : 3 ≤ s) (hs : s ≤ 16) (hj : j ≤ s) (hx : 2 ^ s < x)
    (hA : Admissible (tBits x j)) :
    (∀ m, 1 ≤ m → m < j → x < tStep^[m] x) ∧ tStep^[j] x < x ∧
      ∃ x', 1 < x' ∧ x' ≤ 2 ^ s ∧ tBits x' j = tBits x j ∧ tStep^[j] x' < x' ∧
        (x' - tStep^[j] x') * x ≤ (x - tStep^[j] x) * x' :=
  sieve_skip s j x hs3 hj hx hA
    (classDropsAt_le_10 _ (order_le_10_of_admissible (by omega) hA))

end AcceleratedCollatz
