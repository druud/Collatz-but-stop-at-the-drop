-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.AdmissibleLength
import AcceleratedCollatz.RMap
import AcceleratedCollatz.RShift
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
  Marked vector (paper sec:fast): the marked per-step
  sequence along an R-trajectory, fuel-bounded.
-/

namespace AcceleratedCollatz

variable (e : ℤ) (x0 : ℕ)

/-- Marked entry for one step: v for odd/tripling (valuation v), or the
    marked value -w for even/halving steps (valuation w). -/
def markedEntry (isOdd : Bool) (v : ℕ) : ℤ :=
  if isOdd then (v : ℤ) else -(v : ℤ)

@[simp] theorem markedEntry_true (v : ℕ) : markedEntry true v = (v : ℤ) := rfl
@[simp] theorem markedEntry_false (v : ℕ) : markedEntry false v = -(v : ℤ) := rfl

/-- One raw step, exposing its own odd/even type and valuation alongside
    R's usual next-value. -/
def stepInfo (x : ℕ) : Bool × ℕ × ℕ :=
  if x % 2 = 1 then (true, trailingOnes x, R x)
  else (false, trailingZeros x, R x)

/-- Every step's marked entry, in order, including the final (drop-
    completing) one, with the full valuation throughout. -/
def markedVectorRaw : (fuel : ℕ) → (x0 x : ℕ) → List ℤ
  | 0, _, _ => []
  | fuel + 1, x0, x =>
    let (isOdd, v, x') := stepInfo x
    let entry := markedEntry isOdd v
    if x' < x0 then [entry]
    else entry :: markedVectorRaw fuel x0 x'

/-- The marked vector (paper sec:fast): every internal step uses the
    full valuation; a terminal odd step its own valuation; a terminal even
    step `minCorrection` (the minimal-crossing halving count). -/
def markedVectorFinal : (fuel : ℕ) → (x0 x : ℕ) → List ℤ
  | 0, _, _ => []
  | fuel + 1, x0, x =>
    let (isOdd, v, x') := stepInfo x
    if x' < x0 then
      [markedEntry isOdd (if isOdd then v else minCorrection x0 x)]
    else markedEntry isOdd v :: markedVectorFinal fuel x0 x'

/-- Even-branch macro-step, one halving at a time: the halving count
    taken so far together with either `none` (the strip crossed x0,
    terminal) or `some x'` (the strip reached an odd value x' without
    crossing). -/
def evenStep (x0 x : ℕ) : ℕ × Option ℕ :=
  if x = 0 then (0, none)
  else
    let x' := x / 2
    if x' < x0 then (1, none)
    else if x' % 2 = 1 then (1, some x')
    else
      let (w, r) := evenStep x0 x'
      (w + 1, r)
termination_by x
decreasing_by omega

/-- `markedVectorFinal` with the even branch unrolled into single
    halvings via `evenStep`. -/
def markedVector : (fuel : ℕ) → (x0 x : ℕ) → List ℤ
  | 0, _, _ => []
  | fuel + 1, x0, x =>
    if x % 2 = 1 then
      let v := trailingOnes x
      let x' := R x
      if x' < x0 then [markedEntry true v]
      else markedEntry true v :: markedVector fuel x0 x'
    else
      let (w, r) := evenStep x0 x
      match r with
      | none => [markedEntry false w]
      | some x' => markedEntry false w :: markedVector fuel x0 x'

theorem trailingZeros_double (x : ℕ) (hx : x ≠ 0) :
    trailingZeros (2 * x) = trailingZeros x + 1 := by
  unfold trailingZeros
  set w := padicValNat 2 x with hw_def
  have hdvd : 2 ^ w ∣ x := pow_padicValNat_dvd (p := 2) (n := x)
  set s := x / 2 ^ w with hs_def
  have heq : s * 2 ^ w = x := Nat.div_mul_cancel hdvd
  have hsOdd : Odd s := odd_div_pow_trailingZeros x hx
  have h2x : 2 * x = 2 ^ (w + 1) * s := by
    rw [pow_succ]
    calc 2 * x = 2 * (s * 2 ^ w) := by rw [heq]
      _ = 2 ^ w * 2 * s := by ring
  rw [h2x]
  have hSpos : s ≠ 0 := by
    obtain ⟨k, hk⟩ := hsOdd
    omega
  have hNpos : 2 ^ (w + 1) * s ≠ 0 := by positivity
  have hlow : (w + 1) ≤ padicValNat 2 (2 ^ (w + 1) * s) := by
    rcases (padicValNat_dvd_iff (p := 2) (w + 1) (2 ^ (w + 1) * s)).mp ⟨s, rfl⟩ with h | h
    · exact absurd h hNpos
    · exact h
  have hhigh : ¬ 2 ^ (w + 2) ∣ (2 ^ (w + 1) * s) := by
    intro hdvd2
    obtain ⟨c, hc⟩ := hdvd2
    obtain ⟨k, hk⟩ := hsOdd
    have h2wpos : 0 < (2 : ℕ) ^ (w + 1) := by positivity
    have hpoweq : (2 : ℕ) ^ (w + 2) = 2 ^ (w + 1) * 2 := by rw [pow_succ]
    have heq2 : 2 ^ (w + 1) * s = 2 ^ (w + 1) * (2 * c) := by
      rw [hc, hpoweq]
      ring
    have hcancel : s = 2 * c := Nat.eq_of_mul_eq_mul_left h2wpos heq2
    omega
  have hup : ¬ (w + 2 ≤ padicValNat 2 (2 ^ (w + 1) * s)) := by
    intro hcon
    exact hhigh ((padicValNat_dvd_iff (p := 2) (w + 2) (2 ^ (w + 1) * s)).mpr (Or.inr hcon))
  omega

/-- Unfolding lemma for `evenStep`. -/
theorem evenStep_eq (x0 x : ℕ) :
    evenStep x0 x =
      if x = 0 then (0, none)
      else
        if x / 2 < x0 then (1, none)
        else if x / 2 % 2 = 1 then (1, some (x / 2))
        else
          let (w, r) := evenStep x0 (x / 2)
          (w + 1, r) := by
  conv_lhs => rw [evenStep]

/-- Closed form of `evenStep`: for x0 <= x even, `minCorrection` (no
    continuation) if the full strip crosses x0, else the full valuation
    trailingZeros x (continuing at the fully-stripped odd value). -/
theorem evenStep_spec (hx0 : x0 ≥ 1) :
    ∀ x, x0 ≤ x → Even x →
      evenStep x0 x =
        if x / 2 ^ (trailingZeros x) < x0 then (minCorrection x0 x, none)
        else (trailingZeros x, some (x / 2 ^ (trailingZeros x))) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hxge hxeven
    obtain ⟨k, hk⟩ := hxeven
    have hxdiv : x / 2 = k := by omega
    have hxpos : x ≠ 0 := by omega
    rw [evenStep_eq, ite_eq_right hxpos, hxdiv]
    by_cases hcase1 : k < x0
    · rw [ite_eq_left hcase1]
      -- crossing after one halving: the full strip crosses too
      have hv2pos : trailingZeros x ≥ 1 := one_le_padicValNat_of_dvd hxpos ⟨k, by omega⟩
      have hmono : x / 2 ^ (trailingZeros x) ≤ x / 2 ^ 1 :=
        Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hv2pos) (by positivity)
      have hxk : x / 2 ^ (trailingZeros x) < x0 := by
        have h21 : x / 2 ^ 1 = k := by simpa using hxdiv
        omega
      rw [ite_eq_left hxk]
      have hmc : minCorrection x0 x = 1 := by
        rw [minCorrection_eq]
        have hnotbase : ¬ (x < x0 ∨ x = 0) := by omega
        rw [ite_eq_right hnotbase, hxdiv]
        have : minCorrection x0 k = 0 := by
          rw [minCorrection_eq]
          simp [hcase1]
        omega
      rw [hmc]
    · rw [ite_eq_right hcase1]
      by_cases hcase2 : k % 2 = 1
      · rw [ite_eq_left hcase2]
        have hv2 : trailingZeros x = 1 := by
          have h2k : x = 2 * k := by omega
          rw [h2k, trailingZeros_double k (by omega)]
          unfold trailingZeros
          have : padicValNat 2 k = 0 :=
            padicValNat.eq_zero_of_not_dvd (by omega)
          omega
        have hxk : x / 2 ^ (trailingZeros x) = k := by
          rw [hv2]
          simpa using hxdiv
        rw [hxk, ite_eq_right hcase1, hv2]
      · rw [ite_eq_right hcase2]
        have hkge : x0 ≤ k := by omega
        have hkeven : Even k := (Nat.even_iff).mpr (by omega)
        have hklt : k < x := by omega
        have hIH := ih k hklt hkge hkeven
        rw [hIH]
        have h2k : x = 2 * k := by omega
        have hv2 : trailingZeros x = trailingZeros k + 1 := by
          rw [h2k, trailingZeros_double k (by omega)]
        have hxk : x / 2 ^ (trailingZeros x) = k / 2 ^ (trailingZeros k) := by
          rw [hv2, h2k, pow_succ, mul_comm (2 ^ trailingZeros k) 2,
            Nat.mul_div_mul_left k (2 ^ trailingZeros k) (by norm_num : (0:ℕ) < 2)]
        rw [hxk]
        by_cases hcase3 : k / 2 ^ (trailingZeros k) < x0
        · rw [ite_eq_left hcase3, ite_eq_left hcase3]
          change (minCorrection x0 k + 1, none) = (minCorrection x0 x, none)
          have hmc : minCorrection x0 x = minCorrection x0 k + 1 := by
            rw [minCorrection_eq, ite_eq_right (by omega : ¬ (x < x0 ∨ x = 0)), hxdiv]
          rw [hmc]
        · rw [ite_eq_right hcase3, ite_eq_right hcase3, hv2]

/-- One marked entry's bit expansion: positive v (odd/tripling step) ->
    v ones then a terminating zero; negative -w (even/halving step) ->
    w zeros, no terminator (the marked-vector encoding of paper sec:fast). -/
def expandEntry (e : ℤ) : List Bool :=
  if e > 0 then List.replicate e.toNat true ++ [false]
  else List.replicate (-e).toNat false

/-- Full bit-string decoded from a raw marked vector, entry by entry,
    in order (paper's Correspondence argument, "mechanical" direction:
    vector -> bit-string). -/
def decodeVector (v : List ℤ) : List Bool :=
  v.flatMap expandEntry

theorem decodeVector_cons (rest : List ℤ) :
    decodeVector (e :: rest) = expandEntry e ++ decodeVector rest := by
  simp [decodeVector]

theorem decodeVector_singleton : decodeVector [e] = expandEntry e := by
  simp [decodeVector]

theorem expandEntry_natCast (v : ℕ) (hv : 1 ≤ v) :
    expandEntry (v : ℤ) = List.replicate v true ++ [false] := by
  simp [expandEntry]
  omega

theorem expandEntry_neg_natCast (w : ℕ) :
    expandEntry (-(w : ℤ)) = List.replicate w false := by
  simp [expandEntry]

/-- Affine-coefficient fold recovering a class's r-value from its raw
    bit-string (Appendix PARI's r-accumulator): fold left-to-right
    (earliest-generated bit first, matching the bit-string's own
    index-0-first order), r -> (3r+bit)/2, from an arbitrary starting
    value r0. -/
def rFoldFrom (r0 : ℚ) (bits : List Bool) : ℚ :=
  bits.foldl (fun r b => (if b then 3 * r + 1 else r) / 2) r0

def rFold (bits : List Bool) : ℚ := rFoldFrom 0 bits

/-- One-step unfolding of `rFoldFrom`. -/
theorem rFoldFrom_cons (r0 : ℚ) (b : Bool) (rest : List Bool) :
    rFoldFrom r0 (b :: rest) = rFoldFrom ((if b then 3 * r0 + 1 else r0) / 2) rest := by
  unfold rFoldFrom
  simp [List.foldl_cons]

/-- `rFoldFrom` is affine in its starting value: the linear coefficient
    is 3^p3/2^p2 (p3 = count of true bits, p2 = total length), the constant
    term `rFoldFrom 0 bits`. -/
theorem rFoldFrom_linear (bits : List Bool) (r0 : ℚ) :
    rFoldFrom r0 bits =
      (3 : ℚ) ^ (bits.count true) / 2 ^ bits.length * r0 + rFoldFrom 0 bits := by
  induction bits generalizing r0 with
  | nil => simp [rFoldFrom]
  | cons b rest ih =>
    rw [rFoldFrom_cons, rFoldFrom_cons]
    rw [ih (r0 := (if b then 3 * r0 + 1 else r0) / 2),
      ih (r0 := (if b then (3 : ℚ) * 0 + 1 else 0) / 2)]
    cases b
    · simp [List.length_cons]
      ring
    · simp [List.length_cons]
      ring

/-- `-(rFold bits) * 2^p2 / 3^p3` for a bit-string of order p3 and length p2: the
    rational `-rho / 3^p3` (`classIdOf_eq` in TFold). -/
def classIdOf (p2 p3 : ℕ) (bits : List Bool) : ℚ :=
  -(rFold bits) * 2 ^ p2 / 3 ^ p3

/-- One-step unfolding of markedVectorFinal, odd branch. -/
theorem markedVectorFinal_succ_odd (fuel x0 x : ℕ) (hxOdd : x % 2 = 1) :
    markedVectorFinal (fuel + 1) x0 x =
      if R x < x0 then [markedEntry true (trailingOnes x)]
      else markedEntry true (trailingOnes x) :: markedVectorFinal fuel x0 (R x) := by
  simp only [markedVectorFinal, stepInfo, hxOdd, ite_true]

/-- One-step unfolding of `markedVectorFinal`, even branch: the terminal
    entry uses `minCorrection x0 x`, the others `trailingZeros x`. -/
theorem markedVectorFinal_succ_even (fuel x0 x : ℕ) (hxEven : x % 2 ≠ 1) :
    markedVectorFinal (fuel + 1) x0 x =
      if R x < x0 then [markedEntry false (minCorrection x0 x)]
      else markedEntry false (trailingZeros x) :: markedVectorFinal fuel x0 (R x) := by
  simp only [markedVectorFinal, stepInfo, hxEven, ite_false, Bool.false_eq_true]

/-- One-step unfolding of `markedVector`, odd branch. -/
theorem markedVector_succ_odd (fuel x0 x : ℕ) (hxOdd : x % 2 = 1) :
    markedVector (fuel + 1) x0 x =
      if R x < x0 then [markedEntry true (trailingOnes x)]
      else markedEntry true (trailingOnes x) :: markedVector fuel x0 (R x) := by
  simp only [markedVector, hxOdd, ite_true]

/-- One-step unfolding of markedVector, even branch, in terms of
    evenStep directly (companion to markedVectorFinal_succ_even). -/
theorem markedVector_succ_even (fuel x0 x : ℕ) (hxEven : x % 2 ≠ 1) :
    markedVector (fuel + 1) x0 x =
      (let (w, r) := evenStep x0 x
       match r with
       | none => [markedEntry false w]
       | some x' => markedEntry false w :: markedVector fuel x0 x') := by
  simp only [markedVector, hxEven, ite_false]

/-- `markedVector` agrees with `markedVectorFinal` for x0 <= x. -/
theorem markedVector_eq_markedVectorFinal (hx0 : x0 ≥ 1) :
    ∀ fuel x, x0 ≤ x → markedVector fuel x0 x = markedVectorFinal fuel x0 x := by
  intro fuel
  induction fuel with
  | zero =>
    intro x _
    rfl
  | succ fuel ih =>
    intro x hxge
    by_cases hxodd : x % 2 = 1
    · rw [markedVector_succ_odd fuel x0 x hxodd, markedVectorFinal_succ_odd fuel x0 x hxodd]
      by_cases hterm : R x < x0
      · rw [ite_eq_left hterm, ite_eq_left hterm]
      · rw [ite_eq_right hterm, ite_eq_right hterm, ih (R x) (by omega)]
    · rw [markedVector_succ_even fuel x0 x hxodd, markedVectorFinal_succ_even fuel x0 x hxodd]
      have hxeven : Even x := by
        rw [Nat.even_iff]
        omega
      have hx1 : x > 1 := by
        obtain ⟨r, hr⟩ := hxeven
        omega
      have hReq : R x = x / 2 ^ (trailingZeros x) := R_even_closed_form x hx1 hxeven
      rw [hReq, evenStep_spec x0 hx0 x hxge hxeven]
      by_cases hterm : x / 2 ^ (trailingZeros x) < x0
      · rw [ite_eq_left hterm, ite_eq_left hterm]
      · rw [ite_eq_right hterm, ite_eq_right hterm]
        dsimp only
        rw [ih (x / 2 ^ (trailingZeros x)) (by omega)]

/-- Total tripling valuation along a fuel-bounded trajectory from x;
    even steps contribute 0. -/
def trajOrder (x0 : ℕ) : (fuel : ℕ) → (x : ℕ) → ℕ
  | 0, _ => 0
  | fuel + 1, x =>
    if x % 2 = 1 then
      let v := trailingOnes x
      if R x < x0 then v else v + trajOrder x0 fuel (R x)
    else
      if x / 2 ^ (trailingZeros x) < x0 then 0
      else trajOrder x0 fuel (x / 2 ^ (trailingZeros x))

/-- A positive entry expands to that many true bits: its contribution to
    `order` is its value. -/
theorem order_expandEntry_pos (he : e > 0) : order (expandEntry e) = e.toNat := by
  simp [expandEntry, order, he, List.filter_append]

theorem order_expandEntry_nonpos (he : ¬ e > 0) : order (expandEntry e) = 0 := by
  simp [expandEntry, order, he]

theorem order_decodeVector_cons (rest : List ℤ) :
    order (decodeVector (e :: rest)) = order (expandEntry e) + order (decodeVector rest) := by
  unfold decodeVector order
  simp [List.flatMap_cons, List.filter_append, List.length_append]

/-- `trajOrder` equals `order` of the decoded trajectory. -/
theorem order_decodeVector_eq_trajOrder (hx0 : x0 ≥ 1) :
    ∀ fuel x, x0 ≤ x →
      order (decodeVector (markedVector fuel x0 x)) = trajOrder x0 fuel x := by
  intro fuel
  induction fuel with
  | zero =>
    intro x _
    simp [markedVector, trajOrder, decodeVector, order]
  | succ fuel ih =>
    intro x hxge
    by_cases hxodd : x % 2 = 1
    · rw [markedVector_succ_odd fuel x0 x hxodd]
      unfold trajOrder
      rw [ite_eq_left hxodd]
      have hvpos : (trailingOnes x : ℤ) > 0 := by
        have hv1 : trailingOnes x ≥ 1 := by
          have hxodd' : Odd x := Nat.odd_iff.mpr hxodd
          obtain ⟨j, hj⟩ := hxodd'
          exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
        exact_mod_cast hv1
      by_cases hterm : R x < x0
      · rw [ite_eq_left hterm, ite_eq_left hterm]
        have hvpos' : 0 < trailingOnes x := by exact_mod_cast hvpos
        simp [decodeVector, order, markedEntry_true, expandEntry, hvpos']
      · rw [ite_eq_right hterm, ite_eq_right hterm, markedEntry_true, order_decodeVector_cons,
          order_expandEntry_pos (trailingOnes x : ℤ) hvpos, ih (R x) (by omega)]
        simp
    · rw [markedVector_succ_even fuel x0 x hxodd]
      unfold trajOrder
      rw [ite_eq_right hxodd]
      have hxeven : Even x := by
        rw [Nat.even_iff]
        omega
      rw [evenStep_spec x0 hx0 x hxge hxeven]
      by_cases hterm : x / 2 ^ (trailingZeros x) < x0
      · rw [ite_eq_left hterm, ite_eq_left hterm]
        have hmcnn : ¬ ((minCorrection x0 x : ℤ) < 0) := not_lt.mpr (Int.natCast_nonneg _)
        simp [decodeVector, order, markedEntry_false, expandEntry, hmcnn]
      · rw [ite_eq_right hterm, ite_eq_right hterm]
        dsimp only
        rw [markedEntry_false, order_decodeVector_cons, order_expandEntry_nonpos _ (by omega),
          ih (x / 2 ^ (trailingZeros x)) (by omega)]
        simp

/-- `order s` is the number of `true` entries of s. -/
theorem order_eq_count_true (s : List Bool) : order s = s.count true := by
  unfold order
  induction s with
  | nil => simp
  | cons b t ih =>
    cases b
    · simp [ih]
    · simp [ih]

/-- Closed form of `seqProduct`: 3^(count true)/2^length. -/
theorem seqProduct_eq_pow_ratio (bits : List Bool) :
    seqProduct bits = (3 : ℚ) ^ (bits.count true) / 2 ^ bits.length := by
  rw [seqProduct_eq, ← order_eq_count_true]
  have hle : order bits ≤ bits.length := order_le_length bits
  rw [div_pow, div_pow, one_pow]
  rw [div_mul_div_comm, mul_one, ← pow_add]
  congr 2
  omega

/-- (order, length, drop) of the remaining trajectory from x with
    threshold x0; drop is the final value once terminated (x if the fuel
    runs out first). -/
def trajStats (x0 : ℕ) : (fuel : ℕ) → (x : ℕ) → ℕ × ℕ × ℕ
  | 0, x => (0, 0, x)
  | fuel + 1, x =>
    if x % 2 = 1 then
      let v := trailingOnes x
      let xp := R x
      if xp < x0 then (v, v + 1, xp)
      else
        let (o, l, d) := trajStats x0 fuel xp
        (v + o, v + 1 + l, d)
    else
      let w := trailingZeros x
      let xp := x / 2 ^ w
      if xp < x0 then (0, minCorrection x0 x, x / 2 ^ (minCorrection x0 x))
      else
        let (o, l, d) := trajStats x0 fuel xp
        (o, w + l, d)

/-- Prefix splitting for `markedVector`: if the trajectory has
    not terminated within the first fuel1 steps (drop value still >= x0),
    fuel1 + fuel2 steps give the fuel1-step entries followed by fuel2 more
    steps from where fuel1 steps left off. -/
theorem markedVector_prefix_split (hx0 : x0 > 1) :
    ∀ fuel1 fuel2 x, x0 ≤ x →
      (trajStats x0 fuel1 x).2.2 ≥ x0 →
      markedVector (fuel1 + fuel2) x0 x =
        markedVector fuel1 x0 x ++
          markedVector fuel2 x0 (trajStats x0 fuel1 x).2.2 := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 x _ _
    simp [trajStats, markedVector]
  | succ fuel1 ih =>
    intro fuel2 x hxge hnonterm
    have hx1 : x > 1 := by omega
    have hnonterm' := hnonterm
    unfold trajStats at hnonterm'
    by_cases hxodd : x % 2 = 1
    · simp only [hxodd, ite_true] at hnonterm'
      by_cases hterm : R x < x0
      · simp only [hterm, ite_true] at hnonterm'
        omega
      · simp only [hterm, ite_false] at hnonterm'
        have heq : fuel1 + 1 + fuel2 = (fuel1 + fuel2) + 1 := by ring
        rw [heq, markedVector_succ_odd (fuel1 + fuel2) x0 x hxodd,
            markedVector_succ_odd fuel1 x0 x hxodd,
            ite_eq_right hterm, ite_eq_right hterm, List.cons_append]
        have hstats_eq : (trajStats x0 (fuel1 + 1) x).2.2 = (trajStats x0 fuel1 (R x)).2.2 := by
          simp only [trajStats, hxodd, ite_true, hterm, ite_false]
        rw [hstats_eq]
        congr 1
        exact ih fuel2 (R x) (by omega) hnonterm'
    · simp only [hxodd, ite_false] at hnonterm'
      have hxeven : Even x := Nat.even_iff.mpr (by omega)
      have hReq : R x = x / 2 ^ (trailingZeros x) := R_even_closed_form x hx1 hxeven
      by_cases hterm : x / 2 ^ (trailingZeros x) < x0
      · simp only [hterm, ite_true] at hnonterm'
        have hsuff : x / 2 ^ (minCorrection x0 x) < x0 := minCorrection_suff x0 x (by omega)
        omega
      · simp only [hterm, ite_false] at hnonterm'
        have heq : fuel1 + 1 + fuel2 = (fuel1 + fuel2) + 1 := by ring
        rw [heq, markedVector_succ_even (fuel1 + fuel2) x0 x hxodd,
            markedVector_succ_even fuel1 x0 x hxodd,
            evenStep_spec x0 (by omega) x hxge hxeven, ite_eq_right hterm]
        dsimp only
        rw [List.cons_append]
        have hstats_eq : (trajStats x0 (fuel1 + 1) x).2.2 =
            (trajStats x0 fuel1 (x / 2 ^ (trailingZeros x))).2.2 := by
          simp only [trajStats, hxodd, ite_false, hterm]
        rw [hstats_eq]
        congr 1
        exact ih fuel2 (x / 2 ^ (trailingZeros x)) (by omega) hnonterm'

/-- Length companion to order_expandEntry_pos/nonpos. -/
theorem length_expandEntry_pos (he : e > 0) :
    (expandEntry e).length = e.toNat + 1 := by
  simp [expandEntry, he]

theorem length_expandEntry_nonpos (he : ¬ e > 0) :
    (expandEntry e).length = (-e).toNat := by
  simp [expandEntry, he]

theorem length_decodeVector_cons (rest : List ℤ) :
    (decodeVector (e :: rest)).length = (expandEntry e).length + (decodeVector rest).length := by
  unfold decodeVector
  simp [List.flatMap_cons, List.length_append]

/-- The decoded bit-length of a fuel-bounded trajectory's entries
    equals the length component of `trajStats`. -/
theorem length_decodeVector_eq_trajStats (hx0 : x0 > 1) :
    ∀ fuel x, x0 ≤ x →
      (decodeVector (markedVector fuel x0 x)).length = (trajStats x0 fuel x).2.1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro x _
    simp [markedVector, trajStats, decodeVector]
  | succ fuel ih =>
    intro x hxge
    unfold trajStats
    by_cases hxodd : x % 2 = 1
    · simp only [hxodd, ite_true]
      have hv1 : trailingOnes x ≥ 1 := by
        have hxodd' : Odd x := Nat.odd_iff.mpr hxodd
        obtain ⟨j, hj⟩ := hxodd'
        exact one_le_padicValNat_of_dvd (by omega) ⟨j + 1, by omega⟩
      have hvpos : (trailingOnes x : ℤ) > 0 := by exact_mod_cast hv1
      by_cases hterm : R x < x0
      · rw [markedVector_succ_odd fuel x0 x hxodd, ite_eq_left hterm, ite_eq_left hterm]
        have hv1' : 0 < trailingOnes x := hv1
        simp [decodeVector, markedEntry_true, expandEntry, hv1']
      · rw [markedVector_succ_odd fuel x0 x hxodd, ite_eq_right hterm, ite_eq_right hterm]
        dsimp only
        rw [markedEntry_true, length_decodeVector_cons,
          length_expandEntry_pos (trailingOnes x : ℤ) hvpos, ih (R x) (by omega)]
        simp
    · simp only [hxodd, ite_false]
      have hxeven : Even x := Nat.even_iff.mpr (by omega)
      have hx1 : x > 1 := by
        obtain ⟨r, hr⟩ := hxeven
        omega
      by_cases hterm : x / 2 ^ (trailingZeros x) < x0
      · rw [markedVector_succ_even fuel x0 x hxodd,
          evenStep_spec x0 (by omega) x hxge hxeven, ite_eq_left hterm, ite_eq_left hterm]
        have hmcnn : ¬ (-(minCorrection x0 x : ℤ) > 0) := by omega
        simp only [decodeVector, markedEntry_false, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, expandEntry, hmcnn, ite_false, List.length_replicate]
        simp
      · rw [markedVector_succ_even fuel x0 x hxodd,
          evenStep_spec x0 (by omega) x hxge hxeven, ite_eq_right hterm, ite_eq_right hterm]
        dsimp only
        rw [markedEntry_false, length_decodeVector_cons,
          length_expandEntry_nonpos (-(trailingZeros x : ℤ)) (by omega),
          ih (x / 2 ^ (trailingZeros x)) (by omega)]
        simp

/-- Every macro-step consumes at least 1 bit of length. -/
theorem trajStats_length_ge_one (hx0 : x0 > 1) :
    ∀ fuel x, x0 ≤ x → fuel ≥ 1 → (trajStats x0 fuel x).2.1 ≥ 1 := by
  intro fuel x hxge hfuel
  obtain ⟨fuel', rfl⟩ := Nat.exists_eq_add_of_le hfuel
  have heq : 1 + fuel' = fuel' + 1 := by ring
  rw [heq]
  have hx1 : x > 1 := by omega
  unfold trajStats
  by_cases hxodd : x % 2 = 1
  · simp only [hxodd, ite_true]
    by_cases hterm : R x < x0
    · simp [hterm]
    · simp [hterm]
      try omega
  · simp only [hxodd, ite_false]
    have hxeven : Even x := Nat.even_iff.mpr (by omega)
    by_cases hterm : x / 2 ^ (trailingZeros x) < x0
    · simp only [hterm, ite_true]
      have hmc : minCorrection x0 x ≥ 1 := by
        rw [minCorrection_eq]
        have : ¬ (x < x0 ∨ x = 0) := by omega
        simp [this]
      exact hmc
    · simp only [hterm, ite_false]
      have hv1 : trailingZeros x ≥ 1 := by
        obtain ⟨r, hr⟩ := hxeven
        have : x ≠ 0 := by omega
        exact one_le_padicValNat_of_dvd this ⟨r, by omega⟩
      omega

/-- `trajOrder` is the order component of `trajStats`. -/
theorem trajOrder_eq_trajStats_fst :
    ∀ fuel x, trajOrder x0 fuel x = (trajStats x0 fuel x).1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro x
    simp [trajOrder, trajStats]
  | succ fuel ih =>
    intro x
    unfold trajOrder trajStats
    by_cases hxodd : x % 2 = 1
    · simp only [hxodd, ite_true]
      by_cases hterm : R x < x0
      · simp [hterm]
      · simp [hterm, ih (R x)]
    · simp only [hxodd, ite_false]
      by_cases hterm : x / 2 ^ (trailingZeros x) < x0
      · simp [hterm]
      · simp [hterm, ih (x / 2 ^ (trailingZeros x))]

/-- If the trajectory of x0 (fuel1 + fuel2 macro-steps) is Admissible
    when decoded and has not terminated within the first fuel1 steps, the
    prefix of those fuel1 steps satisfies 2^length < 3^order. -/
theorem admissible_gives_prefix_lt (hx0 : x0 > 1) (fuel1 fuel2 : ℕ)
    (hnonterm : (trajStats x0 fuel1 x0).2.2 ≥ x0)
    (hfuel1pos : fuel1 ≥ 1) (hfuel2pos : fuel2 ≥ 1)
    (hAdm : Admissible (decodeVector (markedVector (fuel1 + fuel2) x0 x0))) :
    2 ^ (trajStats x0 fuel1 x0).2.1 < 3 ^ (trajStats x0 fuel1 x0).1 := by
  have hsplit := markedVector_prefix_split x0 hx0 fuel1 fuel2 x0 (le_refl x0) hnonterm
  have hdecode_split : decodeVector (markedVector (fuel1 + fuel2) x0 x0) =
      decodeVector (markedVector fuel1 x0 x0) ++
        decodeVector (markedVector fuel2 x0 (trajStats x0 fuel1 x0).2.2) := by
    rw [hsplit]
    exact List.flatMap_append
  have hlen : (decodeVector (markedVector fuel1 x0 x0)).length =
      (trajStats x0 fuel1 x0).2.1 :=
    length_decodeVector_eq_trajStats x0 hx0 fuel1 x0 (le_refl x0)
  have htake : (decodeVector (markedVector (fuel1 + fuel2) x0 x0)).take
      (trajStats x0 fuel1 x0).2.1 = decodeVector (markedVector fuel1 x0 x0) := by
    rw [hdecode_split, ← hlen]
    exact List.take_left
  have htailge1 : (decodeVector (markedVector fuel2 x0 (trajStats x0 fuel1 x0).2.2)).length
      ≥ 1 := by
    have := length_decodeVector_eq_trajStats x0 hx0 fuel2
      (trajStats x0 fuel1 x0).2.2 hnonterm
    rw [this]
    exact trajStats_length_ge_one x0 hx0 fuel2 (trajStats x0 fuel1 x0).2.2 hnonterm hfuel2pos
  have hfulllen : (trajStats x0 fuel1 x0).2.1 <
      (decodeVector (markedVector (fuel1 + fuel2) x0 x0)).length := by
    rw [hdecode_split, List.length_append, hlen]
    omega
  have hmpos : (1:ℕ) ≤ (trajStats x0 fuel1 x0).2.1 :=
    trajStats_length_ge_one x0 hx0 fuel1 x0 (le_refl x0) hfuel1pos
  have hclause := hAdm.prefix_gt (trajStats x0 fuel1 x0).2.1 hmpos hfulllen
  rw [htake, seqProduct_eq_pow_ratio, ← order_eq_count_true,
      order_decodeVector_eq_trajOrder x0 (by omega) fuel1 x0 (le_refl x0), hlen,
      trajOrder_eq_trajStats_fst x0 fuel1 x0] at hclause
  rw [lt_div_iff₀ (by positivity)] at hclause
  have hclause' : (2:ℚ) ^ (trajStats x0 fuel1 x0).2.1 < 3 ^ (trajStats x0 fuel1 x0).1 := by
    linarith [hclause]
  exact_mod_cast hclause'

/-- `trajStats` additivity: fuel1 + fuel2 steps from x give the
    combined (order, length) of fuel1 steps plus fuel2 more steps from where
    fuel1 left off, and the drop of the latter, provided fuel1 steps have
    not terminated. -/
theorem trajStats_add (hx0 : x0 > 1) :
    ∀ fuel1 fuel2 x, x0 ≤ x → (trajStats x0 fuel1 x).2.2 ≥ x0 →
      (trajStats x0 (fuel1 + fuel2) x).1 =
        (trajStats x0 fuel1 x).1 + (trajStats x0 fuel2 (trajStats x0 fuel1 x).2.2).1 ∧
      (trajStats x0 (fuel1 + fuel2) x).2.1 =
        (trajStats x0 fuel1 x).2.1 + (trajStats x0 fuel2 (trajStats x0 fuel1 x).2.2).2.1 ∧
      (trajStats x0 (fuel1 + fuel2) x).2.2 =
        (trajStats x0 fuel2 (trajStats x0 fuel1 x).2.2).2.2 := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 x _ _
    simp [trajStats]
  | succ fuel1 ih =>
    intro fuel2 x hxge hnonterm
    have hx1 : x > 1 := by omega
    have hnonterm' := hnonterm
    simp only [trajStats] at hnonterm'
    by_cases hxodd : x % 2 = 1
    · simp only [hxodd, ite_true] at hnonterm'
      by_cases hterm : R x < x0
      · simp only [hterm, ite_true] at hnonterm'
        omega
      · simp only [hterm, ite_false] at hnonterm'
        have heq : fuel1 + 1 + fuel2 = (fuel1 + fuel2) + 1 := by ring
        have hrec := ih fuel2 (R x) (by omega) hnonterm'
        have hL1 : (trajStats x0 (fuel1 + 1) x).1 =
            trailingOnes x + (trajStats x0 fuel1 (R x)).1 := by
          simp only [trajStats, hxodd, ite_true, hterm, ite_false]
        have hL2 : (trajStats x0 (fuel1 + 1) x).2.1 =
            trailingOnes x + 1 + (trajStats x0 fuel1 (R x)).2.1 := by
          simp only [trajStats, hxodd, ite_true, hterm, ite_false]
        have hL3 : (trajStats x0 (fuel1 + 1) x).2.2 = (trajStats x0 fuel1 (R x)).2.2 := by
          simp only [trajStats, hxodd, ite_true, hterm, ite_false]
        have hR1 : (trajStats x0 ((fuel1 + fuel2) + 1) x).1 =
            trailingOnes x + (trajStats x0 (fuel1 + fuel2) (R x)).1 := by
          simp only [trajStats, hxodd, ite_true, hterm, ite_false]
        have hR2 : (trajStats x0 ((fuel1 + fuel2) + 1) x).2.1 =
            trailingOnes x + 1 + (trajStats x0 (fuel1 + fuel2) (R x)).2.1 := by
          simp only [trajStats, hxodd, ite_true, hterm, ite_false]
        have hR3 : (trajStats x0 ((fuel1 + fuel2) + 1) x).2.2 =
            (trajStats x0 (fuel1 + fuel2) (R x)).2.2 := by
          simp only [trajStats, hxodd, ite_true, hterm, ite_false]
        rw [heq, hR1, hR2, hR3, hL1, hL2, hL3]
        omega
    · simp only [hxodd, ite_false] at hnonterm'
      have hxeven : Even x := Nat.even_iff.mpr (by omega)
      by_cases hterm : x / 2 ^ (trailingZeros x) < x0
      · simp only [hterm, ite_true] at hnonterm'
        have hsuff : x / 2 ^ (minCorrection x0 x) < x0 := minCorrection_suff x0 x (by omega)
        omega
      · simp only [hterm, ite_false] at hnonterm'
        have heq : fuel1 + 1 + fuel2 = (fuel1 + fuel2) + 1 := by ring
        have hrec := ih fuel2 (x / 2 ^ (trailingZeros x)) (by omega) hnonterm'
        have hL1 : (trajStats x0 (fuel1 + 1) x).1 =
            (trajStats x0 fuel1 (x / 2 ^ (trailingZeros x))).1 := by
          simp only [trajStats, hxodd, ite_false, hterm]
        have hL2 : (trajStats x0 (fuel1 + 1) x).2.1 =
            trailingZeros x + (trajStats x0 fuel1 (x / 2 ^ (trailingZeros x))).2.1 := by
          simp only [trajStats, hxodd, ite_false, hterm]
        have hL3 : (trajStats x0 (fuel1 + 1) x).2.2 =
            (trajStats x0 fuel1 (x / 2 ^ (trailingZeros x))).2.2 := by
          simp only [trajStats, hxodd, ite_false, hterm]
        have hR1 : (trajStats x0 ((fuel1 + fuel2) + 1) x).1 =
            (trajStats x0 (fuel1 + fuel2) (x / 2 ^ (trailingZeros x))).1 := by
          simp only [trajStats, hxodd, ite_false, hterm]
        have hR2 : (trajStats x0 ((fuel1 + fuel2) + 1) x).2.1 =
            trailingZeros x + (trajStats x0 (fuel1 + fuel2) (x / 2 ^ (trailingZeros x))).2.1 := by
          simp only [trajStats, hxodd, ite_false, hterm]
        have hR3 : (trajStats x0 ((fuel1 + fuel2) + 1) x).2.2 =
            (trajStats x0 (fuel1 + fuel2) (x / 2 ^ (trailingZeros x))).2.2 := by
          simp only [trajStats, hxodd, ite_false, hterm]
        rw [heq, hR1, hR2, hR3, hL1, hL2, hL3]
        omega

end AcceleratedCollatz
