-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainParse
import AcceleratedCollatz.TSieve

/-!
  The three letters of OEIS A324245 on odd k (paper sec:three): U for k ≡ 3 (mod 4) to
  (3k+1)/2, D for k ≡ 1 (mod 8) to (3k+1)/4, S for k ≡ 5 (mod 8) to (k-1)/4; their bits
  U = 1, D = 10, S = 00 (`udsBits`). After the letters w of k the value z satisfies
  2^|bits| z = 3^M k + c (`udsStep_iterate_affine`, M the Order of the bits), so for all
  large k with letters w the stop (`IsUdsStop`) is at the first prefix whose product is
  below 1 (`isUdsStop_iff_of_large`). The odd starts of a letter word are one class
  modulo 2^(|bits| + 1) (`udsWord_class`).
-/

namespace AcceleratedCollatz

/-- The three letters of A324245. -/
inductive UDS
  | U
  | D
  | S
  deriving DecidableEq, Repr

/-- The letter of odd k. -/
def udsOf (k : ℕ) : UDS :=
  if k % 4 = 3 then .U else if k % 8 = 1 then .D else .S

/-- The step of the letter of k. -/
def udsStep (k : ℕ) : ℕ :=
  match udsOf k with
  | .U => (3 * k + 1) / 2
  | .D => (3 * k + 1) / 4
  | .S => (k - 1) / 4

/-- The first n letters of k. -/
def udsWord : ℕ → ℕ → List UDS
  | _, 0 => []
  | k, n + 1 => udsOf k :: udsWord (udsStep k) n

/-- The bits of a letter: U = 1, D = 10, S = 00. -/
def UDS.bits : UDS → List Bool
  | .U => [true]
  | .D => [true, false]
  | .S => [false, false]

/-- The term c of a letter: 2^|bits| z = 3^Order k + c. -/
def UDS.shift : UDS → ℤ
  | .U => 1
  | .D => 1
  | .S => -1

/-- The bits of a letter word. -/
def udsBits (w : List UDS) : List Bool := w.flatMap UDS.bits

/-- The term c of a letter word: 2^|bits| z = 3^M k + c after its letters. -/
def udsConst : List UDS → ℤ
  | [] => 0
  | c :: w => 3 ^ order (udsBits w) * c.shift + 2 ^ c.bits.length * udsConst w

/-- k stops after j letters: the value is below k there and not before. -/
def IsUdsStop (k j : ℕ) : Prop :=
  udsStep^[j] k < k ∧ ∀ i < j, k ≤ udsStep^[i] k

/-- The product rule: the product of the bits is below 1 at the end of the letter word
    and above 1 at every proper nonempty prefix. -/
def UdsStopWord (w : List UDS) : Prop :=
  seqProduct (udsBits w) < 1 ∧
    ∀ i, 1 ≤ i → i < w.length → 1 < seqProduct (udsBits (w.take i))

@[simp]
theorem udsBits_nil : udsBits [] = [] := rfl

@[simp]
theorem udsBits_cons (c : UDS) (w : List UDS) : udsBits (c :: w) = c.bits ++ udsBits w := by
  simp [udsBits]

theorem udsBits_append (v w : List UDS) : udsBits (v ++ w) = udsBits v ++ udsBits w := by
  simp [udsBits]

theorem UDS.bits_ne_nil (c : UDS) : c.bits ≠ [] := by
  cases c with
  | U =>
    simp [UDS.bits]
  | D =>
    simp [UDS.bits]
  | S =>
    simp [UDS.bits]

theorem udsBits_ne_nil (w : List UDS) (hw : w ≠ []) : udsBits w ≠ [] := by
  obtain ⟨c, v, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [UDS.bits_ne_nil]

theorem length_le_length_udsBits (w : List UDS) : w.length ≤ (udsBits w).length := by
  induction w with
  | nil =>
    simp
  | cons c w ih =>
    have hc : 1 ≤ c.bits.length := List.length_pos_of_ne_nil (UDS.bits_ne_nil c)
    simp only [udsBits_cons, List.length_append, List.length_cons]
    omega

/-- A letter keeps k odd. -/
theorem udsStep_odd (k : ℕ) (hk : k % 2 = 1) : udsStep k % 2 = 1 := by
  unfold udsStep udsOf
  split_ifs with h1 h2
  · simp only
    omega
  · simp only
    omega
  · simp only
    omega

theorem udsStep_iterate_odd (k : ℕ) (hk : k % 2 = 1) (n : ℕ) : udsStep^[n] k % 2 = 1 := by
  induction n generalizing k with
  | zero =>
    exact hk
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (udsStep k) (udsStep_odd k hk)

/-- One letter: 2^|bits| z = 3^Order k + c. -/
theorem udsStep_affine (k : ℕ) (hk : k % 2 = 1) :
    2 ^ (udsOf k).bits.length * (udsStep k : ℤ) =
      3 ^ order (udsOf k).bits * k + (udsOf k).shift := by
  unfold udsStep udsOf
  split_ifs with h1 h2
  · have h : 2 * ((3 * k + 1) / 2) = 3 * k + 1 := by omega
    simp only [UDS.bits, UDS.shift, List.length_singleton, pow_one]
    norm_num [order]
    exact_mod_cast h
  · have h : 4 * ((3 * k + 1) / 4) = 3 * k + 1 := by omega
    simp only [UDS.bits, UDS.shift, List.length_cons, List.length_nil]
    norm_num [order]
    exact_mod_cast h
  · have h : 4 * ((k - 1) / 4) + 1 = k := by omega
    simp only [UDS.bits, UDS.shift, List.length_cons, List.length_nil]
    norm_num [order]
    have h' : (4 : ℤ) * ((k - 1) / 4 : ℕ) + 1 = k := by exact_mod_cast h
    linarith

theorem udsWord_succ (k n : ℕ) : udsWord k (n + 1) = udsOf k :: udsWord (udsStep k) n := rfl

@[simp]
theorem length_udsWord (k n : ℕ) : (udsWord k n).length = n := by
  induction n generalizing k with
  | zero =>
    rfl
  | succ n ih =>
    simp [udsWord, ih]

theorem udsWord_take (k n m : ℕ) (hm : m ≤ n) : (udsWord k n).take m = udsWord k m := by
  induction n generalizing k m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    rfl
  | succ n ih =>
    cases m with
    | zero =>
      rfl
    | succ m =>
      rw [udsWord_succ, udsWord_succ, List.take_succ_cons, ih (udsStep k) m (by omega)]

/-- The value after the letters w of k: 2^|bits w| z = 3^M k + c w. -/
theorem udsStep_iterate_affine (w : List UDS) (k : ℕ) (hk : k % 2 = 1)
    (hw : udsWord k w.length = w) :
    2 ^ (udsBits w).length * (udsStep^[w.length] k : ℤ) =
      3 ^ order (udsBits w) * k + udsConst w := by
  induction w generalizing k with
  | nil =>
    simp [udsConst, order]
  | cons c w ih =>
    rw [List.length_cons, udsWord_succ] at hw
    have hc : udsOf k = c := (List.cons.inj hw).1
    have hrest : udsWord (udsStep k) w.length = w := (List.cons.inj hw).2
    have h1 := udsStep_affine k hk
    rw [hc] at h1
    have h2 := ih (udsStep k) (udsStep_odd k hk) hrest
    rw [List.length_cons, Function.iterate_succ_apply, udsBits_cons, List.length_append,
      order_append, udsConst, pow_add, pow_add]
    calc (2 : ℤ) ^ c.bits.length * 2 ^ (udsBits w).length * (udsStep^[w.length] (udsStep k) : ℤ)
        = 2 ^ c.bits.length * (3 ^ order (udsBits w) * (udsStep k : ℤ) + udsConst w) := by
          rw [← h2]
          ring
      _ = 3 ^ order (udsBits w) * (2 ^ c.bits.length * (udsStep k : ℤ)) +
            2 ^ c.bits.length * udsConst w := by
          ring
      _ = 3 ^ order c.bits * 3 ^ order (udsBits w) * k +
            (3 ^ order (udsBits w) * c.shift + 2 ^ c.bits.length * udsConst w) := by
          rw [h1]
          ring

/-- 3^M ≠ 2^|bits| for a nonempty letter word. -/
theorem three_pow_ne_two_pow (a b : ℕ) (hb : 1 ≤ b) : (3 : ℤ) ^ a ≠ 2 ^ b := by
  intro h
  have hN : 3 ^ a = 2 ^ b := by exact_mod_cast h
  have h2 : 2 ∣ 3 ^ a := by
    rw [hN]
    exact dvd_pow_self 2 (by omega)
  have h3 : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  omega

/-- Large k: the value after the letters w is below k iff their product is below 1. -/
theorem udsStep_iterate_lt_iff (w : List UDS) (hne : w ≠ []) (k : ℕ) (hk : k % 2 = 1)
    (hw : udsWord k w.length = w) (hlarge : (udsConst w).natAbs < k) :
    udsStep^[w.length] k < k ↔ seqProduct (udsBits w) < 1 := by
  have haff := udsStep_iterate_affine w k hk hw
  have hb : 1 ≤ (udsBits w).length := List.length_pos_of_ne_nil (udsBits_ne_nil w hne)
  have hne3 := three_pow_ne_two_pow (order (udsBits w)) (udsBits w).length hb
  rw [seqProduct_lt_one_iff]
  set X : ℤ := 2 ^ (udsBits w).length with hX
  set Y : ℤ := 3 ^ order (udsBits w) with hY
  set z : ℤ := (udsStep^[w.length] k : ℤ) with hz
  have hXpos : 0 < X := by positivity
  have hc1 : udsConst w < k := by
    rcases Int.natAbs_eq (udsConst w) with h | h
    · omega
    · omega
  have hc2 : -(k : ℤ) < udsConst w := by
    rcases Int.natAbs_eq (udsConst w) with h | h
    · omega
    · omega
  have hiff : (3 ^ order (udsBits w) < 2 ^ (udsBits w).length) ↔ Y < X := by
    rw [hX, hY]
    exact_mod_cast Iff.rfl
  rw [hiff]
  have hzk : udsStep^[w.length] k < k ↔ z < k := by
    rw [hz]
    exact_mod_cast Iff.rfl
  rw [hzk]
  constructor
  · intro hlt
    by_contra hge
    have hYX : X < Y := lt_of_le_of_ne (not_lt.mp hge) (Ne.symm hne3)
    have h1 : (X + 1) * k ≤ Y * k := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      omega
    have h2 : X * z < X * k := mul_lt_mul_of_pos_left hlt hXpos
    nlinarith
  · intro hlt
    have h1 : (Y + 1) * k ≤ X * k := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      omega
    have h2 : X * z < X * k := by
      nlinarith
    exact lt_of_mul_lt_mul_left h2 hXpos.le

/-- For all large k with letters w the stop is at the first prefix of w whose product is
    below 1. -/
theorem isUdsStop_iff_of_large (w : List UDS) (hne : w ≠ []) :
    ∃ K, ∀ k, K < k → k % 2 = 1 → udsWord k w.length = w →
      (IsUdsStop k w.length ↔ UdsStopWord w) := by
  refine ⟨(Finset.range (w.length + 1)).sup fun i => (udsConst (w.take i)).natAbs, ?_⟩
  intro k hK hk hw
  have hpre : ∀ i, 1 ≤ i → i ≤ w.length →
      (udsStep^[i] k < k ↔ seqProduct (udsBits (w.take i)) < 1) := by
    intro i hi1 hi
    have hti : (w.take i).length = i := by
      simp only [List.length_take]
      omega
    have hwi : udsWord k (w.take i).length = w.take i := by
      rw [hti, ← udsWord_take k w.length i hi, hw]
    have hne' : w.take i ≠ [] := by
      intro h
      rw [h] at hti
      simp at hti
      omega
    have hle : (udsConst (w.take i)).natAbs ≤
        (Finset.range (w.length + 1)).sup fun i => (udsConst (w.take i)).natAbs :=
      Finset.le_sup (f := fun i => (udsConst (w.take i)).natAbs)
        (Finset.mem_range.mpr (by omega))
    have h := udsStep_iterate_lt_iff (w.take i) hne' k hk hwi (by omega)
    rwa [hti] at h
  have hlen : 1 ≤ w.length := List.length_pos_of_ne_nil hne
  have hfull := hpre w.length hlen le_rfl
  rw [List.take_length] at hfull
  unfold IsUdsStop UdsStopWord
  rw [hfull]
  constructor
  · rintro ⟨hlt, hmin⟩
    refine ⟨hlt, fun i hi1 hi => ?_⟩
    have hge := hmin i hi
    have hnot : ¬ seqProduct (udsBits (w.take i)) < 1 := by
      rw [← hpre i hi1 hi.le]
      omega
    have hne1 : seqProduct (udsBits (w.take i)) ≠ 1 := by
      apply seqProduct_ne_one
      apply udsBits_ne_nil
      intro h
      have := congrArg List.length h
      simp only [List.length_take, List.length_nil] at this
      omega
    exact lt_of_le_of_ne (not_lt.mp hnot) (Ne.symm hne1)
  · rintro ⟨hlt, hgt⟩
    refine ⟨hlt, fun i hi => ?_⟩
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      exact le_rfl
    · have hnot : ¬ udsStep^[i] k < k := by
        rw [hpre i hpos hi.le]
        exact not_lt.mpr (hgt i hpos hi).le
      omega

/-- Odd starts congruent modulo 2^(|bits w| + 1) have the same letters w. -/
theorem udsWord_congr (w : List UDS) (k k' : ℕ) (hk : k % 2 = 1) (hk' : k' % 2 = 1)
    (hmod : (2 : ℤ) ^ ((udsBits w).length + 1) ∣ (k : ℤ) - k')
    (hw : udsWord k w.length = w) : udsWord k' w.length = w := by
  induction w generalizing k k' with
  | nil =>
    rfl
  | cons c w ih =>
    rw [List.length_cons, udsWord_succ] at hw ⊢
    have hc : udsOf k = c := (List.cons.inj hw).1
    have hrest : udsWord (udsStep k) w.length = w := (List.cons.inj hw).2
    rw [udsBits_cons, List.length_append] at hmod
    have hc' : udsOf k' = c := by
      have h4 : (2 : ℤ) ^ 2 ∣ (k : ℤ) - k' := by
        apply (pow_dvd_pow 2 _).trans hmod
        have := List.length_pos_of_ne_nil (UDS.bits_ne_nil c)
        omega
      rw [← hc]
      unfold udsOf
      cases c with
      | U =>
        have h4' : (4 : ℤ) ∣ (k : ℤ) - k' := by simpa using h4
        have hU : k % 4 = 3 := by
          unfold udsOf at hc
          split_ifs at hc with h1 h2
          exact h1
        have hU' : k' % 4 = 3 := by omega
        simp [hU, hU']
      | D =>
        have h8 : (2 : ℤ) ^ 3 ∣ (k : ℤ) - k' := by
          apply (pow_dvd_pow 2 _).trans hmod
          simp only [UDS.bits, List.length_cons, List.length_nil]
          omega
        have h8' : (8 : ℤ) ∣ (k : ℤ) - k' := by simpa using h8
        have hD : k % 4 ≠ 3 ∧ k % 8 = 1 := by
          unfold udsOf at hc
          split_ifs at hc with h1 h2
          exact ⟨h1, h2⟩
        have hD1 : k' % 4 ≠ 3 := by omega
        have hD2 : k' % 8 = 1 := by omega
        simp [hD.1, hD.2, hD1, hD2]
      | S =>
        have h8 : (2 : ℤ) ^ 3 ∣ (k : ℤ) - k' := by
          apply (pow_dvd_pow 2 _).trans hmod
          simp only [UDS.bits, List.length_cons, List.length_nil]
          omega
        have h8' : (8 : ℤ) ∣ (k : ℤ) - k' := by simpa using h8
        have hS : k % 4 ≠ 3 ∧ k % 8 ≠ 1 := by
          unfold udsOf at hc
          split_ifs at hc with h1 h2
          exact ⟨h1, h2⟩
        have hS1 : k' % 4 ≠ 3 := by omega
        have hS2 : k' % 8 ≠ 1 := by omega
        simp [hS.1, hS.2, hS1, hS2]
    refine congrArg₂ List.cons hc' (ih (udsStep k) (udsStep k') (udsStep_odd k hk)
      (udsStep_odd k' hk') ?_ hrest)
    have h1 := udsStep_affine k hk
    have h1' := udsStep_affine k' hk'
    rw [hc] at h1
    rw [hc'] at h1'
    have hdiff : (2 : ℤ) ^ c.bits.length * ((udsStep k : ℤ) - udsStep k') =
        3 ^ order c.bits * ((k : ℤ) - k') := by
      rw [mul_sub, mul_sub, h1, h1']
      ring
    have hdvd : (2 : ℤ) ^ c.bits.length * 2 ^ ((udsBits w).length + 1) ∣
        (2 : ℤ) ^ c.bits.length * ((udsStep k : ℤ) - udsStep k') := by
      rw [hdiff, ← pow_add]
      exact Dvd.dvd.mul_left (by rwa [← add_assoc]) _
    exact (mul_dvd_mul_iff_left (by positivity)).mp hdvd

/-- Odd starts with the same letters w are congruent modulo 2^(|bits w| + 1). -/
theorem modEq_of_udsWord_eq (w : List UDS) (k k' : ℕ) (hk : k % 2 = 1) (hk' : k' % 2 = 1)
    (hw : udsWord k w.length = w) (hw' : udsWord k' w.length = w) :
    (2 : ℤ) ^ ((udsBits w).length + 1) ∣ (k : ℤ) - k' := by
  induction w generalizing k k' with
  | nil =>
    simp only [udsBits_nil, List.length_nil, zero_add, pow_one]
    omega
  | cons c w ih =>
    rw [List.length_cons, udsWord_succ] at hw hw'
    have hc : udsOf k = c := (List.cons.inj hw).1
    have hc' : udsOf k' = c := (List.cons.inj hw').1
    have ih' := ih (udsStep k) (udsStep k') (udsStep_odd k hk) (udsStep_odd k' hk')
      (List.cons.inj hw).2 (List.cons.inj hw').2
    have h1 := udsStep_affine k hk
    have h1' := udsStep_affine k' hk'
    rw [hc] at h1
    rw [hc'] at h1'
    have hdiff : (2 : ℤ) ^ c.bits.length * ((udsStep k : ℤ) - udsStep k') =
        3 ^ order c.bits * ((k : ℤ) - k') := by
      rw [mul_sub, mul_sub, h1, h1']
      ring
    have hdvd : (2 : ℤ) ^ (c.bits.length + ((udsBits w).length + 1)) ∣
        3 ^ order c.bits * ((k : ℤ) - k') := by
      rw [← hdiff, pow_add]
      exact mul_dvd_mul_left _ ih'
    have hcop : Int.gcd ((2 : ℤ) ^ (c.bits.length + ((udsBits w).length + 1)))
        ((3 : ℤ) ^ order c.bits) = 1 := by
      unfold Int.gcd
      rw [Int.natAbs_pow, Int.natAbs_pow]
      exact Nat.Coprime.pow _ _ (by decide)
    rw [udsBits_cons, List.length_append, add_assoc]
    exact Int.dvd_of_dvd_mul_right_of_gcd_one hdvd hcop

/-- Every letter word is the letters of some odd start. -/
theorem exists_udsWord_eq (w : List UDS) : ∃ k, k % 2 = 1 ∧ udsWord k w.length = w := by
  induction w with
  | nil =>
    exact ⟨1, rfl, rfl⟩
  | cons c w ih =>
    obtain ⟨z0, hz0, hw0⟩ := ih
    set P := 2 ^ ((udsBits w).length + 1) with hP
    have hP3 : P % 3 ≠ 0 := by
      intro h
      have h3 : 3 ∣ 2 ^ ((udsBits w).length + 1) := Nat.dvd_of_mod_eq_zero h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    have hP2 : P % 2 = 0 := by
      rw [hP, pow_succ]
      simp
    have hshift : ∀ t, (z0 + P * t) % 2 = 1 ∧ udsWord (z0 + P * t) w.length = w := by
      intro t
      have hodd : (z0 + P * t) % 2 = 1 := by
        rw [Nat.add_mod, Nat.mul_mod, hP2]
        simp [hz0]
      refine ⟨hodd, udsWord_congr w z0 (z0 + P * t) hz0 hodd ?_ hw0⟩
      refine ⟨-(t : ℤ), ?_⟩
      push_cast [hP]
      ring
    have hres : (P % 3 = 1 ∨ P % 3 = 2) ∧ (z0 % 3 = 0 ∨ z0 % 3 = 1 ∨ z0 % 3 = 2) := by
      omega
    have hcases : z0 % 3 = 2 ∨ (z0 + P * 1) % 3 = 2 ∨ (z0 + P * 2) % 3 = 2 := by
      rcases hres with ⟨hp | hp, hz | hz | hz⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    have hcases' : z0 % 3 = 1 ∨ (z0 + P * 1) % 3 = 1 ∨ (z0 + P * 2) % 3 = 1 := by
      rcases hres with ⟨hp | hp, hz | hz | hz⟩
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    have hz2 : ∃ t, (z0 + P * t) % 3 = 2 := by
      rcases hcases with h | h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    have hz1 : ∃ t, (z0 + P * t) % 3 = 1 := by
      rcases hcases' with h | h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    cases c with
    | U =>
      obtain ⟨t, ht⟩ := hz2
      obtain ⟨hodd, hw⟩ := hshift t
      set z := z0 + P * t with hzdef
      refine ⟨(2 * z - 1) / 3, by omega, ?_⟩
      have hU : ((2 * z - 1) / 3) % 4 = 3 := by omega
      have hof : udsOf ((2 * z - 1) / 3) = .U := by
        simp [udsOf, hU]
      have hst : udsStep ((2 * z - 1) / 3) = z := by
        unfold udsStep
        rw [hof]
        dsimp only
        omega
      rw [List.length_cons, udsWord_succ, hof, hst, hw]
    | D =>
      obtain ⟨t, ht⟩ := hz1
      obtain ⟨hodd, hw⟩ := hshift t
      set z := z0 + P * t with hzdef
      refine ⟨(4 * z - 1) / 3, by omega, ?_⟩
      have hD1 : ((4 * z - 1) / 3) % 4 ≠ 3 := by omega
      have hD2 : ((4 * z - 1) / 3) % 8 = 1 := by omega
      have hof : udsOf ((4 * z - 1) / 3) = .D := by
        simp [udsOf, hD1, hD2]
      have hst : udsStep ((4 * z - 1) / 3) = z := by
        unfold udsStep
        rw [hof]
        dsimp only
        omega
      rw [List.length_cons, udsWord_succ, hof, hst, hw]
    | S =>
      refine ⟨4 * z0 + 1, by omega, ?_⟩
      have hS2 : (4 * z0 + 1) % 8 ≠ 1 := by omega
      have hof : udsOf (4 * z0 + 1) = .S := by
        simp [udsOf, hS2]
      have hst : udsStep (4 * z0 + 1) = z0 := by
        unfold udsStep
        rw [hof]
        dsimp only
        omega
      rw [List.length_cons, udsWord_succ, hof, hst, hw0]

/-- The odd starts of a letter word are one class modulo 2^(|bits| + 1). -/
theorem udsWord_class (w : List UDS) :
    ∃ r, ∀ k, k % 2 = 1 →
      (udsWord k w.length = w ↔ k % 2 ^ ((udsBits w).length + 1) = r) := by
  obtain ⟨k0, hk0, hw0⟩ := exists_udsWord_eq w
  refine ⟨k0 % 2 ^ ((udsBits w).length + 1), fun k hk => ⟨fun hw => ?_, fun hr => ?_⟩⟩
  · have h := modEq_of_udsWord_eq w k k0 hk hk0 hw hw0
    have h' : (k : ℤ) ≡ k0 [ZMOD 2 ^ ((udsBits w).length + 1)] :=
      (Int.modEq_iff_dvd.mpr h).symm
    have h'' : k ≡ k0 [MOD 2 ^ ((udsBits w).length + 1)] := by
      exact_mod_cast h'
    exact h''
  · have h'' : k0 ≡ k [MOD 2 ^ ((udsBits w).length + 1)] := hr.symm
    have h' : (k0 : ℤ) ≡ k [ZMOD 2 ^ ((udsBits w).length + 1)] := by
      exact_mod_cast h''
    have h := Int.modEq_iff_dvd.mp h'
    exact udsWord_congr w k0 k hk0 hk (by simpa using (dvd_neg.mpr h)) hw0

end AcceleratedCollatz
