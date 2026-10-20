-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TNest
import AcceleratedCollatz.TParity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
  G-map: from a value 3 mod 4 to the next one, relative to a start b.
  A G-step of x (x + 1 = 2^v s, s odd) is the odd run 1^v, ending at 3^v s - 1,
  followed by the descent 0^w (1 0^w₁) … (1 0^wₘ) to the first value that is
  3 mod 4 or below b (`gStep`, `gStep_spec`). Every G-step ends.
  Odd run: `odd_run_three_mod_four`, `odd_run_last`, `odd_run_end`, `odd_run_ge`.
  G-step formula (`gStep_formula`, for any word of that shape `gWord_formula`):
    2^(W_m) G(x) + 3^m = 3^(v+m) s + Σ_{i=1..m} 3^(m-i) 2^(W_{i-1}),
  W_0 = w, W_i = W_{i-1} + 1 + w_i. First halvings (`gStep_first_halvings`):
  w = v₂(3^v s - 1). Residue mod 3 of (G(x) - 3)/4: `mod_three_after_halvings`.
  Chain of b: b, G(b), G(G(b)), …; its values before the end are 3 mod 4
  (`gChain_mod_four`), its first value below b is the drop of b (`gChain_drop`),
  and it ends iff b drops (`gChain_drop_iff`).
-/

namespace AcceleratedCollatz

/-- Descent: the first value on the T-trajectory of y that is 3 mod 4 or below b;
    0 and 1 end it as well (drop(1) = 1). -/
def gDesc (b y : ℕ) : ℕ :=
  if y % 4 = 3 ∨ y < b ∨ y ≤ 1 then y
  else if y % 2 = 0 then gDesc b (y / 2)
  else gDesc b ((3 * y + 1) / 4)
termination_by y
decreasing_by
  all_goals omega

/-- G-step of x relative to the start b: odd run, then descent. -/
def gStep (b x : ℕ) : ℕ := gDesc b (tStep^[padicValNat 2 (x + 1)] x)

/-- The word (1 0^w₁) … (1 0^wₘ) of the list [w₁, …, wₘ]. -/
def gTail : List ℕ → List Bool
  | [] => []
  | w :: ws => true :: (List.replicate w false ++ gTail ws)

/-- The word 1^v 0^w (1 0^w₁) … (1 0^wₘ) of a G-step. -/
def gWord (v w : ℕ) (ws : List ℕ) : List Bool :=
  List.replicate v true ++ (List.replicate w false ++ gTail ws)

/-- W_m: the number of halvings, from W_0 = W. -/
def gExp : ℕ → List ℕ → ℕ
  | W, [] => W
  | W, w :: ws => gExp (W + 1 + w) ws

/-- Σ_{i=1..m} 3^(m-i) 2^(W_{i-1}), from W_0 = W. -/
def gSum : ℕ → List ℕ → ℕ
  | _, [] => 0
  | W, w :: ws => 3 ^ ws.length * 2 ^ W + gSum (W + 1 + w) ws

set_option linter.hashCommand false in
#guard (List.range 10).map (fun i => (gStep 27)^[i] 27) =
  [27, 31, 91, 103, 175, 167, 283, 319, 911, 23]

-- G-steps to the drop, for b = 4k + 3, k = 0..39.
set_option linter.hashCommand false in
#guard (List.range 40).map (fun k =>
    (List.range 20).findIdx (fun i => (gStep (4 * k + 3))^[i] (4 * k + 3) < 4 * k + 3)) =
  [1, 1, 1, 1, 1, 1, 9, 8, 1, 2, 1, 8, 1, 1, 2, 8, 1, 8, 1, 1,
   1, 1, 7, 1, 1, 6, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2]

/-! ### Odd run -/

/-- x + 1 = 2^v s with s odd, for v = v₂(x + 1). -/
theorem odd_run_decomp (x : ℕ) :
    ∃ s, s % 2 = 1 ∧ x + 1 = 2 ^ padicValNat 2 (x + 1) * s := by
  obtain ⟨s, hs⟩ := pow_padicValNat_dvd (p := 2) (n := x + 1)
  refine ⟨s, ?_, hs⟩
  by_contra hodd
  have hev : s = 2 * (s / 2) := by
    omega
  have hnd := pow_succ_padicValNat_not_dvd (p := 2) (n := x + 1) (by omega)
  apply hnd
  refine ⟨s / 2, ?_⟩
  rw [pow_succ, mul_assoc, ← hev]
  exact hs

/-- Values of the odd run, except the last one, are 3 mod 4. -/
theorem odd_run_three_mod_four (x v s : ℕ) (h : x + 1 = 2 ^ v * s) (k : ℕ) (hk : k + 2 ≤ v) :
    tStep^[k] x % 4 = 3 := by
  have hrun := tStep_iterate_odd_run x v s h k (by omega)
  obtain ⟨d, hd⟩ : ∃ d, v - k = d + 2 := ⟨v - k - 2, by omega⟩
  have hc : 3 ^ k * 2 ^ (d + 2) * s = 4 * (3 ^ k * 2 ^ d * s) := by
    ring
  rw [hd, hc] at hrun
  omega

/-- The last odd value of the run is 1 mod 4. -/
theorem odd_run_last (x v s : ℕ) (h : x + 1 = 2 ^ v * s) (hs : s % 2 = 1) (hv : 1 ≤ v) :
    tStep^[v - 1] x % 4 = 1 := by
  have hrun := tStep_iterate_odd_run x v s h (v - 1) (by omega)
  have hv1 : v - (v - 1) = 1 := by
    omega
  have h3 : 3 ^ (v - 1) % 2 = 1 := by
    rw [Nat.pow_mod]
    simp
  have hc : 3 ^ (v - 1) * 2 ^ (v - (v - 1)) * s = 2 * (3 ^ (v - 1) * s) := by
    rw [hv1]
    ring
  have hodd : 3 ^ (v - 1) * s % 2 = 1 := by
    rw [Nat.mul_mod, h3, hs]
  omega

/-- The odd run ends at 3^v s - 1. -/
theorem odd_run_end (x v s : ℕ) (h : x + 1 = 2 ^ v * s) : tStep^[v] x + 1 = 3 ^ v * s := by
  have hrun := tStep_iterate_odd_run x v s h v le_rfl
  simpa using hrun

/-- The odd run ends at an even value. -/
theorem odd_run_end_even (x v s : ℕ) (h : x + 1 = 2 ^ v * s) (hs : s % 2 = 1) :
    tStep^[v] x % 2 = 0 := by
  have hend := odd_run_end x v s h
  have h3 : 3 ^ v % 2 = 1 := by
    rw [Nat.pow_mod]
    simp
  have hodd : 3 ^ v * s % 2 = 1 := by
    rw [Nat.mul_mod, h3, hs]
  omega

/-- No value of the odd run is below x. -/
theorem odd_run_ge (x v s : ℕ) (h : x + 1 = 2 ^ v * s) (k : ℕ) (hk : k ≤ v) :
    x ≤ tStep^[k] x := by
  have hrun := tStep_iterate_odd_run x v s h k hk
  have hsplit : 2 ^ v * s = 2 ^ k * (2 ^ (v - k) * s) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  have hle : 2 ^ k * (2 ^ (v - k) * s) ≤ 3 ^ k * (2 ^ (v - k) * s) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) k)
  rw [mul_assoc] at hrun
  omega

/-- The parity word of the odd run is 1^v. -/
theorem tBits_odd_run (x v s : ℕ) (h : x + 1 = 2 ^ v * s) :
    tBits x v = List.replicate v true := by
  apply tBits_replicate
  intro k hk
  have hrun := tStep_iterate_odd_run x v s h k (by omega)
  have hv : 2 ^ (v - k) = 2 * 2 ^ (v - k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hc : 3 ^ k * 2 ^ (v - k) * s = 2 * (3 ^ k * 2 ^ (v - k - 1) * s) := by
    rw [hv]
    ring
  have hodd : tStep^[k] x % 2 = 1 := by
    omega
  simp [hodd]

/-! ### Descent -/

/-- The descent from y ends after n = w + |tail| steps, with word 0^w (1 0^w₁) … (1 0^wₘ),
    at the first value that is 3 mod 4 or below b. -/
theorem gDesc_spec (b : ℕ) (hb : 1 < b) (y : ℕ) :
    ∃ n w ws, n = w + (gTail ws).length ∧ (∀ u ∈ ws, 1 ≤ u) ∧
      (y % 2 = 0 → b ≤ y → 1 ≤ w) ∧
      tBits y n = List.replicate w false ++ gTail ws ∧
      tStep^[n] y = gDesc b y ∧
      (gDesc b y % 4 = 3 ∨ gDesc b y < b) ∧
      ∀ j < n, tStep^[j] y % 4 ≠ 3 ∧ b ≤ tStep^[j] y := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    rw [gDesc]
    split_ifs with hstop heven
    · refine ⟨0, 0, [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gTail]
      · simp
      · omega
      · simp [gTail, tBits]
      · simp
      · omega
      · omega
    · obtain ⟨n, w, ws, hn, hws, -, hbits, hit, hend, hmin⟩ := ih (y / 2) (by omega)
      have hT : tStep y = y / 2 := tStep_even y (by omega)
      have hdec : decide (y % 2 = 1) = false := by
        simp [heven]
      refine ⟨n + 1, w + 1, ws, by omega, hws, by omega, ?_, ?_, hend, ?_⟩
      · rw [tBits, hT, hbits, hdec, List.replicate_succ]
        rfl
      · rw [Function.iterate_succ_apply, hT, hit]
      · intro j hj
        cases j with
        | zero =>
          simp only [Function.iterate_zero, id_eq]
          omega
        | succ j =>
          rw [Function.iterate_succ_apply, hT]
          exact hmin j (by omega)
    · obtain ⟨n, w, ws, hn, hws, -, hbits, hit, hend, hmin⟩ :=
        ih ((3 * y + 1) / 4) (by omega)
      have hT1 : tStep y = (3 * y + 1) / 2 := tStep_odd y (by omega)
      have hT2 : tStep ((3 * y + 1) / 2) = (3 * y + 1) / 4 := by
        rw [tStep_even _ (by omega)]
        omega
      have hodd1 : y % 2 = 1 := by
        omega
      have hodd2 : ¬ (3 * y + 1) / 2 % 2 = 1 := by
        omega
      have hdec1 : decide (y % 2 = 1) = true := decide_eq_true hodd1
      have hdec2 : decide ((3 * y + 1) / 2 % 2 = 1) = false := decide_eq_false hodd2
      refine ⟨n + 2, 0, (w + 1) :: ws, ?_, ?_, by omega, ?_, ?_, hend, ?_⟩
      · simp only [gTail, List.length_cons, List.length_append, List.length_replicate]
        omega
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · omega
        · exact hws u hu'
      · rw [tBits, hT1, tBits, hT2, hbits, hdec1, hdec2]
        simp [gTail, List.replicate_succ]
      · rw [Function.iterate_succ_apply, hT1, Function.iterate_succ_apply, hT2, hit]
      · intro j hj
        cases j with
        | zero =>
          simp only [Function.iterate_zero, id_eq]
          omega
        | succ j =>
          cases j with
          | zero =>
            rw [Function.iterate_succ_apply, hT1]
            simp only [Function.iterate_zero, id_eq]
            omega
          | succ j =>
            rw [Function.iterate_succ_apply, hT1, Function.iterate_succ_apply, hT2]
            exact hmin j (by omega)

/-- A G-step of x ≥ b ends: after n > v steps, with word 1^v 0^w (1 0^w₁) … (1 0^wₘ),
    all w's ≥ 1, at the first value from step v on that is 3 mod 4 or below b. -/
theorem gStep_spec (b x : ℕ) (hb : 1 < b) (hbx : b ≤ x) :
    ∃ n w ws, n = padicValNat 2 (x + 1) + (w + (gTail ws).length) ∧ 1 ≤ w ∧
      (∀ u ∈ ws, 1 ≤ u) ∧
      tBits x n = gWord (padicValNat 2 (x + 1)) w ws ∧
      tStep^[n] x = gStep b x ∧
      (gStep b x % 4 = 3 ∨ gStep b x < b) ∧
      ∀ j < n, b ≤ tStep^[j] x ∧ (padicValNat 2 (x + 1) ≤ j → tStep^[j] x % 4 ≠ 3) := by
  obtain ⟨s, hs, hx⟩ := odd_run_decomp x
  generalize hv : padicValNat 2 (x + 1) = v at hx
  have heven := odd_run_end_even x v s hx hs
  have hge := odd_run_ge x v s hx
  obtain ⟨n, w, ws, hn, hws, hw, hbits, hit, hend, hmin⟩ := gDesc_spec b hb (tStep^[v] x)
  have hw1 : 1 ≤ w := hw heven (le_trans hbx (hge v le_rfl))
  refine ⟨v + n, w, ws, by omega, hw1, hws, ?_, ?_, ?_, ?_⟩
  · rw [tBits_add, tBits_odd_run x v s hx, hbits]
    rfl
  · rw [Nat.add_comm, Function.iterate_add_apply, hit, gStep, hv]
  · rw [gStep, hv]
    exact hend
  · intro j hj
    rcases Nat.lt_or_ge j v with hlt | hjv
    · exact ⟨le_trans hbx (hge j (by omega)), by omega⟩
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjv
      rw [Nat.add_comm, Function.iterate_add_apply]
      have hi := hmin i (by omega)
      exact ⟨hi.2, fun _ => hi.1⟩

/-! ### The G-step formula -/

/-- w halvings: 2^w T^w(y) = y. -/
theorem halvings (w : ℕ) :
    ∀ y, tBits y w = List.replicate w false → 2 ^ w * tStep^[w] y = y := by
  induction w with
  | zero =>
    intro y _
    simp
  | succ w ih =>
    intro y hbits
    rw [tBits, List.replicate_succ, List.cons.injEq] at hbits
    have heven : y % 2 ≠ 1 := by
      simpa using hbits.1
    have hT : tStep y = y / 2 := tStep_even y heven
    have hih := ih (tStep y) hbits.2
    have hc : 2 ^ w * 2 * tStep^[w] (tStep y) = 2 * (2 ^ w * tStep^[w] (tStep y)) := by
      ring
    rw [Function.iterate_succ_apply, pow_succ, hc, hih, hT]
    omega

/-- Along (1 0^w₁) … (1 0^wₘ): 2^(W_m) T^n(y) = 3^m 2^W y + Σ. -/
theorem gTail_formula (ws : List ℕ) : ∀ y W, tBits y (gTail ws).length = gTail ws →
    2 ^ gExp W ws * tStep^[(gTail ws).length] y = 3 ^ ws.length * (2 ^ W * y) + gSum W ws := by
  induction ws with
  | nil =>
    intro y W _
    simp [gTail, gExp, gSum]
  | cons w ws ih =>
    intro y W hbits
    have hlen : (gTail (w :: ws)).length = w + (gTail ws).length + 1 := by
      simp only [gTail, List.length_cons, List.length_append, List.length_replicate]
    rw [hlen] at hbits ⊢
    rw [tBits, gTail, List.cons.injEq, tBits_add] at hbits
    have hodd : y % 2 = 1 := by
      simpa using hbits.1
    have hT : tStep y = (3 * y + 1) / 2 := tStep_odd y hodd
    have hparts := List.append_inj hbits.2 (by simp)
    have hhalf := halvings w (tStep y) hparts.1
    have hih := ih (tStep^[w] (tStep y)) (W + 1 + w) hparts.2
    have h2 : 2 * tStep y = 3 * y + 1 := by
      omega
    have hy' : 2 ^ (W + 1 + w) * tStep^[w] (tStep y) = 2 ^ W * (3 * y + 1) := by
      have hc : 2 ^ (W + 1 + w) * tStep^[w] (tStep y) =
          2 ^ W * (2 * (2 ^ w * tStep^[w] (tStep y))) := by
        ring
      rw [hc, hhalf, h2]
    rw [Function.iterate_succ_apply, Nat.add_comm w, Function.iterate_add_apply]
    rw [gExp, gSum, hih, hy', List.length_cons]
    ring

/-- The value at the end of a G-word:
    2^(W_m) T^n(x) + 3^m = 3^(v+m) s + Σ_{i=1..m} 3^(m-i) 2^(W_{i-1}). -/
theorem gWord_formula (x v s w : ℕ) (ws : List ℕ) (h : x + 1 = 2 ^ v * s)
    (hbits : tBits x (v + (w + (gTail ws).length)) = gWord v w ws) :
    2 ^ gExp w ws * tStep^[v + (w + (gTail ws).length)] x + 3 ^ ws.length =
      3 ^ (v + ws.length) * s + gSum w ws := by
  rw [tBits_add, gWord] at hbits
  have hdesc := (List.append_inj hbits (by simp)).2
  rw [tBits_add] at hdesc
  have hparts := List.append_inj hdesc (by simp)
  have hend := odd_run_end x v s h
  have hhalf := halvings w (tStep^[v] x) hparts.1
  have htail := gTail_formula ws (tStep^[w] (tStep^[v] x)) w hparts.2
  rw [Nat.add_comm v, Function.iterate_add_apply, Nat.add_comm w, Function.iterate_add_apply]
  rw [htail, hhalf, pow_add, mul_comm (3 ^ v), mul_assoc, ← hend]
  ring

/-- G-step formula: 2^(W_m) G(x) + 3^m = 3^(v+m) s + Σ_{i=1..m} 3^(m-i) 2^(W_{i-1}),
    for x + 1 = 2^v s, with the w's of the G-step, all ≥ 1. -/
theorem gStep_formula (b x s : ℕ) (hb : 1 < b) (hbx : b ≤ x)
    (hx : x + 1 = 2 ^ padicValNat 2 (x + 1) * s) :
    ∃ w ws, 1 ≤ w ∧ (∀ u ∈ ws, 1 ≤ u) ∧
      2 ^ gExp w ws * gStep b x + 3 ^ ws.length =
        3 ^ (padicValNat 2 (x + 1) + ws.length) * s + gSum w ws := by
  obtain ⟨n, w, ws, hn, hw, hws, hbits, hit, -, -⟩ := gStep_spec b x hb hbx
  subst hn
  refine ⟨w, ws, hw, hws, ?_⟩
  rw [← hit]
  exact gWord_formula x _ s w ws hx hbits

/-- Halvings down to an odd value: their number is the 2-adic valuation. -/
theorem halvings_eq_padicValNat (y w : ℕ) (hbits : tBits y w = List.replicate w false)
    (hodd : tStep^[w] y % 2 = 1) : padicValNat 2 y = w := by
  have hhalf := halvings w y hbits
  have hne : tStep^[w] y ≠ 0 := by
    omega
  have hnd : ¬ 2 ∣ tStep^[w] y := by
    omega
  rw [← hhalf, padicValNat.mul (by positivity) hne, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hnd]
  rfl

/-- First halvings: the halvings after the odd run number v₂(3^v s - 1),
    when they end at an odd value. -/
theorem gStep_first_halvings (x v s w : ℕ) (h : x + 1 = 2 ^ v * s)
    (hbits : tBits (tStep^[v] x) w = List.replicate w false)
    (hodd : tStep^[w] (tStep^[v] x) % 2 = 1) : padicValNat 2 (3 ^ v * s - 1) = w := by
  have hend := odd_run_end x v s h
  have hy : 3 ^ v * s - 1 = tStep^[v] x := by
    omega
  rw [hy]
  exact halvings_eq_padicValNat _ w hbits hodd

theorem two_pow_succ_mod_three (z : ℕ) : 2 ^ (z + 1) % 3 = if z % 2 = 0 then 2 else 1 := by
  induction z with
  | zero =>
    rfl
  | succ z ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs
    · omega
    · rfl
    · rfl
    · omega

/-- A value 4k + 3 reached z halvings after an odd step: k ≡ (-1)^(z+1) mod 3. -/
theorem mod_three_after_halvings (y z k : ℕ) (hy : y % 2 = 1)
    (hbits : tBits (tStep y) z = List.replicate z false)
    (hk : tStep^[z] (tStep y) = 4 * k + 3) : k % 3 = if z % 2 = 0 then 2 else 1 := by
  have hhalf := halvings z (tStep y) hbits
  have hT : tStep y = (3 * y + 1) / 2 := tStep_odd y hy
  rw [hk] at hhalf
  have h2 : 2 ^ (z + 1) * (4 * k + 3) = 3 * y + 1 := by
    rw [pow_succ, mul_assoc, mul_comm 2, ← mul_assoc, hhalf, hT]
    omega
  have hmod : 2 ^ (z + 1) % 3 * ((4 * k + 3) % 3) % 3 = 1 := by
    rw [← Nat.mul_mod, h2]
    omega
  have hk3 : (4 * k + 3) % 3 = k % 3 := by
    omega
  rw [hk3, two_pow_succ_mod_three] at hmod
  split_ifs at hmod ⊢
  · omega
  · omega

/-! ### Chain -/

/-- While the chain of b stays at or above b, it runs along the T-trajectory of b,
    which stays at or above b as well. -/
theorem gChain_iterate (b : ℕ) (hb : b % 4 = 3) (c : ℕ)
    (hmin : ∀ i < c, b ≤ (gStep b)^[i] b) :
    ∃ n, c ≤ n ∧ tStep^[n] b = (gStep b)^[c] b ∧ (∀ j < n, b ≤ tStep^[j] b) ∧
      (c ≠ 0 → (gStep b)^[c] b % 4 = 3 ∨ (gStep b)^[c] b < b) := by
  induction c with
  | zero =>
    exact ⟨0, le_rfl, rfl, by omega, by omega⟩
  | succ c ih =>
    obtain ⟨n, hcn, hit, hge, -⟩ := ih (fun i hi => hmin i (by omega))
    obtain ⟨n', w, ws, hn', hw, -, -, hit', hend, hmin'⟩ :=
      gStep_spec b ((gStep b)^[c] b) (by omega) (hmin c (by omega))
    refine ⟨n' + n, by omega, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hit, hit', Function.iterate_succ_apply']
    · intro j hj
      rcases Nat.lt_or_ge j n with hlt | hjn
      · exact hge j hlt
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjn
        rw [Nat.add_comm, Function.iterate_add_apply, hit]
        exact (hmin' i (by omega)).1
    · intro _
      rw [Function.iterate_succ_apply']
      exact hend

/-- Chain values before the end are 3 mod 4. -/
theorem gChain_mod_four (b : ℕ) (hb : b % 4 = 3) (c : ℕ)
    (hmin : ∀ i ≤ c, b ≤ (gStep b)^[i] b) : (gStep b)^[c] b % 4 = 3 := by
  obtain ⟨n, -, -, -, hend⟩ := gChain_iterate b hb c (fun i hi => hmin i (by omega))
  have hc := hmin c le_rfl
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · exact hb
  · rcases hend (by omega) with h3 | hlt
    · exact h3
    · omega

/-- The first chain value below b is the drop of b. -/
theorem gChain_drop (b c : ℕ) (hb : b % 4 = 3) (hc : (gStep b)^[c] b < b)
    (hmin : ∀ i < c, b ≤ (gStep b)^[i] b) :
    ∃ n, IsTDrop b n ∧ tStep^[n] b = (gStep b)^[c] b := by
  obtain ⟨n, hcn, hit, hge, -⟩ := gChain_iterate b hb c hmin
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hb1 : b ≠ 1 := by
    omega
  refine ⟨n, ?_, hit⟩
  simp only [IsTDrop, hb1, ite_false]
  refine ⟨by omega, ?_, ?_⟩
  · change tStep^[n] b < tStep^[0] b
    rw [hit]
    exact hc
  · intro k _ hk
    exact hge k hk

/-- If b drops at step n, its chain ends within n G-steps. -/
theorem gChain_of_drop (b n : ℕ) (hb : b % 4 = 3) (hd : IsTDrop b n) :
    ∃ c ≤ n, (gStep b)^[c] b < b := by
  by_contra hno
  push Not at hno
  obtain ⟨m, hm, -, hge, -⟩ := gChain_iterate b hb (n + 1) (fun i hi => hno i (by omega))
  have hb1 : b ≠ 1 := by
    omega
  simp only [IsTDrop, hb1, ite_false] at hd
  have hlt : tStep^[n] b < b := hd.2.1
  have := hge n (by omega)
  omega

/-- b drops iff its chain ends. -/
theorem gChain_drop_iff (b : ℕ) (hb : b % 4 = 3) :
    (∃ n, IsTDrop b n) ↔ ∃ c, (gStep b)^[c] b < b := by
  constructor
  · rintro ⟨n, hd⟩
    obtain ⟨c, -, hc⟩ := gChain_of_drop b n hb hd
    exact ⟨c, hc⟩
  · intro hex
    classical
    obtain ⟨n, hd, -⟩ := gChain_drop b (Nat.find hex) hb (Nat.find_spec hex)
      (fun i hi => not_lt.mp (Nat.find_min hex hi))
    exact ⟨n, hd⟩

end AcceleratedCollatz
