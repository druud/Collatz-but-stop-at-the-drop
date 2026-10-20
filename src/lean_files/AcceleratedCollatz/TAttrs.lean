-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainParse
import AcceleratedCollatz.TCorrespondence
import AcceleratedCollatz.TPersistent

/-!
  Map view: every attribute of an admissible PV, computed from its key.
  Key = core, the PV without its trailing zeros: [] for the Order-0 PV, else a
  persistent vector followed by 1 (`IsKey`). `keyPV` and `core` are inverse
  (`keyPV_core`, `core_keyPV`), and the PV of a key is admissible
  (`admissible_keyPV`, `isKey_core`).
  `classIdC`: the class id by inverse steps (`classRes_spec`), equal to `classId`
  (`classIdC_eq`).
  `attrs k`: p2, p3, class id x, drop, rank, rho, chain blocks, (d, c) list;
  `attrs_p2`, `attrs_x`, `attrs_drop`, `attrs_chain`.
-/

namespace AcceleratedCollatz

/-- PV of a key: the key followed by zeros up to length p2(Order). -/
def keyPV (k : List Bool) : List Bool :=
  k ++ List.replicate (p2_of (order k) - k.length) false

/-- Keys: [] (Order 0), or a persistent vector followed by 1. -/
def IsKey (k : List Bool) : Prop :=
  k = [] ∨ ∃ p, Persistent p ∧ k = p ++ [true]

/-- Inverse steps: the residue below 2^|s| with parity sequence s. -/
def classRes : List Bool → ℕ
  | [] => 0
  | false :: t => 2 * classRes t
  | true :: t =>
    2 * (classRes t + (classRes t + 1) * 2 ^ (t.length + 1) % 3 * 2 ^ t.length) / 3

/-- Class id of s, computed by inverse steps. -/
def classIdC (s : List Bool) : ℕ :=
  if classRes s = 0 then 2 ^ s.length else classRes s

/-- Attributes of a key. -/
structure Attrs where
  /-- Length of the PV. -/
  p2 : ℕ
  /-- Order of the PV. -/
  p3 : ℕ
  /-- Class id. -/
  x : ℕ
  /-- Value after the PV: T^p2(x). -/
  drop : ℕ
  /-- 0-based rank within the Order. -/
  rank : ℕ
  /-- rho of the PV. -/
  rho : ℕ
  /-- Chain blocks. -/
  chain : List (List Bool)
  /-- (d, c) list. -/
  code : List (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- Attributes of the key k, all computed from k. -/
def attrs (k : List Bool) : Attrs where
  p2 := p2_of (order k)
  p3 := order k
  x := classIdC (keyPV k)
  drop := (3 ^ order k * classIdC (keyPV k) + rho (keyPV k)) / 2 ^ p2_of (order k)
  rank := rank (order k) (keyPV k)
  rho := rho (keyPV k)
  chain := chainOf (keyPV k)
  code := codeOf (keyPV k)

set_option linter.hashCommand false in
#guard attrs [true, true, false, true, true] =
  { p2 := 7, p3 := 4, x := 59, drop := 38, rank := 0, rho := 85,
    chain := [[true, false], [true, true, false, false]], code := [(1, 0), (2, 0)] }

set_option linter.hashCommand false in
#guard attrs [true, true, true, false, true, true, true] =
  { p2 := 10, p3 := 6, x := 999, drop := 712, rank := 5, rho := 817,
    chain := [[true, true, false, true, true, true, false, false]], code := [(5, 1)] }

set_option linter.hashCommand false in
#guard ((attrs []).x, (attrs []).drop, (attrs [true]).x, (attrs [true]).drop) = (2, 1, 1, 1)

/-! ### Key and PV -/

theorem order_keyPV (k : List Bool) : order (keyPV k) = order k := by
  unfold keyPV
  rw [order_append, order_replicate_false, Nat.add_zero]

theorem keyPV_append_true (p : List Bool) :
    keyPV (p ++ [true]) = complete (order p) p := by
  unfold keyPV complete
  rw [order_append_true, List.length_append, List.length_singleton, List.append_assoc,
    Nat.sub_sub]
  rfl

/-- The PV of a key is admissible. -/
theorem admissible_keyPV {k : List Bool} (hk : IsKey k) : Admissible (keyPV k) := by
  rcases hk with rfl | ⟨p, hp, rfl⟩
  · exact admissible_singleton_false
  · rw [keyPV_append_true]
    exact (admissible_complete p hp).1

theorem length_keyPV {k : List Bool} (hk : IsKey k) : (keyPV k).length = p2_of (order k) := by
  rw [admissible_length _ (admissible_keyPV hk), order_keyPV]

theorem order_core (s : List Bool) : order (core s) = order s := by
  have h := congrArg order (core_append_zeros s)
  rw [order_append, order_replicate_false, Nat.add_zero] at h
  exact h.symm

/-- The key of an admissible PV gives the PV back. -/
theorem keyPV_core {s : List Bool} (hA : Admissible s) : keyPV (core s) = s := by
  unfold keyPV
  rw [order_core, ← admissible_length s hA]
  exact (core_append_zeros s).symm

/-- The core of an admissible PV is a key. -/
theorem isKey_core {s : List Bool} (hA : Admissible s) : IsKey (core s) := by
  rcases core_eq_nil_or_last_true s with h0 | ⟨p, hp⟩
  · exact Or.inl h0
  · refine Or.inr ⟨p, ?_, hp⟩
    have hs := core_append_zeros s
    rw [hp] at hs
    have hne : s ≠ [] := by
      intro h
      rw [h] at hs
      simp at hs
    have hlast := admissible_last_false s hA hne
    have hlen : p.length + 1 < s.length := by
      by_contra hge
      have hz : s.length - (p ++ [true]).length = 0 := by
        rw [List.length_append, List.length_singleton]
        omega
      rw [hz, List.replicate_zero, List.append_nil] at hs
      have hl : s.getLast hne = true := by
        simp [hs]
      rw [hl] at hlast
      exact absurd hlast (by decide)
    intro m hm1 hm
    have htake : p.take m = s.take m := by
      rw [hs, List.append_assoc, List.take_append_of_le_length hm]
    rw [htake]
    exact hA.prefix_gt m hm1 (by omega)

theorem core_append_true_replicate (p : List Bool) (z : ℕ) :
    core (p ++ [true] ++ List.replicate z false) = p ++ [true] := by
  simp [core]

/-- The PV of a key has that key as its core. -/
theorem core_keyPV {k : List Bool} (hk : IsKey k) : core (keyPV k) = k := by
  rcases hk with rfl | ⟨p, -, rfl⟩
  · rfl
  · exact core_append_true_replicate p _

/-! ### Class id by inverse steps -/

theorem two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero =>
    exact Or.inl rfl
  | succ n ih =>
    rw [pow_succ]
    omega

/-- `classRes s` is the residue below 2^|s| with parity sequence s. -/
theorem classRes_spec (s : List Bool) :
    classRes s < 2 ^ s.length ∧ tBits (classRes s) s.length = s := by
  induction s with
  | nil =>
    exact ⟨by decide, rfl⟩
  | cons b t ih =>
    obtain ⟨hlt, hbits⟩ := ih
    cases b with
    | false =>
      have hT : tStep (2 * classRes t) = classRes t := by
        rw [tStep_even _ (by omega)]
        omega
      have hdec : decide (2 * classRes t % 2 = 1) = false := decide_eq_false (by omega)
      refine ⟨?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        change 2 * classRes t < _
        omega
      · change tBits (2 * classRes t) (t.length + 1) = _
        rw [tBits, hT, hbits, hdec]
    | true =>
      obtain ⟨i, hi⟩ : ∃ i, i = (classRes t + 1) * 2 ^ (t.length + 1) % 3 := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y, y = classRes t + i * 2 ^ t.length := ⟨_, rfl⟩
      have hx : classRes (true :: t) = 2 * y / 3 := by
        rw [hy, hi]
        rfl
      have hi2 : i * 2 ^ t.length ≤ 2 * 2 ^ t.length :=
        Nat.mul_le_mul_right _ (by omega)
      have hiP : i * 2 ^ (t.length + 1) % 3 = i % 3 * (2 ^ (t.length + 1) % 3) % 3 :=
        Nat.mul_mod _ _ _
      have hi' : i = (classRes t + 1) % 3 * (2 ^ (t.length + 1) % 3) % 3 := by
        rw [hi]
        exact Nat.mul_mod _ _ _
      have h2y : 2 * y = 2 * classRes t + i * 2 ^ (t.length + 1) := by
        rw [hy, pow_succ]
        ring
      have hmod : 2 * y % 3 = 1 := by
        rcases two_pow_mod_three (t.length + 1) with hc | hc
        · rw [hc] at hiP hi'
          omega
        · rw [hc] at hiP hi'
          omega
      have hodd : 2 * y / 3 % 2 = 1 := by
        omega
      have hT : tStep (2 * y / 3) = y := by
        rw [tStep_odd _ hodd]
        omega
      have hymod : y % 2 ^ t.length = classRes t := by
        rw [hy, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
      have hybits : tBits y t.length = t := by
        rw [← tBits_mod, hymod, hbits]
      have hdec : decide (2 * y / 3 % 2 = 1) = true := decide_eq_true hodd
      rw [hx]
      refine ⟨?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        omega
      · rw [List.length_cons, tBits, hT, hybits, hdec]

theorem classIdC_eq (s : List Bool) : classIdC s = classId s := by
  obtain ⟨hlt, hbits⟩ := classRes_spec s
  have hpow : 0 < 2 ^ s.length := by
    positivity
  apply classId_unique
  · unfold classIdC
    split_ifs with h0
    · exact hpow
    · omega
  · unfold classIdC
    split_ifs with h0
    · exact le_rfl
    · exact hlt.le
  · unfold classIdC
    split_ifs with h0
    · rw [← tBits_mod, Nat.mod_self, ← h0, hbits]
    · exact hbits

/-! ### Attributes -/

theorem attrs_p2 {k : List Bool} (hk : IsKey k) : (attrs k).p2 = (keyPV k).length :=
  (length_keyPV hk).symm

theorem attrs_x (k : List Bool) : (attrs k).x = classId (keyPV k) :=
  classIdC_eq _

/-- The drop attribute is the value after the PV, T^p2(x). -/
theorem attrs_drop {k : List Bool} (hk : IsKey k) :
    (attrs k).drop = tStep^[(attrs k).p2] (attrs k).x := by
  have hlen := length_keyPV hk
  have hbits := tBits_classId (keyPV k)
  have hform := tStep_iterate_nForm (keyPV k).length (classId (keyPV k))
  rw [hbits, order_keyPV, hlen] at hform
  change (3 ^ order k * classIdC (keyPV k) + rho (keyPV k)) / 2 ^ p2_of (order k) =
    tStep^[p2_of (order k)] (classIdC (keyPV k))
  rw [classIdC_eq, ← hform]
  exact Nat.mul_div_cancel_left _ (by positivity)

/-- The chain attribute is the chain decomposition of the PV. -/
theorem attrs_chain {k : List Bool} (hk : IsKey k) (hord : 1 ≤ order k) :
    (attrs k).chain ∈ chainBlocks (order k - 1) ∧ chainWord (attrs k).chain = keyPV k := by
  have hmem : keyPV k ∈ admSet (order k - 1 + 1) := by
    rw [mem_admSet, order_keyPV]
    exact ⟨admissible_keyPV hk, by omega⟩
  exact chainWord_chainOf hmem

end AcceleratedCollatz
