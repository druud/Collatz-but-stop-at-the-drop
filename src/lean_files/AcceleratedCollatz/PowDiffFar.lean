-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.PowDiffWalk

/-!
# Both walk bounds for any certified range

`rhinBoundUpTo_one_two` (TRhinCheck) and `lowAt_upTo` (PowDiffWalk) hold up to Order 10^60,
from one kernel walk each at K = 2^400. Their proofs use the walk only through its result,
so here they are stated for any bracket K = 2^m from B bits, any bound N and any fuel f:
a walk that returns true gives the upper side 3^n ≤ p2(n)^2 (2^p2(n) - 3^n)
(`rhinBoundUpTo_of_walk`) and the lower side 2^(Q-1) (1 + Q^2) ≤ Q^2 3^n
(`lowAt_of_walk`) for every Order 1 ≤ n ≤ N, and both together
min(2^i, 3^j) ≤ p2(j)^2 |2^i - 3^j| for 1 ≤ j ≤ N (`min_le_of_walks`). The kernel runs of
larger walks, in stretches (`walkTo`, `WalkedTo`), are in `PowDiffFarRhin1` to
`PowDiffFarLow4`, joined in `PowDiffFarCheck`.
-/

namespace PowDiff

open AcceleratedCollatz

/-- Upper checks at K = 2^m (bracket from B bits) on every node up to a node k whose
    denominators sum past N give `RhinBound 1 2` for every Order 1 ≤ n ≤ N. -/
theorem rhinBoundUpTo_of_checked {B m N k : ℕ}
    (hNk : N < (sbWalk k).loDen + (sbWalk k).hiDen)
    (hall : ∀ i, i ≤ k →
      rhinOK (2 ^ m) (log2Hi 3 B m) (sbWalk i).hiNum (sbWalk i).hiDen = true) :
    RhinBoundUpTo 1 2 N := by
  apply rhinBoundUpTo_of_records
  intro a ha1 haN hR
  have hbr := log2Bracket_pow3 B m
  have hK : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · exfalso
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have : k = 0 := by omega
        subst this
        have : (sbWalk 0).loDen + (sbWalk 0).hiDen = 1 := by
          decide +kernel
        omega
      · have : k = 1 := by omega
        subst this
        have : (sbWalk 1).loDen + (sbWalk 1).hiDen = 1 := by
          decide +kernel
        omega
    · exact hge
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
  have hp21 : p2Q 3 1 = 2 := p2_of_one
  have hlt : a < (sbWalkQ 3 (p2Q 3 1 + j)).loDen + (sbWalkQ 3 (p2Q 3 1 + j)).hiDen := by
    rw [hp21]
    change a < (sbWalk (2 + j)).loDen + (sbWalk (2 + j)).hiDen
    omega
  obtain ⟨i, hij, hi⟩ := exists_sbWalkQ_hiDen (by decide) le_rfl j a ha1 hlt hR
  rw [hp21] at hi
  change (sbWalk (2 + i)).hiDen = a at hi
  have hok := hall (2 + i) (by omega)
  have hnum := sbWalk_hiNum (k := 2 + i) (by omega)
  rw [hnum, hi] at hok
  exact rhinOK_spec hbr.2 hK hok

/-- A successful upper walk at K = 2^m (bracket from B bits) up to N gives `RhinBound 1 2`
    for every Order 1 ≤ n ≤ N. -/
theorem rhinBoundUpTo_of_walk {B m N f : ℕ}
    (hw : rhinWalk (2 ^ m) (log2Lo 3 B m) (log2Hi 3 B m) N f (sbWalk 0) = true) :
    RhinBoundUpTo 1 2 N := by
  obtain ⟨k, -, hNk, hall⟩ :=
    rhinWalk_spec (log2Bracket_pow3 B m) Nat.one_le_two_pow f 0 hw
  exact rhinBoundUpTo_of_checked hNk fun i hi => hall i (Nat.zero_le i) hi

/-- Lower checks at K = 2^m (bracket from B bits) on every node up to a node k whose
    denominators sum past N give the lower side for every Order 1 ≤ n ≤ N. -/
theorem lowAt_of_checked {B m N k : ℕ}
    (hNk : N < (sbWalk k).loDen + (sbWalk k).hiDen)
    (hall : ∀ i, i ≤ k →
      lowOK (2 ^ m) (log2Lo 3 B m) (sbWalk i).loNum (sbWalk i).loDen = true) :
    ∀ n, 1 ≤ n → n ≤ N → LowAt n := by
  apply lowAt_of_records
  intro c hc1 hcN hR
  have hbr := log2Bracket_pow3 B m
  have hK : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · exfalso
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have : k = 0 := by omega
        subst this
        have : (sbWalk 0).loDen + (sbWalk 0).hiDen = 1 := by
          decide +kernel
        omega
      · have : k = 1 := by omega
        subst this
        have : (sbWalk 1).loDen + (sbWalk 1).hiDen = 1 := by
          decide +kernel
        omega
    · exact hge
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
  have hp21 : p2Q 3 1 = 2 := p2_of_one
  have hlt : c < (sbWalkQ 3 (p2Q 3 1 + j)).loDen + (sbWalkQ 3 (p2Q 3 1 + j)).hiDen := by
    rw [hp21]
    change c < (sbWalk (2 + j)).loDen + (sbWalk (2 + j)).hiDen
    omega
  obtain ⟨i, hij, hi⟩ := exists_sbWalkQ_loDen (by decide) le_rfl j c hc1 hlt hR
  rw [hp21] at hi
  change (sbWalk (2 + i)).loDen = c at hi
  have hok := hall (2 + i) (by omega)
  have hnum := sbWalk_loNum (k := 2 + i) (by omega)
  rw [hi] at hnum
  have hs := lowOK_spec hbr.1 hK hok
  rw [hi] at hs
  unfold LowAt
  rw [← hnum, Nat.add_sub_cancel]
  exact hs

/-- A successful lower walk at K = 2^m (bracket from B bits) up to N gives the lower side
    for every Order 1 ≤ n ≤ N. -/
theorem lowAt_of_walk {B m N f : ℕ}
    (hw : lowWalk (2 ^ m) (log2Lo 3 B m) (log2Hi 3 B m) N f (sbWalk 0) = true) :
    ∀ n, 1 ≤ n → n ≤ N → LowAt n := by
  obtain ⟨k, -, hNk, hall⟩ :=
    lowWalk_spec (log2Bracket_pow3 B m) Nat.one_le_two_pow f 0 hw
  exact lowAt_of_checked hNk fun i hi => hall i (Nat.zero_le i) hi

/-- Both sides up to N: min(2^i, 3^j) ≤ p2(j)^2 |2^i - 3^j| for 1 ≤ j ≤ N. -/
theorem min_le_of_walks {N i j : ℕ} (hU : RhinBoundUpTo 1 2 N)
    (hL : ∀ n, 1 ≤ n → n ≤ N → LowAt n) (hj1 : 1 ≤ j) (hj : j ≤ N) :
    min (2 ^ i) (3 ^ j) ≤ p2_of j ^ 2 * D (2 ^ i) (3 ^ j) := by
  set Q := p2_of j with hQ
  have hlo : 2 ^ (Q - 1) ≤ 3 ^ j := p2_of_spec_lower j
  have hhi : 3 ^ j < 2 ^ Q := p2_of_spec j
  have hne : 2 ^ i ≠ 3 ^ j := two_pow_ne_three_pow_right hj1
  unfold D
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hi : i ≤ Q - 1 := by
      by_contra hc
      have : 2 ^ Q ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h2 : 2 ^ i ≤ 2 ^ (Q - 1) := Nat.pow_le_pow_right (by decide) hi
    have hL' := hL j hj1 hj
    unfold LowAt at hL'
    rw [← hQ] at hL'
    rw [min_eq_left h.le, Nat.sub_eq_zero_of_le h.le, Nat.zero_add, sq]
    have hm : Q * Q * (3 ^ j - 2 ^ (Q - 1)) ≤ Q * Q * (3 ^ j - 2 ^ i) :=
      Nat.mul_le_mul_left _ (by omega)
    have hm2 : 2 ^ (Q - 1) ≤ Q * Q * (3 ^ j - 2 ^ (Q - 1)) := by
      rw [Nat.mul_sub]
      have : 2 ^ (Q - 1) * (1 + Q * Q) = 2 ^ (Q - 1) + Q * Q * 2 ^ (Q - 1) := by ring
      omega
    omega
  · have hi : Q ≤ i := by
      by_contra hc
      have : 2 ^ i ≤ 2 ^ (Q - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h2 : 2 ^ Q ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
    have hU' := hU j hj1 hj
    rw [← hQ, Nat.one_mul] at hU'
    rw [min_eq_right h.le, Nat.sub_eq_zero_of_le h.le, Nat.add_zero]
    calc 3 ^ j ≤ Q ^ 2 * (2 ^ Q - 3 ^ j) := hU'
      _ ≤ Q ^ 2 * (2 ^ i - 3 ^ j) := Nat.mul_le_mul_left _ (by omega)

/-! ### Walks in stretches

A long kernel walk keeps its memory until it ends. `walkTo` checks the nodes from a given
node up to a given end node, so a walk can be cut into stretches, each in its own file:
`walkedTo_start` takes the first stretch from the root, `walkedTo_next` appends a stretch
at the end node of the walk so far. -/

/-- The certified walk from s that checks `ok` at every node until it reaches the node e. -/
def walkTo (ok : SBNode → Bool) (K a b : ℕ) (e : SBNode) : ℕ → SBNode → Bool
  | 0, _ => false
  | f + 1, s =>
    ok s &&
      (decide (s = e) ||
        match sbCertStep K a b s with
        | some t => walkTo ok K a b e f t
        | none => false)

/-- A successful stretch from node j reaches the node e at some k ≥ j, and every node from
    j to k passes the check. -/
theorem walkTo_spec {ok : SBNode → Bool} {K a b : ℕ} {e : SBNode} (h : Log2Bracket K a b)
    (hK : 1 ≤ K) :
    ∀ f j, walkTo ok K a b e f (sbWalk j) = true →
      ∃ k, j ≤ k ∧ sbWalk k = e ∧ ∀ i, j ≤ i → i ≤ k → ok (sbWalk i) = true := by
  intro f
  induction f with
  | zero =>
    intro j hw
    exact absurd hw (by simp [walkTo])
  | succ f ih =>
    intro j hw
    rw [walkTo, Bool.and_eq_true, Bool.or_eq_true] at hw
    obtain ⟨hok, hrest⟩ := hw
    rcases hrest with he | hstep
    · refine ⟨j, le_rfl, of_decide_eq_true he, fun i hi1 hi2 => ?_⟩
      have : i = j := by omega
      rw [this]
      exact hok
    · cases ht : sbCertStep K a b (sbWalk j) with
      | none =>
        rw [ht] at hstep
        exact absurd hstep (by simp)
      | some t =>
        rw [ht] at hstep
        have hs : 1 ≤ (sbWalk j).loDen := one_le_sbWalkQ_loDen 3 j
        have htw : t = sbWalk (j + 1) := by
          rw [sbCertStep_eq h hK hs ht]
          exact (sbWalkQ_succ 3 j).symm
        rw [htw] at hstep
        obtain ⟨k, hjk, hek, hall⟩ := ih (j + 1) hstep
        refine ⟨k, by omega, hek, fun i hi1 hi2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hi1 with heq | hlt
        · rw [← heq]
          exact hok
        · exact hall i (by omega) hi2

/-- The walk has reached the node e = `sbWalk k`, and every node up to k passes `ok`. -/
def WalkedTo (ok : SBNode → Bool) (e : SBNode) : Prop :=
  ∃ k, sbWalk k = e ∧ ∀ i, i ≤ k → ok (sbWalk i) = true

/-- The first stretch, from the root. -/
theorem walkedTo_start {ok : SBNode → Bool} {B m f : ℕ} {e : SBNode}
    (hw : walkTo ok (2 ^ m) (log2Lo 3 B m) (log2Hi 3 B m) e f (sbWalk 0) = true) :
    WalkedTo ok e := by
  obtain ⟨k, -, hek, hall⟩ :=
    walkTo_spec (log2Bracket_pow3 B m) Nat.one_le_two_pow f 0 hw
  exact ⟨k, hek, fun i hi => hall i (Nat.zero_le i) hi⟩

/-- A further stretch, from the end node of the walk so far. -/
theorem walkedTo_next {ok : SBNode → Bool} {B m f : ℕ} {e e' : SBNode} (hW : WalkedTo ok e)
    (hw : walkTo ok (2 ^ m) (log2Lo 3 B m) (log2Hi 3 B m) e' f e = true) :
    WalkedTo ok e' := by
  obtain ⟨j, hje, hallj⟩ := hW
  rw [← hje] at hw
  obtain ⟨k, hjk, hek, hall⟩ :=
    walkTo_spec (log2Bracket_pow3 B m) Nat.one_le_two_pow f j hw
  refine ⟨k, hek, fun i hi => ?_⟩
  rcases Nat.lt_or_ge i j with hij | hij
  · exact hallj i hij.le
  · exact hall i hij hi

/-- The upper check of a node: `rhinOK` at its upper fraction. -/
def rhinOKAt (K b : ℕ) (s : SBNode) : Bool := rhinOK K b s.hiNum s.hiDen

/-- The lower check of a node: `lowOK` at its lower fraction. -/
def lowOKAt (K a : ℕ) (s : SBNode) : Bool := lowOK K a s.loNum s.loDen

/-- An upper walk in stretches to a node whose denominators sum past N gives `RhinBound 1 2`
    for every Order 1 ≤ n ≤ N. -/
theorem rhinBoundUpTo_of_walkedTo {B m N : ℕ} {e : SBNode}
    (hW : WalkedTo (rhinOKAt (2 ^ m) (log2Hi 3 B m)) e) (hN : N < e.loDen + e.hiDen) :
    RhinBoundUpTo 1 2 N := by
  obtain ⟨k, hek, hall⟩ := hW
  rw [← hek] at hN
  exact rhinBoundUpTo_of_checked hN hall

/-- A lower walk in stretches to a node whose denominators sum past N gives the lower side
    for every Order 1 ≤ n ≤ N. -/
theorem lowAt_of_walkedTo {B m N : ℕ} {e : SBNode}
    (hW : WalkedTo (lowOKAt (2 ^ m) (log2Lo 3 B m)) e) (hN : N < e.loDen + e.hiDen) :
    ∀ n, 1 ≤ n → n ≤ N → LowAt n := by
  obtain ⟨k, hek, hall⟩ := hW
  rw [← hek] at hN
  exact lowAt_of_checked hN hall

-- The 10^60 results again, from the generic forms (no new kernel run).
example : RhinBoundUpTo 1 2 (10 ^ 60) := rhinBoundUpTo_of_walk rhinWalk_ok
example : ∀ n, 1 ≤ n → n ≤ 10 ^ 60 → LowAt n := lowAt_of_walk lowWalk_ok

end PowDiff
