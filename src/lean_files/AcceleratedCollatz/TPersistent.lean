-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBinomial

/-!
  Last-1 decomposition of admissible PVs (the OEIS a100982.py count). A persistent
  vector keeps its PV-factor > 1 on every nonempty prefix. Cutting an admissible PV
  of Order d + 1 before its last 1 leaves a persistent vector of Order d; conversely
  p ↦ p ++ 1 :: 0^(p2(d+1) - |p| - 1) is admissible. So the persistent vectors of
  Order d are equinumerous with the admissible PVs of Order d + 1
  (`card_persSet`).
-/

namespace AcceleratedCollatz

variable (d : ℕ)

/-- Every nonempty prefix has PV-factor > 1. -/
def Persistent (p : List Bool) : Prop :=
  ∀ m, 1 ≤ m → m ≤ p.length → 1 < seqProduct (p.take m)

/-- `Persistent` is decidable. -/
instance (p : List Bool) : Decidable (Persistent p) :=
  decidable_of_iff (∀ m, 1 ≤ m → m < p.length + 1 → 1 < seqProduct (p.take m))
    ⟨fun h m h1 h2 => h m h1 (Nat.lt_succ_iff.mpr h2),
      fun h m h1 h2 => h m h1 (Nat.lt_succ_iff.mp h2)⟩

theorem two_pow_lt_three_pow_iff (k n : ℕ) (hn : 1 ≤ n) : 2 ^ k < 3 ^ n ↔ k < p2_of n := by
  constructor
  · intro h
    by_contra hk
    have h1 : 2 ^ p2_of n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := p2_of_spec n
    omega
  · intro hk
    have h1 : 2 ^ k ≤ 2 ^ (p2_of n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := two_pow_pred_p2_lt n hn
    omega

theorem length_lt_p2_of_persistent (p : List Bool) (hp : Persistent p) :
    p.length < p2_of (order p) := by
  rcases Nat.eq_zero_or_pos p.length with h0 | hpos
  · rw [h0]
    simp [p2_of]
  · have h := hp p.length hpos le_rfl
    rw [List.take_length, one_lt_seqProduct_iff] at h
    have hord : 1 ≤ order p := by
      by_contra h0
      have hz : order p = 0 := by omega
      rw [hz, pow_zero] at h
      have := Nat.one_le_two_pow (n := p.length)
      omega
    exact (two_pow_lt_three_pow_iff _ _ hord).mp h

/-- Completion of a persistent vector of Order d to length p2(d + 1). -/
def complete (d : ℕ) (p : List Bool) : List Bool :=
  p ++ true :: List.replicate (p2_of (d + 1) - p.length - 1) false

theorem admissible_complete (p : List Bool) (hp : Persistent p) :
    Admissible (complete (order p) p) ∧ order (complete (order p) p) = order p + 1 := by
  have hlp := length_lt_p2_of_persistent p hp
  have hmono := p2_of_le_succ (order p)
  have hlen : (complete (order p) p).length = p2_of (order p + 1) := by
    simp only [complete, List.length_append, List.length_cons, List.length_replicate]
    omega
  have hord : order (complete (order p) p) = order p + 1 := by
    rw [complete, order_append, order_cons, order_replicate_false]
    simp
  refine ⟨⟨?_, ?_⟩, hord⟩
  · intro m hm1 hml
    rcases Nat.lt_or_ge p.length m with hgt | hle
    · have htl : ((complete (order p) p).take m).length = m := by
        rw [List.length_take]
        omega
      have hto : order ((complete (order p) p).take m) = order p + 1 := by
        rw [complete]
        exact order_take_last_one p _ m hgt
      rw [one_lt_seqProduct_iff, htl, hto, two_pow_lt_three_pow_iff _ _ (by omega), ← hlen]
      exact hml
    · rw [complete, List.take_append_of_le_length hle]
      exact hp m hm1 hle
  · rw [seqProduct_lt_one_iff, hord, hlen]
    exact p2_of_spec _

/-- Persistent vectors of Order d. -/
def persSet (d : ℕ) : Finset (List Bool) :=
  ((Finset.range (p2_of d)).biUnion (fun L => (allBits L).toFinset)).filter
    (fun p => Persistent p ∧ order p = d)

theorem mem_persSet (p : List Bool) :
    p ∈ persSet d ↔ Persistent p ∧ order p = d := by
  simp only [persSet, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    List.mem_toFinset, mem_allBits]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨⟨p.length, ?_, rfl⟩, h⟩
    have := length_lt_p2_of_persistent p h.1
    rw [h.2] at this
    exact this

/-- Persistent vectors of Order d and admissible PVs of Order d + 1 are equinumerous. -/
theorem card_persSet : (persSet d).card = (admSet (d + 1)).card := by
  have himg : (persSet d).image (complete d) = admSet (d + 1) := by
    ext s
    simp only [Finset.mem_image, mem_persSet, mem_admSet]
    constructor
    · rintro ⟨p, ⟨hp, hord⟩, rfl⟩
      have h := admissible_complete p hp
      rw [hord] at h
      exact h
    · rintro ⟨hA, hord⟩
      have hmem : true ∈ s := order_pos_mem s (by omega)
      obtain ⟨a, r, rfl⟩ := exists_last_true s hmem
      have hoa : order a = d := by
        rw [order_append, order_cons, order_replicate_false] at hord
        simp only [↓reduceIte] at hord
        omega
      have hlen := admissible_length _ hA
      rw [hord] at hlen
      simp only [List.length_append, List.length_cons, List.length_replicate] at hlen
      refine ⟨a, ⟨?_, hoa⟩, ?_⟩
      · intro m hm1 hml
        have hms : m < (a ++ true :: List.replicate r false).length := by
          simp only [List.length_append, List.length_cons, List.length_replicate]
          omega
        have h := hA.1 m hm1 hms
        rw [List.take_append_of_le_length hml] at h
        exact h
      · rw [complete]
        congr 3
        omega
  have hinj : Set.InjOn (complete d) (persSet d) := by
    intro p hp q hq h
    rw [Finset.mem_coe, mem_persSet] at hp hq
    have hlen : p.length = q.length := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have h1 := order_take_last_one p (p2_of (d + 1) - p.length - 1) (p.length + 1) (by omega)
        rw [← complete, h, complete, List.take_append_of_le_length (by omega)] at h1
        have h2 := order_take_le q (p.length + 1)
        omega
      · have h1 := order_take_last_one q (p2_of (d + 1) - q.length - 1) (q.length + 1) (by omega)
        rw [← complete, ← h, complete, List.take_append_of_le_length (by omega)] at h1
        have h2 := order_take_le p (q.length + 1)
        omega
    have h' := congrArg (List.take p.length) h
    simp only [complete, List.take_left] at h'
    rw [hlen, List.take_left] at h'
    exact h'
  rw [← himg, Finset.card_image_of_injOn hinj]

end AcceleratedCollatz
