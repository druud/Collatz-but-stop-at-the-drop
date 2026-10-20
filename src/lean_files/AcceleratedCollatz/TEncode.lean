-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TDrop

/-!
  Integer encodings of admissible parity vectors. `encode` reads a vector
  MSB-first ([1,1,0,1,0] ↦ 26); `oddPart` strips trailing zeros (26 ↦ 13).
  Both are injective on admissible vectors, so admissible vectors, their
  encodings, their odd parts and (via `classEquiv`) their class ids are
  equivalent sets, each with its own sorting.
-/

namespace AcceleratedCollatz

variable (s : List Bool)

/-- MSB-first binary value of a bit list. -/
def encode : List Bool → ℕ
  | [] => 0
  | b :: t => (if b then 2 ^ t.length else 0) + encode t

/-- n with its trailing binary zeros removed. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ trailingZeros n

theorem encode_lt : encode s < 2 ^ s.length := by
  induction s with
  | nil =>
    simp [encode]
  | cons b t ih =>
    rw [List.length_cons, pow_succ]
    cases b with
    | true =>
      simp only [encode, ↓reduceIte]
      omega
    | false =>
      simp only [encode, Bool.false_eq_true, ↓reduceIte]
      omega

theorem encode_append (a b : List Bool) : encode (a ++ b) = encode a * 2 ^ b.length + encode b := by
  induction a with
  | nil =>
    simp [encode]
  | cons x a ih =>
    simp only [List.cons_append, encode, List.length_append, ih]
    cases x with
    | true =>
      simp only [↓reduceIte, pow_add]
      ring
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring

theorem encode_replicate_false (k : ℕ) : encode (List.replicate k false) = 0 := by
  induction k with
  | zero =>
    simp [encode]
  | succ k ih =>
    simp [List.replicate_succ, encode, ih]

theorem log_encode_cons_true (t : List Bool) : Nat.log 2 (encode (true :: t)) = t.length := by
  have hlt := encode_lt t
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · simp only [encode, ↓reduceIte]
    omega
  · simp only [encode, ↓reduceIte, pow_succ]
    omega

/-- Same-length lists with equal encodings are equal. -/
theorem encode_inj_of_length (s t : List Bool) (hlen : s.length = t.length)
    (h : encode s = encode t) : s = t := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil =>
      rfl
    | cons c t =>
      simp at hlen
  | cons b s ih =>
    cases t with
    | nil =>
      simp at hlen
    | cons c t =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hs := encode_lt s
      have ht := encode_lt t
      simp only [encode] at h
      rw [hlen] at hs h
      cases b with
      | true =>
        cases c with
        | true =>
          simp only [↓reduceIte, Nat.add_left_cancel_iff] at h
          rw [ih t hlen h]
        | false =>
          simp only [↓reduceIte, Bool.false_eq_true] at h
          omega
      | false =>
        cases c with
        | true =>
          simp only [↓reduceIte, Bool.false_eq_true] at h
          omega
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h
          rw [ih t hlen h]

/-- Lists starting with 1 and with equal encodings are equal. -/
theorem encode_inj_of_head (u w : List Bool) (h : encode (true :: u) = encode (true :: w)) :
    true :: u = true :: w := by
  have hlen : u.length = w.length := by
    rw [← log_encode_cons_true u, ← log_encode_cons_true w, h]
  apply encode_inj_of_length
  · simp [hlen]
  · exact h

/-- The only admissible word of Order 0 is [0]. -/
theorem admissible_order_zero (hA : Admissible s) (h0 : order s = 0) :
    s = [false] := by
  have hlen := admissible_length s hA
  rw [h0] at hlen
  have hp2 : p2_of 0 = 1 := by
    simp [p2_of]
  rw [hp2] at hlen
  match s, hlen with
  | [b], _ =>
    cases b with
    | true =>
      simp [order] at h0
    | false =>
      rfl

/-- An admissible word of Order ≥ 1 starts with 1. -/
theorem admissible_cons_true (hA : Admissible s) (hord : 1 ≤ order s) :
    ∃ u, s = true :: u := by
  have h32 : 3 ^ order s < 2 ^ s.length := (seqProduct_lt_one_iff s).mp hA.lt_one
  have hle := order_le_length s
  have hlen : 2 ≤ s.length := by
    by_contra hlt
    have ho : order s = 1 := by omega
    have hl : s.length = 1 := by omega
    rw [ho, hl] at h32
    norm_num at h32
  have hp := hA.prefix_gt 1 le_rfl (by omega)
  rw [one_lt_seqProduct_iff] at hp
  match s, hp with
  | b :: u, hp =>
    cases b with
    | true =>
      exact ⟨u, rfl⟩
    | false =>
      simp [order] at hp

theorem encode_pos_of_order (hA : Admissible s) (hord : 1 ≤ order s) :
    0 < encode s := by
  obtain ⟨u, rfl⟩ := admissible_cons_true s hA hord
  simp only [encode, ↓reduceIte]
  positivity

/-- Admissible vectors are determined by their encodings. -/
theorem encode_injective (s t : List Bool) (hs : Admissible s) (ht : Admissible t)
    (h : encode s = encode t) : s = t := by
  by_cases hs0 : order s = 0
  · by_cases ht0 : order t = 0
    · rw [admissible_order_zero s hs hs0, admissible_order_zero t ht ht0]
    · have hpos := encode_pos_of_order t ht (by omega)
      rw [admissible_order_zero s hs hs0] at h
      simp [encode] at h
      omega
  · by_cases ht0 : order t = 0
    · have hpos := encode_pos_of_order s hs (by omega)
      rw [admissible_order_zero t ht ht0] at h
      simp [encode] at h
      omega
    · obtain ⟨u, rfl⟩ := admissible_cons_true s hs (by omega)
      obtain ⟨w, rfl⟩ := admissible_cons_true t ht (by omega)
      exact encode_inj_of_head u w h

theorem oddPart_mul (n : ℕ) : oddPart n * 2 ^ trailingZeros n = n :=
  Nat.div_mul_cancel pow_padicValNat_dvd

theorem oddPart_pos (n : ℕ) (hn : 0 < n) : 0 < oddPart n := by
  have h := oddPart_mul n
  by_contra h0
  have hz : oddPart n = 0 := by omega
  rw [hz, zero_mul] at h
  omega

/-- oddPart injectivity, case trailingZeros (encode s) ≤ trailingZeros (encode t). -/
theorem oddPart_inj_aux (s t : List Bool) (hs : Admissible s) (ht : Admissible t)
    (hs1 : 1 ≤ order s) (ht1 : 1 ≤ order t)
    (hle : trailingZeros (encode s) ≤ trailingZeros (encode t))
    (h : oddPart (encode s) = oddPart (encode t)) : s = t := by
  have hms := oddPart_mul (encode s)
  have hmt := oddPart_mul (encode t)
  have hmul : encode t = encode s * 2 ^ (trailingZeros (encode t) - trailingZeros (encode s)) :=
    calc encode t = oddPart (encode t) * 2 ^ trailingZeros (encode t) := hmt.symm
      _ = oddPart (encode s) *
          2 ^ (trailingZeros (encode s) +
            (trailingZeros (encode t) - trailingZeros (encode s))) := by
        rw [h, Nat.add_sub_cancel' hle]
      _ = encode s * 2 ^ (trailingZeros (encode t) - trailingZeros (encode s)) := by
        rw [pow_add, ← mul_assoc, hms]
  have hext : encode t =
      encode (s ++ List.replicate (trailingZeros (encode t) - trailingZeros (encode s)) false) := by
    rw [encode_append, encode_replicate_false, List.length_replicate, add_zero]
    exact hmul
  obtain ⟨u, hu⟩ := admissible_cons_true s hs hs1
  obtain ⟨w, hw⟩ := admissible_cons_true t ht ht1
  have heq : t =
      s ++ List.replicate (trailingZeros (encode t) - trailingZeros (encode s)) false := by
    rw [hw] at hext ⊢
    rw [hu] at hext ⊢
    exact encode_inj_of_head w _ hext
  by_contra hne
  exact admissible_not_prefix s t hs ht hne ⟨_, heq.symm⟩

/-- Admissible vectors are determined by the odd parts of their encodings. -/
theorem oddPart_injective (s t : List Bool) (hs : Admissible s) (ht : Admissible t)
    (h : oddPart (encode s) = oddPart (encode t)) : s = t := by
  by_cases hs0 : order s = 0
  · by_cases ht0 : order t = 0
    · rw [admissible_order_zero s hs hs0, admissible_order_zero t ht ht0]
    · have hpos := oddPart_pos _ (encode_pos_of_order t ht (by omega))
      have hz : oddPart (encode [false]) = 0 := by
        simp [encode, oddPart]
      rw [admissible_order_zero s hs hs0, hz] at h
      omega
  · by_cases ht0 : order t = 0
    · have hpos := oddPart_pos _ (encode_pos_of_order s hs (by omega))
      have hz : oddPart (encode [false]) = 0 := by
        simp [encode, oddPart]
      rw [admissible_order_zero t ht ht0, hz] at h
      omega
    · rcases le_total (trailingZeros (encode s)) (trailingZeros (encode t)) with hle | hle
      · exact oddPart_inj_aux s t hs ht (by omega) (by omega) hle h
      · exact (oddPart_inj_aux t s ht hs (by omega) (by omega) hle h.symm).symm

example : encode [true, true, false, true, false] = 26 := by
  decide


/-- s with its trailing zeros removed. -/
def core (s : List Bool) : List Bool := (s.reverse.dropWhile (fun b => !b)).reverse

theorem core_append_zeros :
    s = core s ++ List.replicate (s.length - (core s).length) false := by
  have hsplit := List.takeWhile_append_dropWhile (p := fun b => !b) (l := s.reverse)
  have hall : s.reverse.takeWhile (fun b => !b) =
      List.replicate (s.reverse.takeWhile (fun b => !b)).length false := by
    apply List.eq_replicate_iff.mpr
    refine ⟨rfl, ?_⟩
    intro b hb
    have hall := List.all_takeWhile (p := fun b => !b) (l := s.reverse)
    rw [List.all_eq_true] at hall
    simpa using hall b hb
  have hlen : (s.reverse.takeWhile (fun b => !b)).length = s.length - (core s).length := by
    have h := congrArg List.length hsplit
    simp only [List.length_append, List.length_reverse] at h
    simp only [core, List.length_reverse]
    omega
  conv_lhs => rw [← List.reverse_reverse s, ← hsplit, hall, hlen]
  rw [List.reverse_append, List.reverse_replicate]
  rfl

theorem core_eq_nil_or_last_true :
    core s = [] ∨ ∃ a, core s = a ++ [true] := by
  unfold core
  cases h : s.reverse.dropWhile (fun b => !b) with
  | nil =>
    left
    rfl
  | cons b t =>
    right
    have hb : b = true := by
      have hne : s.reverse.dropWhile (fun b => !b) ≠ [] := by
        rw [h]
        simp
      have := List.head_dropWhile_not (fun b => !b) hne
      simp only [h, List.head_cons] at this
      simpa using this
    refine ⟨t.reverse, ?_⟩
    rw [hb]
    simp

theorem oddPart_mul_two_pow (m z : ℕ) (hm : m % 2 = 1) : oddPart (m * 2 ^ z) = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : trailingZeros (m * 2 ^ z) = z := by
    unfold trailingZeros
    rw [padicValNat.mul (by omega) (by positivity), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by omega)]
    simp
  unfold oddPart
  rw [hv]
  exact Nat.mul_div_cancel _ (by positivity)

/-- The core's encoding is the odd part of the encoding. -/
theorem encode_core : encode (core s) = oddPart (encode s) := by
  have hs := core_append_zeros s
  have henc : encode s = encode (core s) * 2 ^ (s.length - (core s).length) := by
    conv_lhs => rw [hs]
    rw [encode_append, encode_replicate_false, List.length_replicate, add_zero]
  rcases core_eq_nil_or_last_true s with h0 | ⟨a, ha⟩
  · rw [henc, h0]
    simp [encode, oddPart, trailingZeros]
  · have hodd : encode (core s) % 2 = 1 := by
      rw [ha, encode_append]
      simp [encode]
    rw [henc, oddPart_mul_two_pow _ _ hodd]

example : core [true, true, false, true, true, false, false] = [true, true, false, true, true] := by
  decide

end AcceleratedCollatz
