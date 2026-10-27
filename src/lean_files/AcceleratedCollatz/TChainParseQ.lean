-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TChainEquivQ
import AcceleratedCollatz.TRank

/-!
  Computable chain decomposition in the q-family (odd q ≥ 3), the q-form of `TChainParse`.
  `chainParseQ q u` cuts u greedily into shortest prefixes of level < 1; on blocks ++ tail
  it returns the blocks (`chainParseQ_append`, `chainParseQ_flatten`). `chainOfQ q s`: the
  blocks of s after its leading 1, Order-0 blocks included (they can stand anywhere in the
  q-family), the inverse of `chainWordQ` (`chainOfQ_chainWordQ`), equal to `chainEquivQ`
  (`chainEquivQ_eq_chainOfQ`). `codeOfQ q s`: the (d, c) list of s, c the 0-based index of
  the block among the admissible words of its Order (`rankQ`, the number of smaller ones);
  equal to `codeEquivQ` (`codeEquivQ_eq_codeOfQ`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

theorem seqProductQ_nil (q : ℕ) : seqProductQ q [] = 1 := by
  simp [seqProductQ]

/-- Greedy parse: repeatedly the shortest prefix of level < 1. -/
def chainParseQ (q : ℕ) (u : List Bool) : List (List Bool) :=
  if h : ∃ j, j < u.length + 1 ∧ seqProductQ q (u.take j) < 1 then
    u.take (Nat.find h) :: chainParseQ q (u.drop (Nat.find h))
  else []
termination_by u.length
decreasing_by
  have hspec := Nat.find_spec h
  have hpos : Nat.find h ≠ 0 := by
    intro h0
    rw [h0, List.take_zero, seqProductQ_nil] at hspec
    exact absurd hspec.2 (lt_irrefl 1)
  rw [List.length_drop]
  omega

/-- The blocks of s: the parse of s without its leading 1. -/
def chainOfQ (q : ℕ) (s : List Bool) : List (List Bool) := chainParseQ q s.tail

/-- The 0-based index of b among the admissible words of Order d: the smaller ones. -/
def rankQ (q d : ℕ) (b : List Bool) : ℕ := ((admSetQ q d).filter (· < b)).card

/-- (d, c) list of s: Order and 0-based index of every block. -/
def codeOfQ (q : ℕ) (s : List Bool) : List (ℕ × ℕ) :=
  (chainOfQ q s).map (fun b => (order b, rankQ q (order b) b))

-- q = 5: the word 11000 = 1 | 100 | 0 and its codes.
set_option linter.hashCommand false in
#guard chainOfQ 5 [true, true, false, false, false] = [[true, false, false], [false]]

set_option linter.hashCommand false in
#guard codeOfQ 5 [true, true, false, false, false] = [(1, 0), (0, 0)]

theorem chainParseQ_nil (q : ℕ) : chainParseQ q [] = [] := by
  have hno : ¬ ∃ j, j < ([] : List Bool).length + 1 ∧
      seqProductQ q (([] : List Bool).take j) < 1 := by
    rintro ⟨j, -, hlt⟩
    rw [List.take_nil, seqProductQ_nil] at hlt
    exact lt_irrefl 1 hlt
  rw [chainParseQ]
  simp only [hno, ↓reduceDIte]

/-- An admissible prefix is the first block. -/
theorem chainParseQ_append (b r : List Bool) (hb : AdmissibleQ q b) :
    chainParseQ q (b ++ r) = b :: chainParseQ q r := by
  have hex : ∃ j, j < (b ++ r).length + 1 ∧ seqProductQ q ((b ++ r).take j) < 1 := by
    refine ⟨b.length, ?_, ?_⟩
    · rw [List.length_append]
      omega
    · rw [List.take_left]
      exact hb.lt_one
  have hfind : Nat.find hex = b.length := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.length_append]
      omega
    · rw [List.take_left]
      exact hb.lt_one
    · intro m hm hcon
      have htake : (b ++ r).take m = b.take m := List.take_append_of_le_length (by omega)
      rw [htake] at hcon
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rw [List.take_zero, seqProductQ_nil] at hcon
        exact lt_irrefl 1 hcon.2
      · exact lt_asymm (hb.prefix_gt m hpos hm) hcon.2
  rw [chainParseQ]
  simp only [hex, ↓reduceDIte]
  rw [hfind, List.take_left, List.drop_left]

/-- On admissible blocks followed by r: the blocks, then the parse of r. -/
theorem chainParseQ_flatten (bs : List (List Bool)) (r : List Bool)
    (h : ∀ b ∈ bs, AdmissibleQ q b) : chainParseQ q (bs.flatten ++ r) = bs ++ chainParseQ q r := by
  induction bs with
  | nil =>
    rfl
  | cons b t ih =>
    rw [List.flatten_cons, List.append_assoc, chainParseQ_append _ _ (h b List.mem_cons_self),
      ih (fun c hc => h c (List.mem_cons_of_mem b hc))]
    rfl

/-- `chainOfQ` inverts `chainWordQ`. -/
theorem chainOfQ_chainWordQ (bs : List (List Bool)) (h : ∀ b ∈ bs, AdmissibleQ q b) :
    chainOfQ q (chainWordQ bs) = bs := by
  unfold chainOfQ chainWordQ
  rw [List.tail_cons, ← List.append_nil bs.flatten, chainParseQ_flatten bs [] h,
    chainParseQ_nil, List.append_nil]

/-- `chainOfQ` computes `chainEquivQ`. -/
theorem chainEquivQ_eq_chainOfQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ)
    (s : (admSetQ q (n + 1) : Set (List Bool))) :
    (chainEquivQ hodd hq n s : List (List Bool)) = chainOfQ q s := by
  have h := chainOfQ_chainWordQ (chainEquivQ hodd hq n s) (chainEquivQ hodd hq n s).2.1
  rw [chainWordQ_chainEquivQ] at h
  exact h.symm

/-- `rankQ` computes the inverse of `admIndexQ`. -/
theorem admIndexQ_symm_eq_rankQ (d : ℕ) (b : List Bool) (hb : b ∈ admSetQ q d) :
    ((admIndexQ q d).symm ⟨b, hb⟩ : ℕ) = rankQ q d b := by
  unfold admIndexQ rankQ
  exact orderIsoOfFin_symm_eq_card _ b hb

/-- `codeOfQ` computes `codeEquivQ`. -/
theorem codeEquivQ_eq_codeOfQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ)
    (s : (admSetQ q (n + 1) : Set (List Bool))) :
    (codeEquivQ hodd hq n s).1.map (fun x => (x.1, (x.2 : ℕ))) = codeOfQ q s := by
  unfold codeOfQ
  rw [← chainEquivQ_eq_chainOfQ hodd hq n s]
  change ((chainEquivQ hodd hq n s).1.pmap (blockCodeQ q) _).map _ = _
  rw [List.map_pmap]
  have hfun : ∀ (a : List Bool) (h : a ∈ admSetQ q (order a)),
      ((blockCodeQ q a h).fst, ((blockCodeQ q a h).snd : ℕ)) = (order a, rankQ q (order a) a) :=
    fun a h => Prod.ext rfl (admIndexQ_symm_eq_rankQ (order a) a h)
  have hcongr := List.pmap_congr_left (chainEquivQ hodd hq n s).1
    (f := fun a h => ((blockCodeQ q a h).fst, ((blockCodeQ q a h).snd : ℕ)))
    (g := fun a (_ : a ∈ admSetQ q (order a)) => (order a, rankQ q (order a) a))
    (H₁ := fun b hb => mem_admSetQ_order hq ((chainEquivQ hodd hq n s).2.1 b hb))
    (H₂ := fun b hb => mem_admSetQ_order hq ((chainEquivQ hodd hq n s).2.1 b hb))
    (fun a _ h₁ _ => hfun a h₁)
  exact hcongr.trans (List.pmap_eq_map _)

end AcceleratedCollatz
