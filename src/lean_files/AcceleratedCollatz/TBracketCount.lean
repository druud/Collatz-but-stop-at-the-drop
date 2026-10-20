-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketTree
import Mathlib.Data.Set.Card

/-!
  Counting bracket trees. `bracketTrees n` is the set of the bracket words of the
  admissible words of Order n; for n + 1 these are the bracket trees of length
  n + 1 (`mem_bracketTrees`), and there are as many as admissible words of that
  Order (`card_bracketTrees`, `ncard_isBracketTree`), A100982.
-/

namespace AcceleratedCollatz

/-- Bracket words of the admissible words of Order n. -/
def bracketTrees (n : ℕ) : Finset (List ℕ) := (admSet n).image bracketWord

/-- `bracketTrees (n + 1)` holds the bracket trees of length n + 1. -/
theorem mem_bracketTrees (n : ℕ) (c : List ℕ) :
    c ∈ bracketTrees (n + 1) ↔ IsBracketTree c ∧ c.length = n + 1 := by
  have h := image_bracketWord_admSet n
  rw [← Finset.coe_image] at h
  rw [← Finset.mem_coe]
  exact Set.ext_iff.mp h c

/-- There are as many bracket words of Order n as admissible words of Order n. -/
theorem card_bracketTrees (n : ℕ) : (bracketTrees n).card = (admSet n).card := by
  apply Finset.card_image_of_injOn
  intro s hs s' hs' h
  have hA := ((mem_admSet n s).mp (Finset.mem_coe.mp hs)).1
  have hA' := ((mem_admSet n s').mp (Finset.mem_coe.mp hs')).1
  exact bracketWord_injective hA hA' h

/-- The bracket trees of length n + 1 number as many as the admissible words of
    Order n + 1. -/
theorem ncard_isBracketTree (n : ℕ) :
    {c | IsBracketTree c ∧ c.length = n + 1}.ncard = (admSet (n + 1)).card := by
  rw [← image_bracketWord_admSet, ← Finset.coe_image, Set.ncard_coe_finset]
  exact card_bracketTrees (n + 1)

-- The numbers of bracket trees of lengths 1 .. 7: A100982.
set_option linter.hashCommand false in
#guard (List.range 7).map (fun n => (bracketTrees (n + 1)).card) = [1, 1, 2, 3, 7, 12, 30]

end AcceleratedCollatz
