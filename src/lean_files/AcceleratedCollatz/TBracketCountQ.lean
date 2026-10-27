-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TBracketWordTreeQ
import AcceleratedCollatz.TBracketCount
import AcceleratedCollatz.TAdmSet

/-!
  Counting bracket words in the q-family (odd q ≥ 3), the q-form of `TBracketCount`.
  `bracketTreesQ q n` is the set of the bracket words of the admissible words of Order n;
  there are as many as admissible words (`card_bracketTreesQ`), and they are exactly the
  encodings of the valid trees of Order n (`mem_bracketTreesQ`, `ncard_encQ_validTreesQ`).
  For q = 3 these are the bracket trees of `TBracketCount` (`bracketTreesQ_three`).
-/

namespace AcceleratedCollatz

variable {q : ℕ}

/-- Bracket words of the admissible words of Order n in the q-family. -/
def bracketTreesQ (q n : ℕ) : Finset (List ℕ) := (admSetQ q n).image (bracketWordQ q)

/-- There are as many bracket words of Order n as admissible words of Order n. -/
theorem card_bracketTreesQ (hq : 3 ≤ q) (n : ℕ) :
    (bracketTreesQ q n).card = (admSetQ q n).card := by
  apply Finset.card_image_of_injOn
  intro s hs s' hs' h
  have hA := ((mem_admSetQ (by omega) n s).mp (Finset.mem_coe.mp hs)).1
  have hA' := ((mem_admSetQ (by omega) n s').mp (Finset.mem_coe.mp hs')).1
  exact bracketWordQ_injective hq hA hA' h

/-- The bracket words of Order n are the encodings of the valid trees of Order n. -/
theorem mem_bracketTreesQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) (c : List ℕ) :
    c ∈ bracketTreesQ q n ↔ ∃ t ∈ validTreesQ q n, encQ q t = c := by
  have hB := word_bijOn_validTreesQ hodd hq n
  constructor
  · intro hc
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨t, ht, rfl⟩ := hB.surjOn (Finset.mem_coe.mpr hs)
    exact ⟨t, ht, (bracketWordQ_word_eq_encQ hodd hq ht.1).symm⟩
  · rintro ⟨t, ht, rfl⟩
    rw [← bracketWordQ_word_eq_encQ hodd hq ht.1]
    exact Finset.mem_image.mpr ⟨t.word, Finset.mem_coe.mp (hB.mapsTo ht), rfl⟩

/-- The encodings of the valid trees of Order n are as many as the admissible words. -/
theorem ncard_encQ_validTreesQ (hodd : Odd q) (hq : 3 ≤ q) (n : ℕ) :
    (encQ q '' validTreesQ q n).ncard = (admSetQ q n).card := by
  have h : encQ q '' validTreesQ q n = (bracketTreesQ q n : Set (List ℕ)) := by
    ext c
    rw [Finset.mem_coe, mem_bracketTreesQ hodd hq]
    rfl
  rw [h, Set.ncard_coe_finset]
  exact card_bracketTreesQ hq n

/-- For q = 3 the bracket words are those of `TBracketCount`. -/
theorem bracketTreesQ_three (n : ℕ) : bracketTreesQ 3 n = bracketTrees n := by
  unfold bracketTreesQ bracketTrees
  rw [admSetQ_three]
  congr 1
  funext s
  exact bracketWordQ_three s

-- The numbers of bracket words of Orders 1 .. 4 for q = 5.
set_option linter.hashCommand false in
#guard (List.range 4).map (fun n => (bracketTreesQ 5 (n + 1)).card) = [1, 2, 5, 14]

end AcceleratedCollatz
