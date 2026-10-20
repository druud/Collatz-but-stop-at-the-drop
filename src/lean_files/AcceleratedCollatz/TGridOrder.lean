-- SPDX-License-Identifier: MIT
import AcceleratedCollatz.TGridOrderQ

/-!
  Record Orders as the Orders with a linear grid (paper sec:sweeps), the q = 3
  case of `TGridOrderQ`. The points (o, j) with o ≤ n and j ≤ P are sorted by the
  3-smooth levels 3^o / 2^j; the grid is linear for (n, P) when the linear levels
  o P - j n sort all pairs of points the same way, except the pair of origin and
  corner (`GridLinear`). With P = p2(n) this holds exactly at the upper record
  Orders, where p2(n)/n is below every earlier p2(a)/a (`gridLinear_iff_upperRecord`);
  with P = p2(n) - 1 exactly at the lower record Orders, where (p2(n) - 1)/n is
  above every earlier (p2(a) - 1)/a (`gridLinear_iff_lowerRecord`).
-/

namespace AcceleratedCollatz

/-- The linear levels o P - j n sort the points of the (n, P) grid like 3^o / 2^j,
    except the pair of origin and corner. -/
def GridLinear (n P : ℕ) : Prop := GridLinearQ 3 n P

/-- Upper record Order: p2(n)/n is below p2(a)/a for every 1 ≤ a < n.
    Orders 0 and 1 qualify: there is no such a. -/
def UpperRecord (n : ℕ) : Prop :=
  ∀ a, 1 ≤ a → a < n → a * p2_of n < n * p2_of a

/-- Lower record Order: (p2(n) - 1)/n is above (p2(a) - 1)/a for every 1 ≤ a < n.
    Orders 0 and 1 qualify: there is no such a. -/
def LowerRecord (n : ℕ) : Prop :=
  ∀ a, 1 ≤ a → a < n → n * (p2_of a - 1) < a * (p2_of n - 1)

/-- The grid of slope p2(n)/n is linear exactly at the upper record Orders. -/
theorem gridLinear_iff_upperRecord {n : ℕ} (hn : 1 ≤ n) :
    GridLinear n (p2_of n) ↔ UpperRecord n :=
  gridLinearQ_iff_upperRecordQ (by decide) le_rfl hn

/-- The grid of slope (p2(n) - 1)/n is linear exactly at the lower record Orders. -/
theorem gridLinear_iff_lowerRecord {n : ℕ} (hn : 1 ≤ n) :
    GridLinear n (p2_of n - 1) ↔ LowerRecord n :=
  gridLinearQ_iff_lowerRecordQ (by decide) le_rfl hn

end AcceleratedCollatz
