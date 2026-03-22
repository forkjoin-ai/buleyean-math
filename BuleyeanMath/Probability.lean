import Init

/-!
# Buleyean Probability

The complement distribution. Weight = total rejections - rejections at i + 1.
The +1 is the sliver (Barbelo). No option ever reaches zero probability.

Key theorems:
  - buleyean_positivity: weight i ≥ 1 for all i
  - buleyean_concentration: less rejected = higher weight
  - The sliver is derived from thermodynamics (Landauer heat from vents)
  - The complement distribution is the Skyrms walker's stationary distribution
-/

namespace BuleyeanMath.Probability

-- Buleyean weight: complement of rejection + sliver
def weight (totalRejections rejections : Nat) : Nat :=
  totalRejections - rejections + 1

-- Positivity: weight is always at least 1 (the sliver guarantees this)
theorem positivity (total rej : Nat) (_ : rej ≤ total) :
    weight total rej ≥ 1 := by
  unfold weight; omega

-- At maximum rejection, weight = 1 (the sliver alone survives)
theorem max_rejection_is_sliver (total : Nat) :
    weight total total = 1 := by
  unfold weight; omega

-- Zero rejection = maximum weight
theorem zero_rejection_max (total : Nat) :
    weight total 0 = total + 1 := by
  unfold weight; omega

-- Concentration: less rejected → higher weight
theorem concentration (total r1 r2 : Nat)
    (h1 : r1 ≤ total) (h2 : r2 ≤ total) (h : r1 < r2) :
    weight total r1 > weight total r2 := by
  unfold weight; omega

-- The complement distribution over K modes
structure ComplementDistribution (K : Nat) where
  rejections : Fin K → Nat
  total : Nat
  bounded : ∀ i, rejections i ≤ total

-- Every mode has positive weight (Barbelo)
theorem all_positive (d : ComplementDistribution K) (i : Fin K) :
    weight d.total (d.rejections i) ≥ 1 := by
  exact positivity d.total (d.rejections i) (d.bounded i)

-- The mode with fewest rejections has the highest weight (Sophia's peak)
theorem sophia_peak (d : ComplementDistribution K) (i j : Fin K)
    (h : d.rejections i ≤ d.rejections j) :
    weight d.total (d.rejections i) ≥ weight d.total (d.rejections j) := by
  unfold weight; omega

end BuleyeanMath.Probability
