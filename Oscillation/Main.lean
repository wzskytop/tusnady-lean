import Oscillation.R65

namespace Oscillation

/-- The all-n, all-colorings random-point lower bound through the direct proof. -/
theorem paper_lower_bound : Riesz.PaperLowerBound := R65.paper_lower_bound

/-- The deterministic planar rectangle-discrepancy consequence. -/
theorem planar_tusnady_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (Real.logb 2 n) ^ (3 / 2 : ℝ) < Riesz.PointSets.Δ₂ n :=
  Riesz.deterministic_lower_of_paper paper_lower_bound

end Oscillation
