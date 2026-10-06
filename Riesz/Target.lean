import Riesz.PointSets
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exact target and its deterministic consequence

`PaperLowerBound` records the exact random-point theorem. It is a proposition,
not an axiom. The new proof is `Oscillation.paper_lower_bound` in
`Oscillation/Main.lean`. This module also provides the reduction to worst-case
discrepancy and contains no proof of the lower bound as an assumption.
-/

namespace Riesz
open PointSets

/-- The current manuscript's random lower bound, for every requested exponential
failure rate and every positive sample size. `GoodEvent` uses a strict lower
bound, which is slightly stronger than the paper's non-strict statement. -/
def PaperLowerBound : Prop :=
  ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    GoodEvent n (c * (Real.logb 2 n) ^ ((3 : ℝ) / 2)) (Real.exp (-A * n))

/-- Positive probability suffices for the deterministic lower-bound conclusion.
This reusable reduction is instantiated by `planar_tusnady_lower_bound` in Main. -/
theorem deterministic_lower_of_paper (h : PaperLowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (Real.logb 2 n) ^ ((3 : ℝ) / 2) < PointSets.Δ₂ n := by
  obtain ⟨c, hc, hevent⟩ := h 1 (by norm_num)
  refine ⟨c, hc, fun n hn => ?_⟩
  apply lt_Δ₂_of_goodEvent (ε := Real.exp (-(1 : ℝ) * n)) ?_ (hevent n hn)
  rw [Real.exp_lt_one_iff]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end Riesz
