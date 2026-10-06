import Oscillation.AveragedLocal

/-! Average the child functions before comparing their maximum, as in r15. -/
namespace Oscillation
noncomputable section
open Finset

/-- The sum of child maxima pays for the averaged representative values and
the difference between the two endpoint representatives. -/
theorem sum_gridMax_averaged_end_comparison {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (f : Fin (2*d) → Fin m → ℝ) (a : Fin (2*d) → Fin m) :
    (∑ l : Fin (2*d), finAvg (fun k => f k (a l))) +
      |finAvg (fun k => f k (a ⟨0, by omega⟩)) -
        finAvg (fun k => f k (a ⟨2*d-1, by omega⟩))| ≤
      ∑ k : Fin (2*d), gridMax hm (f k) := by
  have hmax : gridMax hm (fun t => finAvg (fun k => f k t)) ≤
      finAvg (fun k => gridMax hm (f k)) :=
    gridMax_le hm _ (fun t => finAvg_mono (fun k => le_gridMax hm (f k) t))
  have H := (gridMax_end_comparison hd hm (fun t => finAvg (fun k => f k t)) a).trans hmax
  apply (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (2*d:ℕ))).mp
  simpa only [finAvg, Fintype.card_fin] using H

end
end Oscillation
