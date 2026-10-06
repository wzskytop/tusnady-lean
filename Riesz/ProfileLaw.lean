import Riesz.Dyadic
import Riesz.Moments

/-!
# The finite law of one dyadically averaged profile

The support `Fin 4 × Fin m` is the first two horizontal bits followed by the
remaining bits (`m = 2^(L-2)`).  `profile_cell_average` identifies each value
below with the integral average of the actual continuous profile on its cell.
-/

namespace Riesz
noncomputable section
open Finset Moments

/-- Uniform distribution on the `4m` horizontal cells. -/
def profileLaw (m : ℕ) (hm : 0 < m) : FiniteLaw (Fin 4 × Fin m) where
  weight := fun _ => 1 / (4 * m)
  nonneg := fun _ => by positivity
  total := by
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

/-- The value of `w_L` on a cell, parameterized by quarter and within-quarter index. -/
def profileValue (m : ℕ) (a : Fin 4 × Fin m) : ℝ :=
  quarterValue a.1 (quarterMidpoint m a.2)

lemma profileValue_abs_le {m : ℕ} (a : Fin 4 × Fin m) :
    |profileValue m a| ≤ 1 / 4 :=
  abs_quarterValue a.1 (quarterMidpoint_bounds a.2).1 (quarterMidpoint_bounds a.2).2

lemma profileLaw_expectation {m : ℕ} (hm : 0 < m) (f : ℝ → ℝ) :
    expectation (profileLaw m hm) (fun a => f (profileValue m a)) = blockMean m f := by
  unfold expectation profileLaw profileValue blockMean quarterMean
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_div]
  ring

lemma profileLaw_centered {m : ℕ} (hm : 0 < m) :
    expectation (profileLaw m hm) (profileValue m) = 0 := by
  simpa only [id_eq] using (profileLaw_expectation hm id).trans (blockMean_id m)

lemma profileLaw_variance_lower {m : ℕ} (hm : 0 < m) :
    1 / 64 ≤ expectation (profileLaw m hm) (fun a => profileValue m a ^ 2) := by
  rw [profileLaw_expectation hm (fun x : ℝ => x ^ 2)]
  exact blockMean_sq_lower hm

lemma profileLaw_fourth_moment {m : ℕ} (hm : 0 < m) :
    expectation (profileLaw m hm) (fun a => profileValue m a ^ 4) ≤
      4 * (expectation (profileLaw m hm) (fun a => profileValue m a ^ 2)) ^ 2 := by
  rw [profileLaw_expectation hm (fun x : ℝ => x ^ 4),
    profileLaw_expectation hm (fun x : ℝ => x ^ 2)]
  exact blockMean_fourth_le hm

end
end Riesz
