import Oscillation.RealGrid
import Oscillation.Exponential

namespace Oscillation
noncomputable section
open MeasureTheory
open scoped ENNReal

lemma density_laplace_coefficient {b : ℝ} (hb : 0 < b) {n h M : ℕ} (hM : 0 < M)
    (hd : (n : ℝ) ≤ h * M / (4 * b ^ 3)) :
    Real.sqrt (b * n / M) ≤ Real.sqrt (h : ℝ) / (2 * b) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
  apply (div_le_div_iff₀ hMR (by positivity)).mpr
  have hd' := (le_div_iff₀ (show 0 < 4 * b ^ 3 by positivity)).mp hd
  nlinarith

lemma sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg _) (Real.exp_nonneg _)).mpr
  rw [← Real.exp_add]
  congr 1
  ring

lemma laplace_histogram_rhs {b : ℝ} (hb : 0 < b) {n M : ℕ} (hMn : M ≤ n) :
    Real.exp (n : ℝ) * Real.sqrt ((2 : ℝ) ^ (n + M) * (4 / b) ^ n) ≤
      Real.exp ((n : ℝ) * (1 + 2 * Real.log 2 - Real.log b / 2)) := by
  have hp (a : ℝ) (ha : 0 < a) (k : ℕ) : a ^ k = Real.exp ((k : ℝ) * Real.log a) := by
    rw [Real.exp_nat_mul, Real.exp_log ha]
  rw [hp 2 (by norm_num), hp (4 / b) (by positivity), ← Real.exp_add, sqrt_exp_half,
    ← Real.exp_add, Real.log_div (by norm_num) hb.ne']
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  rw [h4]
  apply Real.exp_le_exp.mpr
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hl : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hMnR hl]

theorem small_event_of_laplace {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (Z : Ω → ℝ) (t a B : ℝ) (ht : 0 < t)
    (hi : Integrable (fun ω ↦ Real.exp (-t * Z ω)) μ)
    (hLap : (∫ ω, Real.exp (-t * Z ω) ∂μ) ≤ B) :
    μ {ω | Z ω ≤ a} ≤ ENNReal.ofReal (Real.exp (t * a) * B) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω ↦ Real.exp_nonneg (-t * Z ω))) hi (Real.exp (-t * a))
  have hr : μ.real {ω | Real.exp (-t * a) ≤ Real.exp (-t * Z ω)} ≤
      Real.exp (t * a) * B := by
    calc
      _ ≤ (∫ ω, Real.exp (-t * Z ω) ∂μ) / Real.exp (-t * a) := by
        apply (le_div_iff₀ (Real.exp_pos _)).mpr
        nlinarith
      _ ≤ B / Real.exp (-t * a) := div_le_div_of_nonneg_right hLap (Real.exp_nonneg _)
      _ = Real.exp (t * a) * B := by rw [neg_mul, Real.exp_neg, div_inv_eq_mul]; ring
  have he : μ {ω | Real.exp (-t * a) ≤ Real.exp (-t * Z ω)} ≤
      ENNReal.ofReal (Real.exp (t * a) * B) := by
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.ofReal_le_ofReal hr
  apply (measure_mono ?_).trans he
  intro ω hω
  apply Real.exp_le_exp.mpr
  change Z ω ≤ a at hω
  nlinarith

lemma fixed_scale_exponent {n h : ℕ} {b M : ℝ} (_hb : 0 < b) (hM : 0 < M) (hh : 0 < h) :
    Real.exp ((M / Real.sqrt h) * (2 * ((n : ℝ) * Real.sqrt h / (8 * M)))) *
      Real.exp ((n : ℝ) * (1 + 2 * Real.log 2 - Real.log b / 2)) =
      Real.exp (-(Real.log b / 2 - 2 * Real.log 2 - 5 / 4) * n) := by
  have hs : 0 < Real.sqrt (h : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

end
end Oscillation
