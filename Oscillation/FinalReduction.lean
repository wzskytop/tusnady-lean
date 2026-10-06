import Oscillation.Parameters
import Riesz.Colorings
import Riesz.Target

/-! Final scale selection. The explicit fixed-scale premise is discharged in Main. -/
namespace Oscillation
noncomputable section
open MeasureTheory Riesz Riesz.PointSets Parameters
open scoped ENNReal

def scaleThreshold (n k L : ℕ) : ℝ :=
  (n : ℝ) * Real.sqrt (k + 1 : ℝ) / (8 * ((2 : ℝ) ^ L) ^ k)

def scaleRate (L : ℕ) : ℝ :=
  Real.log ((2 : ℝ) ^ L) / 2 - 2 * Real.log 2 - 5 / 4

/-- The concrete finite-oscillation estimate required by the final reduction. -/
def FixedScaleEstimate : Prop :=
  ∀ L : ℕ, 4 ≤ L → ∀ n k : ℕ, 1 ≤ n → ((2 : ℝ) ^ L) ^ k ≤ n →
    (n : ℝ) ≤ (k + 1 : ℝ) * ((2 : ℝ) ^ L) ^ k / (4 * ((2 : ℝ) ^ L) ^ 3) →
    ∀ χ : Fin n → Bool,
      unifPts n (fixedColorBad n (scaleThreshold n k L) χ) ≤
        ENNReal.ofReal (Real.exp (-(scaleRate L) * n))

lemma fixedColorBad_mono {n : ℕ} {a b : ℝ} (hab : a ≤ b) (χ : Fin n → Bool) :
    fixedColorBad n a χ ⊆ fixedColorBad n b χ := by
  intro X hX x hx y hy
  exact (hX x hx y hy).trans hab

theorem paper_lower_bound_of_fixed_scale (hfixed : FixedScaleEstimate) : Riesz.PaperLowerBound := by
  intro A hA
  obtain ⟨L, hL, hLA⟩ := exists_base A
  let b : ℝ := (2 : ℝ) ^ L
  have hb : (16 : ℝ) ≤ b := by
    calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ L := pow_le_pow_right₀ (by norm_num) hL
  have hbp : 0 < b := by linarith
  have hb64 : (64 : ℝ) ≤ b := by
    have hL6 : 6 ≤ L := by
      have hh : (6 : ℝ) ≤ L := by linarith
      exact_mod_cast hh
    calc (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ L := pow_le_pow_right₀ (by norm_num) hL6
  refine ⟨paperConstant b L, paperConstant_pos hbp L, ?_⟩
  intro n hn
  obtain ⟨k, hk, hmax⟩ := exists_maximal_scale (by linarith : 2 ≤ b) n hn
  have hlog : Real.logb 2 (n : ℝ) < (L + 1 : ℝ) * (k + 1 : ℝ) :=
    logarithmic_scale (by omega) hn hmax
  have hlog0 : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
  have hc : paperConstant b L * (Real.logb 2 (n : ℝ)) ^ (3 / 2 : ℝ) ≤
      thresholdConstant b L * (Real.logb 2 (n : ℝ)) ^ (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right (paperConstant_le_threshold hb64 L) (by positivity)
  apply goodEvent_of_bad n _ (Real.exp (-A * n)) (Real.exp_pos _).le
  by_cases hnM : b ^ k ≤ n
  · have ht : paperConstant b L * (Real.logb 2 (n : ℝ)) ^ (3 / 2 : ℝ) ≤
        scaleThreshold n k L := hc.trans (threshold_below_scale (by linarith) hlog0 hlog.le hk)
    have hd : (n : ℝ) ≤ (k + 1 : ℝ) * b ^ k / (4 * b ^ 3) :=
      density_bound (by linarith) hk hmax
    have hcolor (χ : Fin n → Bool) : unifPts n (fixedColorBad n
        (paperConstant b L * (Real.logb 2 (n : ℝ)) ^ (3 / 2 : ℝ)) χ) ≤
        ENNReal.ofReal (Real.exp (-(scaleRate L) * n)) :=
      (measure_mono (fixedColorBad_mono ht χ)).trans (hfixed L hL n k hn hnM hd χ)
    have hu := badSet_measure_le_of_fixedColor n _ _ hcolor
    apply hu.trans
    have hr : A + Real.log 2 ≤ scaleRate L := failure_exponent hA hLA
    have hexp : Real.exp (-(scaleRate L) * n) ≤ Real.exp (-(A + Real.log 2) * n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hreal : (2 : ℝ) ^ n * Real.exp (-(scaleRate L) * n) ≤ Real.exp (-A * n) := by
      calc
        _ ≤ (2 : ℝ) ^ n * Real.exp (-(A + Real.log 2) * n) := by gcongr
        _ = _ := coloring_union A n
    have he := ENNReal.ofReal_le_ofReal hreal
    simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ n),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using he
  · rw [badSet_measure_zero n hn _
      (hc.trans_lt (threshold_small (by linarith) hlog0 hlog.le hk (lt_of_not_ge hnM)))]
    exact bot_le

end
end Oscillation
