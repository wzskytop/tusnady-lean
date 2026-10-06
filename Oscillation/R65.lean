import Oscillation.R17Parameters

/- R65 reuses the all-transition union route. The r17 modules remain available
   for comparison, but dependency auditing excludes them from the main proof. -/
namespace Oscillation.R65
noncomputable section
open MeasureTheory Riesz.PointSets
open scoped ENNReal

/-- R65 Lemma 2.5(ii), one transition. All integer bases b ≥ 3. -/
theorem bad_transition_bound {n b h : ℕ} (hn : 0 < n) (hb : 3 ≤ b)
    (hMn : b^(h-1) ≤ n) {j : ℕ} (hj : j < h) :
    (pointSampleLaw n).real (Direct.paperGoodTransition (n := n) b h (by omega) j)ᶜ ≤
      (48/(b:ℝ))^((n:ℝ)/2) := by
  by_cases hb4 : 4 ≤ b
  · have H := Direct.paper_bad_transition_bound hn hb4 hMn hj
    rw [Direct.geometry_factor_eq (by positivity)] at H
    exact H
  · have hbR : (0:ℝ) < b := by positivity
    have hb48 : (b:ℝ) ≤ 48 := by exact_mod_cast (show b ≤ 48 by omega)
    have hbase : (1:ℝ) ≤ 48/b := (le_div_iff₀ hbR).mpr (by simpa using hb48)
    exact measureReal_le_one.trans (Real.one_le_rpow hbase (by positivity))

/-- R65 Lemma 2.5(ii), all transitions, without a parity assumption. -/
theorem all_good_compl_bound {n b h : ℕ} (hn : 0 < n) (hb : 3 ≤ b)
    (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (pointSampleLaw n).real (Direct.allGood (n := n) b h (by omega))ᶜ ≤
      h*(48/(b:ℝ))^((n:ℝ)/2) := by
  by_cases hb4 : 4 ≤ b
  · exact Direct.allGood_compl_bound_exact hn hb4 hMn
  · have hbR : (0:ℝ) < b := by positivity
    have hb48 : (b:ℝ) ≤ 48 := by exact_mod_cast (show b ≤ 48 by omega)
    have hbase : (1:ℝ) ≤ 48/b := (le_div_iff₀ hbR).mpr (by simpa using hb48)
    have hr := Real.one_le_rpow hbase (show (0:ℝ) ≤ n/2 by positivity)
    have hhR : (1:ℝ) ≤ h := by exact_mod_cast hh
    exact measureReal_le_one.trans (by nlinarith)

/-- R65 Proposition 2.7: exact displayed constants, even-base local proof. -/
theorem simultaneous_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (heven : Even b) (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n ((h:ℝ)*Real.sqrt ((n:ℝ)/(b^(h-1):ℕ))/(64*(b:ℝ)^(3/2:ℝ)))) ≤
      h*(48/(b:ℝ))^((n:ℝ)/2) + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) :=
  Direct.proposition_2_7 hn hb heven hh hMn

/-- R65 Theorem 1.1, with no unproved probability estimates as premises. -/
theorem paper_lower_bound : Riesz.PaperLowerBound := Direct.paper_lower_bound

end
end Oscillation.R65
