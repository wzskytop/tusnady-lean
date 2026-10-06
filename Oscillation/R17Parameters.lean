import Oscillation.DirectParameters
import Oscillation.R17Scale

namespace Oscillation.Direct
noncomputable section
open MeasureTheory Riesz Riesz.PointSets Oscillation.Parameters
open scoped ENNReal
set_option maxHeartbeats 1000000

lemma r17_failure_sum {A : ℝ} {n h : ℕ} (hn : 0<n) (hhn : h≤n)
    {b M : ℝ} (hb : 0<b)
    (hgeom : 4*Real.sqrt (3/b)≤Real.exp (-(A+2)))
    (hnoise : A+2+Real.log 2≤b/4096)
    (hscale : (n:ℝ)<2*h*M/b^4) :
    (16/b)^((n:ℝ)/2)+2^n*Real.exp (-(h:ℝ)*M/(2048*b^3)) ≤ Real.exp (-A*n) := by
  have hhR : (1:ℝ)≤h := by
    have hh : 0<h := by
      by_contra H
      have he : h=0 := by omega
      simp only [he,Nat.cast_zero,mul_zero,zero_mul,zero_div] at hscale
      have : (0:ℝ)≤n := by positivity
      linarith
    exact_mod_cast hh
  apply le_trans _ (failure_sum hn hhn hb hgeom hnoise hscale)
  apply add_le_add _ le_rfl
  calc
    _ ≤ (48/b)^((n:ℝ)/2) := Real.rpow_le_rpow (by positivity)
      (by apply div_le_div_of_nonneg_right (by norm_num) hb.le) (by positivity)
    _ = (4*Real.sqrt (3/b))^n := (geometry_factor_eq hb).symm
    _ ≤ h*(4*Real.sqrt (3/b))^n := by nlinarith [show 0≤(4*Real.sqrt (3/b))^n by positivity]

theorem r17_paper_lower_bound : Riesz.PaperLowerBound := by
  intro A hA
  obtain ⟨L,hL,hLA⟩ := exists_base (1024*(A+10))
  have hLA' : 4096*(A+10) ≤ (L:ℝ) := by linarith
  have hL6 : 7 ≤ L := by
    have hh : (7:ℝ) ≤ L := by linarith
    exact_mod_cast hh
  let b : ℕ := 2^L
  have hb64 : 128 ≤ b := by
    calc 128 = 2^7 := by norm_num
         _ ≤ 2^L := Nat.pow_le_pow_right (by norm_num) hL6
  have hb0 : 0 < b := by omega
  have hbR : (128:ℝ) ≤ b := by exact_mod_cast hb64
  have hb : (0:ℝ) < b := by positivity
  have heven : Even b := Even.pow_of_ne_zero (by norm_num : Even (2:ℕ)) (by omega)
  have hrates := direct_rates hA hLA'
  have hgeom : 4*Real.sqrt (3/(b:ℝ)) ≤ Real.exp (-(A+2)) :=
    geometry_rate hb (by simpa only [b,Nat.cast_pow,Nat.cast_ofNat] using hrates.1)
  have hnoise : A+2+Real.log 2 ≤ (b:ℝ)/4096 := by
    simpa only [b,Nat.cast_pow,Nat.cast_ofNat] using hrates.2
  refine ⟨paperConstant b L, paperConstant_pos hb L, ?_⟩
  intro n hn
  obtain ⟨k,hk,hmax⟩ := exists_maximal_scale (by linarith : (2:ℝ) ≤ b) n hn
  have hlog : Real.logb 2 (n:ℝ) < (L+1:ℝ)*(k+1:ℝ) :=
    logarithmic_scale (by omega) hn (by simpa only [b,Nat.cast_pow,Nat.cast_ofNat] using hmax)
  have hlog0 : 0 ≤ Real.logb 2 (n:ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
  have hc : paperConstant b L*(Real.logb 2 (n:ℝ))^(3/2:ℝ) ≤
      thresholdConstant b L*(Real.logb 2 (n:ℝ))^(3/2:ℝ) :=
    mul_le_mul_of_nonneg_right (paperConstant_le_threshold (by linarith : (64:ℝ) ≤ b) L) (by positivity)
  apply goodEvent_of_bad n _ (Real.exp (-A*n)) (Real.exp_nonneg _)
  by_cases hMn : b^k ≤ n
  · have hMnR : ((b:ℝ)^k) ≤ n := by exact_mod_cast hMn
    have ht := hc.trans (threshold_below_scale (by linarith : (2:ℝ) ≤ b) hlog0 hlog.le hk)
    have ht' := old_threshold_le_direct (by omega : 0<n) (by omega : 0<k+1) hb
      (show 0 < (b:ℝ)^k by positivity) (by
        simpa only [Nat.cast_add,Nat.cast_one] using direct_density (by linarith : (128:ℝ) ≤ b) hk hmax)
    simp only [Nat.cast_add,Nat.cast_one] at ht'
    have hthreshold : paperConstant b L*(Real.logb 2 (n:ℝ))^(3/2:ℝ) ≤
        threshold n (k+1) b (b^((k+1)-1):ℕ) := by
      simpa only [Nat.add_sub_cancel,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using ht.trans ht'
    have hprob := r17_simultaneous_bound (by omega : 0<n) (by omega : 4<b) heven
      (by omega : 0<k+1) (by simpa only [Nat.add_sub_cancel] using hMn)
    have hfail := r17_failure_sum (A:=A) (n:=n) (h:=k+1) (by omega)
      (stages_le_sample (by omega : 2 ≤ b) (by omega : 0 < k+1)
        (by simpa only [Nat.add_sub_cancel] using hMn)) hb hgeom hnoise
      (by simpa only [Nat.cast_add,Nat.cast_one] using (maximal_scale_bounds (by linarith : (2:ℝ)≤b) hk hmax).2)
    have hf : (unifPts n).real (badSet n (threshold n (k+1) b (b^((k+1)-1):ℕ))) ≤ Real.exp (-A*n) := by
      apply hprob.trans
      simpa only [Nat.add_sub_cancel,Nat.cast_pow] using hfail
    have hs : badSet n (paperConstant b L*(Real.logb 2 (n:ℝ))^(3/2:ℝ)) ⊆
        badSet n (threshold n (k+1) b (b^((k+1)-1):ℕ)) := by
      rw [badSet_eq_iUnion_fixedColorBad,badSet_eq_iUnion_fixedColorBad]
      exact Set.iUnion_mono (fun χ => fixedColorBad_mono hthreshold χ)
    have H := (measureReal_mono hs (measure_ne_top _ _)).trans hf
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal H
  · have hnM : (n:ℝ) < (b:ℝ)^k := by exact_mod_cast Nat.lt_of_not_ge hMn
    rw [badSet_measure_zero n hn _ (hc.trans_lt (threshold_small (by linarith : (2:ℝ)≤b) hlog0 hlog.le hk hnM))]
    exact bot_le

end
end Oscillation.Direct
