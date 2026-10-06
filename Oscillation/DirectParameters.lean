import Oscillation.UnionScale

namespace Oscillation.Direct
noncomputable section
open MeasureTheory Riesz Riesz.PointSets Oscillation.Parameters
open scoped ENNReal
set_option maxHeartbeats 1000000

lemma direct_density {b : ℝ} (hb : 128 ≤ b) {n k : ℕ}
    (hk : Admissible b n k) (hmax : ∀ m, Admissible b n m → m ≤ k) :
    (n:ℝ) ≤ (k+1:ℝ)*b^k/(64*b^3) := by
  have hbp : 0 < b := by linarith
  apply (maximal_scale_bounds (by linarith) hk hmax).2.le.trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hnon : 0 ≤ (k+1:ℝ)*b^k*b^3 := by positivity
  nlinarith [mul_nonneg hnon (sub_nonneg.mpr hb)]

lemma old_threshold_le_direct {n h : ℕ} (hn : 0 < n) (hh : 0 < h)
    {b M : ℝ} (hb : 0 < b) (hM : 0 < M)
    (hd : (n:ℝ) ≤ h*M/(64*b^3)) :
    (n:ℝ)*Real.sqrt h/(8*M) ≤ threshold n h b M := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hr : 0 < Real.sqrt (b*n/M) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt hhR.le
  have hsroot : Real.sqrt (b*n/M) ≤ Real.sqrt h/(8*b) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, hs]
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    have hd' := (le_div_iff₀ (show 0 < 64*b^3 by positivity)).mp hd
    nlinarith
  have hprod : 8*b*Real.sqrt h*Real.sqrt (b*n/M) ≤ h := by
    have ht := mul_le_mul_of_nonneg_left hsroot (show 0 ≤ 8*b*Real.sqrt h by positivity)
    have he : 8*b*Real.sqrt h*(Real.sqrt h/(8*b)) = h := by field_simp; nlinarith
    exact ht.trans_eq he
  unfold threshold drift massFloor
  field_simp
  simp only [mul_comm b (n:ℝ)] at hprod
  nlinarith

lemma geometry_rate {A b : ℝ} (hb : 0 < b)
    (hlog : A+3+2*Real.log 2 ≤ Real.log b/2) :
    4*Real.sqrt (3/b) ≤ Real.exp (-(A+2)) := by
  have he : 3/b = Real.exp (Real.log 3-Real.log b) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_log hb]
  have h4 : (4:ℝ) = Real.exp (2*Real.log 2) := by
    rw [show (2:ℝ)*Real.log 2 = (2:ℕ)*Real.log 2 by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num)]; norm_num
  rw [he,sqrt_exp_half,h4,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  linarith

lemma direct_rates {A : ℝ} (hA : 0 < A) {L : ℕ}
    (hLA : 4096*(A+10) ≤ (L:ℝ)) :
    A+3+2*Real.log 2 ≤ Real.log ((2:ℝ)^L)/2 ∧
      A+2+Real.log 2 ≤ (2:ℝ)^L/4096 := by
  have hlo : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hhi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hpow : (L:ℝ) ≤ (2:ℝ)^L := by exact_mod_cast (Nat.lt_two_pow_self (n:=L)).le
  constructor
  · rw [Real.log_pow]
    have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (α:=ℝ) L)
    nlinarith
  · linarith

lemma failure_sum {A : ℝ} {n h : ℕ} (hn : 0 < n) (hhn : h ≤ n)
    {b M : ℝ} (hb : 0 < b)
    (hgeom : 4*Real.sqrt (3/b) ≤ Real.exp (-(A+2)))
    (hnoise : A+2+Real.log 2 ≤ b/4096)
    (hscale : (n:ℝ) < 2*h*M/b^4) :
    h*(4*Real.sqrt (3/b))^n + 2^n*Real.exp (-(h:ℝ)*M/(2048*b^3)) ≤
      Real.exp (-A*n) := by
  have hnoise' : (A+2+Real.log 2)*n ≤ h*M/(2048*b^3) := by
    have hs := (lt_div_iff₀ (show 0 < b^4 by positivity)).mp hscale
    have hn0 : (0:ℝ) ≤ n := by positivity
    apply le_trans (mul_le_mul_of_nonneg_right hnoise hn0)
    apply (le_div_iff₀ (show 0 < 2048*b^3 by positivity)).mpr
    nlinarith
  have hg : (4*Real.sqrt (3/b))^n ≤ Real.exp (-(A+2)*n) := by
    calc
      _ ≤ (Real.exp (-(A+2)))^n := pow_le_pow_left₀ (by positivity) hgeom n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have ht : (2:ℝ)^n*Real.exp (-(h:ℝ)*M/(2048*b^3)) ≤ Real.exp (-(A+2)*n) := by
    calc
      _ ≤ (2:ℝ)^n*Real.exp (-(A+2+Real.log 2)*n) := by
        gcongr
        convert neg_le_neg hnoise' using 1 <;> ring
      _ = _ := coloring_union (A+2) n
  calc
    _ ≤ ((h:ℝ)+1)*Real.exp (-(A+2)*n) := by
      have H := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α:=ℝ) h)
      nlinarith
    _ ≤ _ := absorb_all_stages hn hhn

theorem paper_lower_bound : Riesz.PaperLowerBound := by
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
    have hprob := union_simultaneous_bound (by omega : 0<n) (by omega : 4≤b) heven
      (by omega : 0<k+1) (by simpa only [Nat.add_sub_cancel] using hMn)
    have hfail := failure_sum (A:=A) (n:=n) (h:=k+1) (by omega)
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
