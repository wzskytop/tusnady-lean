import Oscillation.SequentialCrowding
import Oscillation.DirectScale

namespace Oscillation.Direct
noncomputable section
open MeasureTheory Finset Riesz Riesz.PointSets
open scoped ENNReal Classical
set_option maxHeartbeats 1000000

lemma layer_crowding_exp {n b h : ℕ} (hn : 0<n) (hb : 4<b)
    (hMn : b^(h-1)≤n) {j : ℕ} (hj : j<h) :
    (∫ P, Real.exp (Real.log ((b:ℝ)/4)*((n:ℝ)-Real.sqrt ((b:ℝ)*n/(b^(h-1):ℕ))*
      pointLayerMass b h (by omega) j P)) ∂pointSampleLaw n) ≤ 2^n := by
  have hb0 : 0<b := by omega
  let K := b^j
  let V := b^(h-j-1)
  let m := b^j
  have hK : 0<K := pow_pos hb0 _
  have hV : 0<V := pow_pos hb0 _
  have hm : 0<m := pow_pos hb0 _
  have hdim : K*V=b^(h-1) := layer_comparison_size hj
  have hfine : V*(b*m)=b^h := layer_fine_size hj
  letI : MeasurableSpace (Option (Fin (K*V))) := ⊤
  have H := sequential_mass_exp (μI.prod μI) hn (Nat.mul_pos hK hV)
    (by simpa only [hdim] using hMn) (by exact_mod_cast hb : (4:ℝ)<b)
    (rectangularBucket K V b m hK hV hb0 hm)
    (rectangularBucket_measurable K V b m hK hV hb0 hm)
    (fun c => by
      have hc := rectangularBucket_good_mass K V b m hK hV hb0 hm c
      simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤1/(K*V:ℕ))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hc)
    (by
      have hc := rectangularBucket_bad_mass K V b m hK hV (by omega : 4≤b) hm
      simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2/(b:ℝ))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hc)
  simp_rw [bucketSquareRootSum_eq_interiorMass] at H
  rw [hdim] at H
  simp_rw [sampleCells_eq_of_grid_eq hfine _ (pow_pos hb0 h)] at H
  exact H

/-- Joint exponential estimate. Jensen uses the common sample without assuming stage independence. -/
lemma stages_crowding_exp {n b h : ℕ} (hn : 0<n) (hb : 4<b)
    (hh : 0<h) (hMn : b^(h-1)≤n) :
    (∫ P, Real.exp (Real.log ((b:ℝ)/4)*((n:ℝ)-Real.sqrt ((b:ℝ)*n/(b^(h-1):ℕ))/h*
      ∑ j ∈ range h, pointLayerMass b h (by omega) j P)) ∂pointSampleLaw n) ≤ 2^n := by
  letI : NeZero h := ⟨by omega⟩
  let t := Real.log ((b:ℝ)/4)
  let v := Real.sqrt ((b:ℝ)*n/(b^(h-1):ℕ))
  let S := pointLayerMass (n:=n) b h (by omega)
  have ht : 0≤t := Real.log_nonneg (by
    have H : (4:ℝ)<b := by exact_mod_cast hb
    linarith)
  have hv : 0≤v := Real.sqrt_nonneg _
  have hi (j : Fin h) : Integrable (fun P => Real.exp (t*(n-v*S j P))) (pointSampleLaw n) :=
    integrable_exp_of_bounded ((measurable_const.sub ((measurable_pointLayerMass b h (by omega) j).const_mul v)).const_mul t)
      (t*n) (fun P => by have H := pointLayerMass_nonneg b h (by omega) j P; dsimp [S]; exact mul_le_mul_of_nonneg_left (sub_le_self _ (mul_nonneg hv H)) ht)
  have hfin : Integrable (fun P => finAvg (fun j : Fin h => Real.exp (t*(n-v*S j P)))) (pointSampleLaw n) := by
    unfold finAvg
    exact (integrable_finsetSum univ (fun j _=>hi j)).div_const _
  have heq (P) : finAvg (fun j : Fin h => t*(n-v*S j P)) = t*(n-v/h*∑j∈range h,S j P) := by
    simp only [finAvg, Fintype.card_fin, mul_sub, sum_sub_distrib, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun j => S j P) h]
    have hh0 : (h:ℝ)≠0 := by positivity
    field_simp
    <;> ring
  have hm : Measurable (fun P => t*(n-v/h*∑j∈range h,S j P)) := by
    exact (measurable_const.sub ((Finset.measurable_sum (range h) (fun j _ => measurable_pointLayerMass b h (by omega) j)).const_mul (v/h))).const_mul t
  have hInt := integrable_exp_of_bounded (μ:=pointSampleLaw n) hm (t*n) (fun P => by
    have H : 0≤∑j∈range h,S j P := sum_nonneg (fun j _=>pointLayerMass_nonneg b h (by omega) j P)
    have H' : 0≤v/(h:ℝ)*(∑j∈range h,S j P) := by positivity
    nlinarith)
  calc
    _ ≤ ∫ P, finAvg (fun j : Fin h => Real.exp (t*(n-v*S j P))) ∂pointSampleLaw n := by
      apply integral_mono hInt hfin
      intro P
      dsimp only
      rw [← heq]
      exact exp_finAvg_le_finAvg_exp _
    _ = finAvg (fun j : Fin h => ∫ P, Real.exp (t*(n-v*S j P)) ∂pointSampleLaw n) := integral_finAvg _ hi
    _ ≤ finAvg (fun _j : Fin h => (2:ℝ)^n) := finAvg_mono (fun j=>layer_crowding_exp hn hb hMn j.isLt)
    _ = _ := finAvg_const _

/-- R17 Lemma 2.5, written with its square-root mass threshold. -/
theorem crowding_bound {n b h : ℕ} (hn : 0<n) (hb : 4<b)
    (hh : 0<h) (hMn : b^(h-1)≤n) :
    (pointSampleLaw n).real {P | (∑j∈range h,pointLayerMass b h (by omega) j P) ≤
      h*massFloor n b (b^(h-1):ℕ)} ≤ 2^n*Real.exp (-Real.log ((b:ℝ)/4)*n/2) := by
  let t := Real.log ((b:ℝ)/4)
  let v := Real.sqrt ((b:ℝ)*n/(b^(h-1):ℕ))
  let S := fun P => ∑j∈range h,pointLayerMass (n:=n) b h (by omega) j P
  let E := fun P => Real.exp (t*(n-v/h*S P))
  have ht : 0≤t := Real.log_nonneg (by
    have H : (4:ℝ)<b := by exact_mod_cast hb
    linarith)
  have hv : 0<v := by dsimp [v]; positivity
  have hhR : (0:ℝ)<h := by positivity
  have hm : Measurable (fun P => t*(n-v/h*S P)) := by
    exact (measurable_const.sub ((Finset.measurable_sum (range h) (fun j _ => measurable_pointLayerMass b h (by omega) j)).const_mul (v/h))).const_mul t
  have hi : Integrable E (pointSampleLaw n) := integrable_exp_of_bounded hm (t*n) (fun P => by
    have H : 0≤S P := sum_nonneg (fun j _=>pointLayerMass_nonneg b h (by omega) j P)
    have H' : 0≤v/(h:ℝ)*S P := by positivity
    nlinarith)
  have hs : {P | S P≤h*massFloor n b (b^(h-1):ℕ)} ⊆ {P | Real.exp (t*n/2)≤E P} := by
    intro P hP
    apply Real.exp_le_exp.mpr
    have heq : v/h*(h*massFloor n b (b^(h-1):ℕ))=(n:ℝ)/2 := by
      dsimp [massFloor,v]; field_simp
    have H := mul_le_mul_of_nonneg_left hP (show 0≤v/(h:ℝ) by positivity)
    rw [heq] at H
    nlinarith
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ:=pointSampleLaw n)
    (Filter.Eventually.of_forall (fun P=>Real.exp_nonneg (t*(n-v/h*S P)))) hi (Real.exp (t*n/2))
  have hI := stages_crowding_exp hn hb hh hMn
  have H := mul_le_mul_of_nonneg_left (measureReal_mono (μ:=pointSampleLaw n) hs) (Real.exp_nonneg (t*n/2))
  have he : Real.exp (t*n/2)*(2^n*Real.exp (-t*n/2))=(2:ℝ)^n := by
    rw [mul_left_comm, ← Real.exp_add]
    ring_nf
    simp
  change (pointSampleLaw n).real {P | S P≤_} ≤ _
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (t*n/2))).mp
  rw [he]
  exact H.trans (hMarkov.trans hI)

end
end Oscillation.Direct
