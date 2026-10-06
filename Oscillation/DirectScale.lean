import Oscillation.DirectAccumulation

namespace Oscillation.Direct
noncomputable section
open MeasureTheory Finset Riesz Riesz.PointSets
open scoped ENNReal Classical
set_option maxHeartbeats 1000000

def massFloor (n : ℕ) (b M : ℝ) : ℝ := n/(2*Real.sqrt (b*n/M))
def drift (n : ℕ) (b M : ℝ) : ℝ := massFloor n b M/(4*b*M)
def threshold (n h : ℕ) (b M : ℝ) : ℝ := h*drift n b M/8

def good {n : ℕ} (b h : ℕ) (hb : 0 < b) : Set (Fin n → ℝ × ℝ) :=
  {P | (h:ℝ)*massFloor n b (b^(h-1):ℕ)/2 ≤ ∑ j ∈ range h, pointLayerMass b h hb j P}

lemma layer_bad_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (hMn : b^(h-1) ≤ n) {j : ℕ} (hj : j < h) :
    (pointSampleLaw n).real
      {P | pointLayerMass b h (by omega) j P < massFloor n b (b^(h-1):ℕ)} ≤
      (4*Real.sqrt (3/b))^n := by
  have hb0 : 0 < b := by omega
  let K := b^j
  let V := b^(h-j-1)
  let m := b^j
  have hK : 0 < K := pow_pos hb0 _
  have hV : 0 < V := pow_pos hb0 _
  have hm : 0 < m := pow_pos hb0 _
  have hdim : K*V = b^(h-1) := layer_comparison_size hj
  have hfine : V*(b*m) = b^h := layer_fine_size hj
  have H := bucket_mass_small (μI.prod μI) hn (Nat.mul_pos hK hV)
    (by simpa only [hdim] using hMn) (by exact_mod_cast (show 3 ≤ b by omega) : (3:ℝ) ≤ b)
    (rectangularBucket K V b m hK hV hb0 hm)
    (fun c => by
      have hc := rectangularBucket_good_mass K V b m hK hV hb0 hm c
      simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1/(K*V:ℕ))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hc)
    (by
      have hc := rectangularBucket_bad_mass K V b m hK hV hb hm
      simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2/(b:ℝ))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hc)
  simp_rw [bucketSquareRootSum_eq_interiorMass] at H
  rw [hdim] at H
  simp_rw [sampleCells_eq_of_grid_eq hfine _ (pow_pos hb0 h)] at H
  exact H

/-- Markov on the number of bad stages; no independence between stages is used. -/
lemma bad_geometry_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (pointSampleLaw n).real (good (n := n) b h (by omega))ᶜ ≤
      2 * (4*Real.sqrt (3/b))^n := by
  have hb0 : 0 < b := by omega
  let μ := pointSampleLaw n
  let q := massFloor n b (b^(h-1):ℕ)
  let E := fun j => {P : Fin n → ℝ × ℝ | pointLayerMass b h hb0 j P < q}
  let B := fun P => ∑ j ∈ range h, (E j).indicator (fun _ => (1:ℝ)) P
  have hm (j : ℕ) : MeasurableSet (E j) :=
    measurableSet_lt (measurable_pointLayerMass b h hb0 j) measurable_const
  have hi (j : ℕ) : Integrable ((E j).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const _).indicator (hm j)
  have hB : Integrable B μ := integrable_finsetSum _ (fun j _ => hi j)
  have hB0 (P) : 0 ≤ B P := sum_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => by norm_num) P)
  have hq : 0 < q := by dsimp [q,massFloor]; positivity
  have hs : (good (n:=n) b h hb0)ᶜ ⊆ {P | (h:ℝ)/2 ≤ B P} := by
    intro P hP
    have hmass : (h:ℝ)*q-q*B P ≤ ∑ j ∈ range h, pointLayerMass b h hb0 j P := by
      have hpoint (j : ℕ) : q-q*(E j).indicator (fun _ => (1:ℝ)) P ≤ pointLayerMass b h hb0 j P := by
        by_cases hj : P ∈ E j
        · simpa [Set.indicator_of_mem hj] using pointLayerMass_nonneg b h hb0 j P
        · have hge : q ≤ pointLayerMass b h hb0 j P := le_of_not_gt hj
          simpa [Set.indicator_of_notMem hj] using hge
      have H := sum_le_sum (s:=range h) (fun j _ => hpoint j)
      simpa [sum_sub_distrib, mul_sum, B] using H
    have hsmall : (∑ j ∈ range h, pointLayerMass b h hb0 j P) < (h:ℝ)*q/2 := lt_of_not_ge hP
    change (h:ℝ)/2 ≤ B P
    nlinarith
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (μ:=μ) (Filter.Eventually.of_forall hB0) hB ((h:ℝ)/2)
  have hInt : (∫ P, B P ∂μ) ≤ h*(4*Real.sqrt (3/b))^n := by
    rw [show (∫ P, B P ∂μ) = ∑ j ∈ range h, ∫ P, (E j).indicator (fun _ => (1:ℝ)) P ∂μ from
      integral_finsetSum _ (fun j _ => hi j)]
    calc
      _ = ∑ j ∈ range h, μ.real (E j) := by
        apply sum_congr rfl
        intro j _
        exact integral_indicator_one (hm j)
      _ ≤ ∑ _j ∈ range h, (4*Real.sqrt (3/b))^n :=
        sum_le_sum (fun j hj => layer_bad_bound hn hb hMn (mem_range.mp hj))
      _ = _ := by simp
  have hmono := measureReal_mono (μ:=μ) hs (measure_ne_top _ _)
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have H := mul_le_mul_of_nonneg_left hmono (show (0:ℝ) ≤ h/2 by positivity)
  change μ.real _ ≤ _
  nlinarith

lemma drift_pos {n : ℕ} (hn : 0 < n) {b M : ℝ} (hb : 0 < b) (hM : 0 < M) :
    0 < drift n b M := by unfold drift massFloor; positivity

lemma drift_exponent {n : ℕ} (hn : 0 < n) {b M : ℝ} (hb : 0 < b) (hM : 0 < M) :
    (drift n b M)^2*M^2/(32*n) = M/(2048*b^3) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hr : 0 < Real.sqrt (b*n/M) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ b*n/M by positivity)
  have hs' : Real.sqrt (b*n/M)^2*M = b*n := (eq_div_iff hM.ne').mp hs
  unfold drift massFloor
  field_simp
  simp only [mul_comm b (n:ℝ)] at hs'
  nlinarith [hs']

lemma loss_tail {n b h : ℕ} (hn : 0 < n) (hb : 0 < b) (heven : Even b)
    (hh : 0 < h) (χ : Fin n → Bool) :
    (pointSampleLaw n).real {P | loss b h hb χ P ≤ -(h:ℝ)*drift n b (b^(h-1):ℕ)/4} ≤
      Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  let M : ℝ := (b^(h-1):ℕ)
  let d := drift n b M
  let u := d*M^2/(4*n)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hM : 0 < M := by dsimp [M]; positivity
  have hd : 0 < d := drift_pos hn hbR hM
  have hu : 0 < u := by dsimp [u]; positivity
  have H := small_event_of_laplace (pointSampleLaw n) (loss b h hb χ) u (-(h:ℝ)*d/4)
    (Real.exp ((h:ℝ)*n*u^2/(2*M^2))) hu
    (integrable_exp_loss b h hb χ u hu.le) (point_exp_loss b h hb heven hh χ u hu.le)
  have he : Real.exp (u*(-(h:ℝ)*d/4))*Real.exp ((h:ℝ)*n*u^2/(2*M^2)) =
      Real.exp (-(h:ℝ)*M/(2048*(b:ℝ)^3)) := by
    rw [← Real.exp_add]
    congr 1
    have halg : u*(-(h:ℝ)*d/4)+(h:ℝ)*n*u^2/(2*M^2) = -(h:ℝ)*(d^2*M^2/(32*n)) := by
      dsimp [u]; field_simp; ring
    rw [halg, drift_exponent hn hbR hM]
    ring
  rw [he] at H
  simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top H

lemma good_fixed_bad_bound {n b h : ℕ} (hn : 0 < n) (hb : 0 < b) (heven : Even b)
    (hh : 0 < h) (χ : Fin n → Bool) :
    (pointSampleLaw n).real (good (n := n) b h hb ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) ≤
      Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  apply le_trans _ (loss_tail hn hb heven hh χ)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_pointSampleLaw_mem_Ioc n] with P hP
  rintro ⟨hg,hbad⟩
  have hx := actualPotential_le_of_fixedColorBad (pow_pos hb h) (by omega : 0 < 1)
    (pow_pos hb h) χ (fun i => (P i).1) (fun i => (P i).2)
    (fun i => (hP i).1) (fun i => (hP i).2) hbad
  rw [sampleCells_eq_of_grid_eq (Nat.one_mul (b^h)) _ (pow_pos hb h)] at hx
  change pointTerminalPotential b h hb χ P ≤ 2*threshold n h b (b^(h-1):ℕ) at hx
  have hs : (h:ℝ)*massFloor n b (b^(h-1):ℕ)/2 ≤ ∑ j ∈ range h, pointLayerMass b h hb j P := hg
  have hdiv := div_le_div_of_nonneg_right hs (show (0:ℝ) ≤ 4*b*(b^(h-1):ℕ) by positivity)
  change loss b h hb χ P ≤ _
  dsimp only [loss,threshold,drift] at *
  have hneg := neg_le_neg hdiv
  linear_combination hx + hneg

/-- Proposition 3.1. The geometric failure is charged once, not once per coloring. -/
theorem simultaneous_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b) (heven : Even b)
    (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n (threshold n h b (b^(h-1):ℕ))) ≤
      2*(4*Real.sqrt (3/b))^n + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  rw [← pointSampleLaw_eq_unifPts]
  have hs : badSet n (threshold n h b (b^(h-1):ℕ)) ⊆
      (good (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        good b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ := by
    intro P hP
    by_cases hg : P ∈ good b h (by omega)
    · right
      rw [badSet_eq_iUnion_fixedColorBad] at hP
      obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp hP
      exact Set.mem_iUnion.mpr ⟨χ,hg,hχ⟩
    · exact Or.inl hg
  calc
    _ ≤ (pointSampleLaw n).real ((good (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        good b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ (pointSampleLaw n).real (good (n := n) b h (by omega))ᶜ +
        (pointSampleLaw n).real (⋃ χ : Fin n → Bool, good b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) := measureReal_union_le _ _
    _ ≤ 2*(4*Real.sqrt (3/b))^n +
        ∑ χ : Fin n → Bool, (pointSampleLaw n).real (good b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) :=
      add_le_add (bad_geometry_bound hn hb hh hMn) (measureReal_iUnion_fintype_le _)
    _ ≤ 2*(4*Real.sqrt (3/b))^n +
        ∑ _χ : Fin n → Bool, Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) :=
      add_le_add_right (sum_le_sum (fun χ _ => good_fixed_bad_bound hn (by omega) heven hh χ)) _
    _ = _ := by simp

/-- The threshold is exactly the one displayed in Proposition 3.1. -/
lemma threshold_eq {n : ℕ} (hn : 0 < n) (h : ℕ) {b M : ℝ} (hb : 0 < b) (hM : 0 < M) :
    threshold n h b M = (h:ℝ)*Real.sqrt (n/M)/(64*b^(3/2:ℝ)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hr : 0 < Real.sqrt ((n:ℝ)/M) := Real.sqrt_pos.mpr (by positivity)
  have hbroot : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hs := Real.sq_sqrt (show 0 ≤ (n:ℝ)/M by positivity)
  have hs' := (eq_div_iff hM.ne').mp hs
  rw [Parameters.rpow_three_halves b hb.le]
  unfold threshold drift massFloor
  rw [show b*n/M = b*((n:ℝ)/M) by ring, Real.sqrt_mul hb.le]
  field_simp
  nlinarith

lemma geometry_factor_eq {n : ℕ} {b : ℝ} (hb : 0 < b) :
    (4*Real.sqrt (3/b))^n = (48/b)^((n:ℝ)/2) := by
  have he : (4:ℝ)*Real.sqrt (3/b) = Real.sqrt (48/b) := by
    rw [show (48:ℝ)/b = 16*(3/b) by ring, Real.sqrt_mul (by norm_num)]
    norm_num
  rw [he, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- Exact numerical form of Proposition 3.1, with the manuscript threshold and constants. -/
theorem proposition_3_1 {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b) (heven : Even b)
    (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n ((h:ℝ)*Real.sqrt ((n:ℝ)/(b^(h-1):ℕ))/(64*(b:ℝ)^(3/2:ℝ)))) ≤
      2*(48/(b:ℝ))^((n:ℝ)/2) + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  have hbR : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have H := simultaneous_bound hn hb heven hh hMn
  rw [threshold_eq hn h hbR (by positivity),geometry_factor_eq hbR] at H
  exact H

end
end Oscillation.Direct
