import Oscillation.FixedScalePrelude
import Oscillation.Accumulation
import Oscillation.FinalReduction
import Oscillation.CoordinateProduct
import Oscillation.Stages

namespace Oscillation
open scoped BigOperators ENNReal
open MeasureTheory Riesz Riesz.PointSets Riesz.Occupancy
noncomputable section

/-- The last finite oscillation potential on the actual sampled point set. -/
def pointTerminalPotential {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool)
    (P : Fin n → ℝ × ℝ) : ℝ :=
  actualPotential (b^h) 1 (b^h) (pow_pos hb h) (pow_pos hb h)
    (fun i => (PointSets.boolSign (χ i) : ℝ))
    (sampleCells n (b^h) (pow_pos hb h) (fun i => (P i).2)) (fun i => (P i).1)

/-- Raw interior square-root count at a layer, all read from the same finest vertical grid. -/
def pointLayerMass {n : ℕ} (b h : ℕ) (hb : 0 < b) (j : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  interiorMass (b^j) (b^(h-j-1)) b (b^j)
    (sampleCells n (b^j) (pow_pos hb j) (fun i => (P i).1))
    (sampleCells n (b^h) (pow_pos hb h) (fun i => (P i).2))

lemma layer_comparison_size {b h j : ℕ} (hj : j < h) :
    b^j * b^(h-j-1) = b^(h-1) := by
  rw [← pow_add]
  congr 1
  omega

lemma layer_fine_size {b h j : ℕ} (hj : j < h) :
    b^(h-j-1) * (b*b^j) = b^h := by
  rw [← pow_succ', ← pow_add]
  congr 1
  omega

lemma measurable_pointTerminalPotential {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool) :
    Measurable (pointTerminalPotential b h hb χ) :=
  measurable_joint_grid_function (pow_pos hb h) (pow_pos hb h)
    (fun p Y => gridPotential (b^h) 1 (b^h) (pow_pos hb h)
      (fun i => (PointSets.boolSign (χ i) : ℝ)) p Y)

lemma pointTerminalPotential_nonneg {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool)
    (P : Fin n → ℝ × ℝ) : 0 ≤ pointTerminalPotential b h hb χ P :=
  gridPotential_nonneg _ _ _ _ _ _ _

lemma pointTerminalPotential_le {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool)
    (P : Fin n → ℝ × ℝ) : pointTerminalPotential b h hb χ P ≤ 2*n := by
  apply gridPotential_le_two_n
  intro i
  cases χ i <;> simp [PointSets.boolSign]

lemma measurable_pointLayerMass {n : ℕ} (b h : ℕ) (hb : 0 < b) (j : ℕ) :
    Measurable (pointLayerMass (n := n) b h hb j) :=
  measurable_joint_grid_function (pow_pos hb j) (pow_pos hb h)
    (interiorMass (b^j) (b^(h-j-1)) b (b^j))

lemma pointLayerMass_nonneg {n : ℕ} (b h : ℕ) (hb : 0 < b) (j : ℕ) (P : Fin n → ℝ × ℝ) :
    0 ≤ pointLayerMass b h hb j P := interiorMass_nonneg' _ _ _ _ _ _

lemma pointLayerMass_le {n : ℕ} (b h : ℕ) (hb : 0 < b) {j : ℕ} (hj : j < h)
    (P : Fin n → ℝ × ℝ) : pointLayerMass b h hb j P ≤ (b^(h-1):ℕ) * Real.sqrt n := by
  have H := interiorMass_le_count_root (b^j) (b^(h-j-1)) b (b^j)
    (sampleCells n (b^j) (pow_pos hb j) (fun i => (P i).1))
    (sampleCells n (b^h) (pow_pos hb h) (fun i => (P i).2))
  simpa only [pointLayerMass, layer_comparison_size hj] using H

lemma sampleCells_eq_of_grid_eq {n K N : ℕ} (h : K = N) (hK : 0 < K) (hN : 0 < N) :
    sampleCells n K hK = sampleCells n N hN := by
  subst N
  rfl

lemma pointLayerMass_laplace {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b) (_hh : 0 < h)
    {j : ℕ} (hj : j < h)
    (hd : (n:ℝ) ≤ h * (b^(h-1):ℕ) / (4*(b:ℝ)^3)) :
    (∫ P : Fin n → ℝ × ℝ,
      Real.exp (-Real.sqrt (h:ℝ) * pointLayerMass b h (by omega) j P / (2*b))
      ∂Measure.pi (fun _ => μI.prod μI)) ≤
      (2:ℝ)^(n+b^(h-1)) * (4/(b:ℝ))^n := by
  have hb0 : 0 < b := by omega
  have hcoeff := density_laplace_coefficient (by exact_mod_cast hb0 : (0:ℝ) < b)
    (pow_pos hb0 (h-1)) hd
  have H := interiorMass_iid_laplace_larger_coefficient (b^j) (b^(h-j-1)) b (b^j)
    (pow_pos hb0 j) (pow_pos hb0 _) hb (pow_pos hb0 j) hn
    (a := Real.sqrt (h:ℝ)/(2*b)) (by simpa only [layer_comparison_size hj] using hcoeff)
  rw [layer_comparison_size hj] at H
  have heq : (fun P : Fin n → ℝ × ℝ =>
      Real.exp (-Real.sqrt (h:ℝ) * pointLayerMass b h hb0 j P / (2*b))) =
      (fun P => Real.exp (-(Real.sqrt (h:ℝ)/(2*b)) *
        interiorMass (b^j) (b^(h-j-1)) b (b^j)
          (sampleCells n (b^j) (pow_pos hb0 j) (fun i => (P i).1))
          (sampleCells n (b^(h-j-1)*(b*b^j)) (by positivity) (fun i => (P i).2)))) := by
    funext P
    congr 1
    rw [sampleCells_eq_of_grid_eq (layer_fine_size hj) _ (pow_pos hb0 h)]
    dsimp [pointLayerMass]
    ring
  rw [heq]
  exact H


lemma pointTerminal_laplace_of_compensated {n b h : ℕ} (hb : 4 ≤ b) (hh : 0 < h)
    (hn : 0 < n) (hMn : b^(h-1) ≤ n)
    (hd : (n:ℝ) ≤ h * (b^(h-1):ℕ) / (4*(b:ℝ)^3)) (χ : Fin n → Bool)
    (hcomp : (∫ P, Real.exp (-2*(b^(h-1):ℕ)*pointTerminalPotential b h (by omega) χ P / Real.sqrt h +
      (∑ j ∈ Finset.range h, pointLayerMass b h (by omega) j P)/(2*b*Real.sqrt h)-2*n)
      ∂pointSampleLaw n) ≤ 1) :
    (∫ P, Real.exp (-((b^(h-1):ℕ)/Real.sqrt (h:ℝ))*pointTerminalPotential b h (by omega) χ P)
      ∂pointSampleLaw n) ≤ Real.exp ((n:ℝ)*(1+2*Real.log 2-Real.log b/2)) := by
  have hb0 : 0 < b := by omega
  have hbR : (0:ℝ) < b := by exact_mod_cast hb0
  have hMR : (0:ℝ) < (b^(h-1):ℕ) := by exact_mod_cast pow_pos hb0 (h-1)
  let K : ℝ := 2*n+(b^(h-1):ℕ)*Real.sqrt n
  have hXb (P : Fin n → ℝ × ℝ) : |pointTerminalPotential b h hb0 χ P| ≤ K := by
    rw [abs_of_nonneg (pointTerminalPotential_nonneg b h hb0 χ P)]
    exact (pointTerminalPotential_le b h hb0 χ P).trans (le_add_of_nonneg_right (by positivity))
  have hSb (j : ℕ) (hj : j < h) (P : Fin n → ℝ × ℝ) : |pointLayerMass b h hb0 j P| ≤ K := by
    rw [abs_of_nonneg (pointLayerMass_nonneg b h hb0 j P)]
    exact (pointLayerMass_le b h hb0 hj P).trans (le_add_of_nonneg_left (by positivity))
  have H := integral_exp_oscillation_laplace_of_marginal_bound (μ := pointSampleLaw n)
    n h hh b (b^(h-1):ℕ) hbR hMR (pointTerminalPotential b h hb0 χ) (pointLayerMass b h hb0)
    (measurable_pointTerminalPotential b h hb0 χ)
    (fun j _ => measurable_pointLayerMass b h hb0 j) K
    ((2:ℝ)^(n+b^(h-1))*(4/(b:ℝ))^n) hXb hSb hcomp
    (fun j hj => pointLayerMass_laplace hn hb hh hj hd)
  have H' := H.trans (laplace_histogram_rhs hbR hMn)
  convert H' using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun P => by dsimp only; congr 1; ring)

lemma integrable_pointTerminal_exp {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool) (t : ℝ) :
    Integrable (fun P => Real.exp (-t*pointTerminalPotential b h hb χ P)) (pointSampleLaw n) :=
  integrable_joint_grid_function (pow_pos hb h) (pow_pos hb h)
    (fun p Y => Real.exp (-t*gridPotential (b^h) 1 (b^h) (pow_pos hb h)
      (fun i => (PointSets.boolSign (χ i) : ℝ)) p Y))

lemma fixedColorBad_le_of_pointTerminal_laplace {n b h : ℕ} (hb : 0 < b) (hh : 0 < h)
    (χ : Fin n → Bool)
    (hLap : (∫ P, Real.exp (-((b^(h-1):ℕ)/Real.sqrt (h:ℝ))*pointTerminalPotential b h hb χ P)
      ∂pointSampleLaw n) ≤ Real.exp ((n:ℝ)*(1+2*Real.log 2-Real.log b/2))) :
    unifPts n (fixedColorBad n ((n:ℝ)*Real.sqrt h/(8*(b^(h-1):ℕ))) χ) ≤
      ENNReal.ofReal (Real.exp (-(Real.log b/2-2*Real.log 2-5/4)*n)) := by
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hMR : (0:ℝ) < (b^(h-1):ℕ) := by exact_mod_cast pow_pos hb (h-1)
  have hsR : 0 < Real.sqrt (h:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hh)
  let B : ℝ := (n:ℝ)*Real.sqrt h/(8*(b^(h-1):ℕ))
  have hsmall := small_event_of_laplace (pointSampleLaw n) (pointTerminalPotential b h hb χ)
    ((b^(h-1):ℕ)/Real.sqrt (h:ℝ)) (2*B)
    (Real.exp ((n:ℝ)*(1+2*Real.log 2-Real.log b/2))) (by positivity)
    (integrable_pointTerminal_exp b h hb χ _) hLap
  rw [fixed_scale_exponent hbR hMR hh] at hsmall
  rw [← pointSampleLaw_eq_unifPts]
  apply le_trans _ hsmall
  apply measure_mono_ae
  filter_upwards [ae_pointSampleLaw_mem_Ioc n] with P hP
  intro hbad
  have HX := actualPotential_le_of_fixedColorBad (pow_pos hb h) (by omega : 0 < 1)
    (pow_pos hb h) χ (fun i => (P i).1) (fun i => (P i).2)
    (fun i => (hP i).1) (fun i => (hP i).2) hbad
  rw [sampleCells_eq_of_grid_eq (Nat.one_mul (b^h)) _ (pow_pos hb h)] at HX
  exact HX


def pointCompensated {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool)
    (P : Fin n → ℝ × ℝ) : ℝ :=
  Real.exp (-2*(b^(h-1):ℕ)*pointTerminalPotential b h hb χ P / Real.sqrt h +
    (∑ j ∈ Finset.range h, pointLayerMass b h hb j P)/(2*b*Real.sqrt h)-2*n)

lemma integrable_pointCompensated {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool) :
    Integrable (pointCompensated b h hb χ) (pointSampleLaw n) := by
  have hm : Measurable (fun P : Fin n → ℝ × ℝ =>
      -2*(b^(h-1):ℕ)*pointTerminalPotential b h hb χ P / Real.sqrt h +
      (∑ j ∈ Finset.range h, pointLayerMass b h hb j P)/(2*b*Real.sqrt h)-2*n) :=
    ((((measurable_pointTerminalPotential b h hb χ).const_mul (-2*(b^(h-1):ℕ))).div_const _).add
      ((Finset.measurable_sum _ (fun j _ => measurable_pointLayerMass b h hb j)).div_const _)).sub_const _
  apply integrable_exp_of_bounded hm ((h:ℝ)*(b^(h-1):ℕ)*Real.sqrt n/(2*b*Real.sqrt h))
  intro P
  have hsum : (∑ j ∈ Finset.range h, pointLayerMass b h hb j P) ≤
      (h:ℝ)*(b^(h-1):ℕ)*Real.sqrt n := by
    calc
      _ ≤ ∑ _j ∈ Finset.range h, (b^(h-1):ℕ)*Real.sqrt (n:ℝ) :=
        Finset.sum_le_sum fun j hj => pointLayerMass_le b h hb (Finset.mem_range.mp hj) P
      _ = _ := by simp; ring
  have hnegative : -2*(b^(h-1):ℕ)*pointTerminalPotential b h hb χ P / Real.sqrt h ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (Real.sqrt_nonneg _)
    have hc : -2*(b^(h-1):ℕ) ≤ (0:ℝ) :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    exact mul_nonpos_of_nonpos_of_nonneg hc (pointTerminalPotential_nonneg b h hb χ P)
  have hd := div_le_div_of_nonneg_right hsum (by positivity : (0:ℝ) ≤ 2*b*Real.sqrt h)
  have hnR : (0:ℝ) ≤ n := by positivity
  linarith

/-- Integrating the horizontal proof over the initially fixed vertical coordinates. -/
lemma pointCompensated_integral_of_sections {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool)
    (hsection : ∀ Y : Fin n → ℕ,
      (∫ U : Fin n → ℝ, Real.exp
        (-2*(b^(h-1):ℕ)*actualPotential (b^h) 1 (b^h) (pow_pos hb h) (pow_pos hb h)
          (fun i => (PointSets.boolSign (χ i) : ℝ)) Y U / Real.sqrt h +
        (∑ j ∈ Finset.range h, interiorMass (b^j) (b^(h-j-1)) b (b^j)
          (sampleCells n (b^j) (pow_pos hb j) U) Y)/(2*b*Real.sqrt h)-2*n)
        ∂coordinateSampleLaw n) ≤ 1) :
    (∫ P, pointCompensated b h hb χ P ∂pointSampleLaw n) ≤ 1 := by
  have hi := integrable_pointCompensated b h hb χ
  rw [integral_point_eq_vertical_horizontal _ hi]
  have ho := ((integrable_pairCoordinates_iff _).mpr hi).integral_prod_right
  calc
    _ ≤ ∫ _W : Fin n → ℝ, (1:ℝ) ∂coordinateSampleLaw n := by
      apply integral_mono ho (integrable_const 1)
      intro W
      exact hsection (sampleCells n (b^h) (pow_pos hb h) W)
    _ = 1 := by simp


/-- Both coordinate directions are sampled under the genuine point-set law. -/
theorem pointCompensated_integral {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (heven : Even b) (hh : 0 < h) (χ : Fin n → Bool) :
    (∫ P, pointCompensated b h hb χ P ∂pointSampleLaw n) ≤ 1 := by
  apply pointCompensated_integral_of_sections b h hb χ
  intro Y
  have hχ : ∀ i, |(PointSets.boolSign (χ i) : ℝ)| = 1 := by
    intro i
    cases χ i <;> simp [PointSets.boolSign]
  have H := integral_exp_stage_compensated n b h hb heven hh
    (fun i => (PointSets.boolSign (χ i) : ℝ)) hχ Y
  have hsum (U : Fin n → ℝ) : (∑ j ∈ Finset.range h, stageMass b h hb Y j U) =
      ∑ j ∈ Finset.range h, interiorMass (b^j) (b^(h-j-1)) b (b^j)
        (sampleCells n (b^j) (pow_pos hb j) U) Y := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [stageMass, ite_eq_left (Finset.mem_range.mp hj)]
  simpa only [stagePotential_terminal, hsum] using H

/-- The complete fixed-scale probability estimate for every fixed coloring. -/
theorem fixed_scale_estimate : FixedScaleEstimate := by
  intro L hL n k hn hMn hd χ
  let b : ℕ := 2^L
  have hb : 4 ≤ b := by
    calc (4:ℕ) = 2^2 := by norm_num
         _ ≤ 2^L := Nat.pow_le_pow_right (by omega) (by omega)
  have hb0 : 0 < b := by omega
  have heven : Even b := Even.pow_of_ne_zero (by norm_num : Even (2:ℕ)) (by omega)
  have hMn' : b^k ≤ n := by
    exact_mod_cast hMn
  have hd' : (n:ℝ) ≤ (k+1:ℕ)*(b^((k+1)-1):ℕ)/(4*(b:ℝ)^3) := by
    simpa only [Nat.add_sub_cancel, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, b] using hd
  have H := pointTerminal_laplace_of_compensated hb (by omega : 0 < k+1) (by omega : 0 < n)
    (by simpa only [Nat.add_sub_cancel] using hMn') hd' χ
    (pointCompensated_integral b (k+1) hb0 heven (by omega) χ)
  have hfixed := fixedColorBad_le_of_pointTerminal_laplace hb0 (by omega : 0 < k+1) χ H
  simpa only [scaleThreshold, scaleRate, Nat.add_sub_cancel, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, b] using hfixed

end
end Oscillation
