import Oscillation.FixedScale
import Oscillation.DirectCounting

namespace Oscillation.Direct
noncomputable section
open MeasureTheory ProbabilityTheory Finset Riesz Riesz.PointSets
open scoped ENNReal Classical

/-- Arbitrary-parameter accumulation; this is the bounded-difference part of the direct proof. -/
theorem stage_exp_gain (n b h : ℕ) (hb : 0 < b) (heven : Even b)
    (hh : 0 < h) (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (Y : Fin n → ℕ)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫ U, Real.exp (-u * stagePotential b h hb χ Y h U +
      u * (∑ j ∈ range h, stageMass b h hb Y j U) / (4 * b * (b^(h-1):ℕ)))
      ∂Measure.pi (fun _ : Fin n => μI)) ≤
      Real.exp ((h:ℝ)*n*u^2/(2*(b^(h-1):ℕ)^2)) := by
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  let M : ℝ := (b ^ (h-1) : ℕ)
  let D : ℝ := 4 * b * M
  let Z := stagePotential b h hb χ Y
  let S : ℕ → (Fin n → ℝ) → ℝ := fun j U ↦ stageMass b h hb Y j U / D
  let F := stageFiltration n b h hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hroot : 0 < Real.sqrt (h : ℝ) := Real.sqrt_pos.2 hhR
  have hχle : ∀ i, |χ i| ≤ 1 := fun i ↦ (hχ i).le
  have hZ : StronglyAdapted F Z := stagePotential_adapted b h hb χ Y
  have hS : StronglyAdapted F S := fun j ↦ ((stageMass_adapted b h hb Y j).measurable.div_const D).stronglyMeasurable
  have hbound : ∀ j U, |Z j U| ≤ max (2 * (n : ℝ)) (M * Real.sqrt n / D) ∧
      |S j U| ≤ max (2 * (n : ℝ)) (M * Real.sqrt n / D) := by
    intro j U
    constructor
    · exact (stagePotential_abs_le b h hb χ hχle Y j U).trans (le_max_left _ _)
    · calc
        |S j U| = |stageMass b h hb Y j U| / D := by dsimp [S]; rw [abs_div, abs_of_pos hD]
        _ ≤ M * Real.sqrt n / D := div_le_div_of_nonneg_right
          (stageMass_abs_le b h hb Y j U) hD.le
        _ ≤ _ := le_max_right _ _
  have hc := integral_exp_accumulated_le (μ := Measure.pi (fun _ : Fin n ↦ μI))
    F n h Z S (stageContinuation b h hb χ Y) hZ hS
    (max (2 * (n : ℝ)) (M * Real.sqrt n / D)) hbound
    (stagePotential_zero b h hb χ Y) (by positivity : 0 ≤ 1 / M) u hu
    (fun j hj ↦ stage_finiteConditionalLaw hb hj χ hχle Y)
    (fun j hj ↦ Filter.Eventually.of_forall (stage_coordinateOscillation hb hj χ hχle Y))
    (fun j hj ↦ Filter.Eventually.of_forall (stage_finite_drift hb heven hj χ hχ Y))
  have he (U : Fin n → ℝ) : u * (∑ j ∈ range h, S j U) =
      u * (∑ j ∈ range h, stageMass b h hb Y j U) / D := by
    simp only [S, ← sum_div]; ring
  simp_rw [he] at hc
  convert hc using 1 <;> dsimp [Z,D,M] <;> congr 1 <;> ring

/-- Terminal potential minus the sum of its proved lower bounds on conditional gains. -/
def loss {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool)
    (P : Fin n → ℝ × ℝ) : ℝ :=
  pointTerminalPotential b h hb χ P -
    (∑ j ∈ range h, pointLayerMass b h hb j P)/(4*b*(b^(h-1):ℕ))

lemma measurable_loss {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool) :
    Measurable (loss b h hb χ) :=
  (measurable_pointTerminalPotential b h hb χ).sub
    ((Finset.measurable_sum _ (fun j _ => measurable_pointLayerMass b h hb j)).div_const _)

lemma integrable_exp_loss {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → Bool)
    (u : ℝ) (hu : 0 ≤ u) :
    Integrable (fun P => Real.exp (-u * loss b h hb χ P)) (pointSampleLaw n) := by
  apply integrable_exp_of_bounded ((measurable_loss b h hb χ).const_mul (-u))
    (u*((h:ℝ)*(b^(h-1):ℕ)*Real.sqrt n)/(4*b*(b^(h-1):ℕ)))
  intro P
  have hsum : (∑ j ∈ range h, pointLayerMass b h hb j P) ≤
      (h:ℝ)*(b^(h-1):ℕ)*Real.sqrt n := by
    calc
      _ ≤ ∑ _j ∈ range h, (b^(h-1):ℕ)*Real.sqrt n :=
        sum_le_sum (fun j hj => pointLayerMass_le b h hb (mem_range.mp hj) P)
      _ = _ := by simp; ring
  have hx := pointTerminalPotential_nonneg b h hb χ P
  have hd : 0 ≤ (4:ℝ)*b*(b^(h-1):ℕ) := by positivity
  have hs := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum hd) hu
  dsimp only [loss]
  convert (sub_le_self _ (mul_nonneg hu hx)).trans hs using 1 <;> ring

/-- Both coordinates are integrated under the actual iid law. -/
theorem point_exp_loss {n : ℕ} (b h : ℕ) (hb : 0 < b) (heven : Even b) (hh : 0 < h)
    (χ : Fin n → Bool) (u : ℝ) (hu : 0 ≤ u) :
    (∫ P, Real.exp (-u * loss b h hb χ P) ∂pointSampleLaw n) ≤
      Real.exp ((h:ℝ)*n*u^2/(2*(b^(h-1):ℕ)^2)) := by
  have hi := integrable_exp_loss b h hb χ u hu
  rw [integral_point_eq_vertical_horizontal _ hi]
  have ho := ((integrable_pairCoordinates_iff _).mpr hi).integral_prod_right
  calc
    _ ≤ ∫ _W : Fin n → ℝ, Real.exp ((h:ℝ)*n*u^2/(2*(b^(h-1):ℕ)^2))
        ∂coordinateSampleLaw n := by
      apply integral_mono ho (integrable_const _)
      intro W
      let Y := sampleCells n (b^h) (pow_pos hb h) W
      have hχ : ∀ i, |(PointSets.boolSign (χ i):ℝ)| = 1 := by
        intro i; cases χ i <;> simp [PointSets.boolSign]
      have H := stage_exp_gain n b h hb heven hh _ hχ Y u hu
      have hsum (U : Fin n → ℝ) : (∑ j ∈ range h, stageMass b h hb Y j U) =
          ∑ j ∈ range h, pointLayerMass b h hb j (fun i => (U i,W i)) := by
        apply sum_congr rfl
        intro j hj
        simp only [stageMass, ite_eq_left (mem_range.mp hj)]
        rfl
      simp_rw [stagePotential_terminal] at H
      simp_rw [hsum] at H
      convert H using 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun U => by dsimp [loss,pointTerminalPotential]; congr 1; ring)
    _ = _ := by simp

end
end Oscillation.Direct
