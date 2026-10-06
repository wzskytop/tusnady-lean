import Oscillation.Accumulation
import Oscillation.RealGrid
import Oscillation.Influence
import Oscillation.StageBasics
import Oscillation.DriftAssembly

/-! The actual horizontal sampling process and its compensated exponential bound. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset Riesz Riesz.PointSets
open scoped ENNReal

lemma actualPotential_finiteConditionalLaw {n K V m b : ℕ} (hK : 0 < K)
    (hm : 0 < m) (hb : 0 < b) (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1)
    (Y : Fin n → ℕ) :
    HasFiniteConditionalLaw (μ := Measure.pi (fun _ : Fin n ↦ μI))
      (sampleGridSigma n K)
      (actualPotential (b*K) V (b*m) (Nat.mul_pos hb hK) (Nat.mul_pos hb hm) χ Y)
      (fun (U : Fin n → ℝ) (r : Fin n → Fin b) ↦ gridPotential (b*K) V (b*m) (Nat.mul_pos hb hm) χ
        (refinedPositions (sampleCells n K hK U) r) Y) := by
  intro φ hφ
  exact condExp_actualPotential_refined hK hm hb χ hχ Y φ hφ

lemma actualPotential_coordinateOscillation {n K V m b : ℕ} (hK : 0 < K)
    (hV : 0 < V) (hm : 0 < m) (hb : 0 < b) (χ : Fin n → ℝ)
    (hχ : ∀ i, |χ i| ≤ 1) (Y : Fin n → ℕ) (U : Fin n → ℝ) :
    CoordinateOscillation
      (fun r : Fin n → Fin b ↦ gridPotential (b*K) V (b*m) (Nat.mul_pos hb hm) χ
        (refinedPositions (sampleCells n K hK U) r) Y) (1 / (K * V : ℕ)) := by
  intro r i a
  rw [Nat.mul_comm b K]
  exact gridPotential_refined_influence hK hV (Nat.mul_pos hb hm) hb χ hχ
    (sampleCells n K hK U) Y r i a

lemma stage_dimension_identity {b h j : ℕ} (hj : j < h) :
    b ^ j * b ^ (h - j - 1) = b ^ (h - 1) := by
  rw [← pow_add]
  congr 1
  omega

lemma stage_cost_identity (n h : ℕ) (hh : 0 < h) (M : ℝ) (hM : 0 < M) :
    (h : ℝ) * n * (2 * M / Real.sqrt h) ^ 2 * (1 / M) ^ 2 / 2 = 2 * n := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hs := Real.sq_sqrt hhR.le
  have hroot : 0 < Real.sqrt (h : ℝ) := Real.sqrt_pos.2 hhR
  field_simp
  nlinarith

lemma stage_drift_factor_identity (b M H S : ℝ) (hb : 0 < b) (hM : 0 < M)
    (hH : 0 < H) :
    (2 * M / H) * (S / (4 * b * M)) = S / (2 * b * H) := by
  field_simp
  ring

/-- The next potential as a function of the actual fresh digit vector. -/
def stageContinuation {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (Y : Fin n → ℕ) (j : ℕ) (U : Fin n → ℝ) (r : Fin n → Fin b) : ℝ :=
  gridPotential (b * b ^ j) (b ^ (h-j-1)) (b * b ^ j)
    (Nat.mul_pos hb (pow_pos hb _)) χ
    (refinedPositions (sampleCells n (b ^ j) (pow_pos hb _) U) r) Y

lemma stagePotential_next {n b h j : ℕ} (hb : 0 < b) (hj : j < h)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) :
    stagePotential b h hb χ Y (j+1) =
      actualPotential (b * b ^ j) (b ^ (h-j-1)) (b * b ^ j)
        (Nat.mul_pos hb (pow_pos hb _)) (Nat.mul_pos hb (pow_pos hb _)) χ Y := by
  funext U
  have he : h-(j+1) = h-j-1 := by omega
  simp only [stagePotential, Nat.min_eq_left (by omega : j+1 ≤ h), he, pow_succ']

lemma stagePotential_before {n b h j : ℕ} (hb : 0 < b) (hj : j < h)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) (U : Fin n → ℝ) :
    stagePotential b h hb χ Y j U =
      gridPotential (b ^ j) (b ^ (h-j-1) * b) (b ^ j) (pow_pos hb _) χ
        (sampleCells n (b ^ j) (pow_pos hb _) U) Y := by
  have he : h-j = (h-j-1)+1 := by omega
  have hv : b ^ (h-j) = b ^ (h-j-1) * b := by
    calc
      _ = b ^ ((h-j-1)+1) := congrArg (fun k ↦ b^k) he
      _ = _ := pow_succ _ _
  simp only [stagePotential, Nat.min_eq_left hj.le, actualPotential, hv]
  have hp := congrArg (fun k : ℕ ↦ sampleCells n (b^k) (pow_pos hb k) U)
    (Nat.min_eq_left hj.le)
  exact congrArg (fun p : Fin n → ℕ ↦ gridPotential (b^j) (b^(h-j-1)*b)
    (b^j) (pow_pos hb j) χ p Y) hp

lemma stage_finiteConditionalLaw {n b h j : ℕ} (hb : 0 < b) (hj : j < h)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1) (Y : Fin n → ℕ) :
    HasFiniteConditionalLaw (μ := Measure.pi (fun _ : Fin n ↦ μI))
      (stageFiltration n b h hb j) (stagePotential b h hb χ Y (j+1))
      (stageContinuation b h hb χ Y j) := by
  rw [stageFiltration_apply, Nat.min_eq_left hj.le, stagePotential_next hb hj]
  exact actualPotential_finiteConditionalLaw (pow_pos hb _) (pow_pos hb _) hb χ hχ Y

lemma stage_coordinateOscillation {n b h j : ℕ} (hb : 0 < b) (hj : j < h)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1) (Y : Fin n → ℕ) (U : Fin n → ℝ) :
    CoordinateOscillation (stageContinuation b h hb χ Y j U) (1 / (b ^ (h-1) : ℕ)) := by
  have hi := actualPotential_coordinateOscillation (K := b^j) (V := b^(h-j-1))
    (m := b^j) (pow_pos hb _) (pow_pos hb _) (pow_pos hb _) hb χ hχ Y U
  rw [stage_rectangles b h j hj] at hi
  exact hi

lemma stage_finite_drift {n b h j : ℕ} (hb : 0 < b) (heven : Even b) (hj : j < h)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (Y : Fin n → ℕ) (U : Fin n → ℝ) :
    stageMass b h hb Y j U / (4 * (b : ℝ) * (b ^ (h-1) : ℕ)) ≤
      finAvg (stageContinuation b h hb χ Y j U) - stagePotential b h hb χ Y j U := by
  have hg := gridPotential_drift_even (K := b^j) (V := b^(h-j-1))
    (pow_pos hb _) (pow_pos hb _) hb heven (pow_pos hb j) χ hχ
    (sampleCells n (b^j) (pow_pos hb _) U) Y
  rw [stage_rectangles b h j hj] at hg
  rw [stageMass, ite_eq_left hj, stagePotential_before hb hj]
  change _ ≤ finAvg (fun r : Fin n → Fin b ↦
    gridPotential (b*b^j) (b^(h-j-1)) (b*b^j) (Nat.mul_pos hb (pow_pos hb j)) χ
      (refinedPositions (sampleCells n (b^j) (pow_pos hb j) U) r) Y) - _
  simpa only [Nat.mul_comm (b^j) b] using hg

/-- The manuscript's compensated exponential estimate for actual iid
horizontal samples, for each fixed vector of vertical fine-cell labels. -/
theorem integral_exp_stage_compensated (n b h : ℕ) (hb : 0 < b) (heven : Even b)
    (hh : 0 < h) (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (Y : Fin n → ℕ) :
    (∫ U, Real.exp (-2 * (b ^ (h-1) : ℕ) * stagePotential b h hb χ Y h U / Real.sqrt h +
      (∑ j ∈ range h, stageMass b h hb Y j U) / (2 * (b : ℝ) * Real.sqrt h) - 2 * n)
      ∂Measure.pi (fun _ : Fin n ↦ μI)) ≤ 1 := by
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  let M : ℝ := (b ^ (h-1) : ℕ)
  let D : ℝ := 4 * b * M
  let u : ℝ := 2 * M / Real.sqrt h
  let Z := stagePotential b h hb χ Y
  let S : ℕ → (Fin n → ℝ) → ℝ := fun j U ↦ stageMass b h hb Y j U / D
  let F := stageFiltration n b h hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hroot : 0 < Real.sqrt (h : ℝ) := Real.sqrt_pos.2 hhR
  have hu : 0 ≤ u := by dsimp [u]; positivity
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
  have hc := integral_exp_compensated_le (μ := Measure.pi (fun _ : Fin n ↦ μI))
    F n h Z S (stageContinuation b h hb χ Y) hZ hS
    (max (2 * (n : ℝ)) (M * Real.sqrt n / D)) hbound
    (stagePotential_zero b h hb χ Y) (by positivity : 0 ≤ 1 / M) u hu
    (fun j hj ↦ stage_finiteConditionalLaw hb hj χ hχle Y)
    (fun j hj ↦ Filter.Eventually.of_forall (stage_coordinateOscillation hb hj χ hχle Y))
    (fun j hj ↦ Filter.Eventually.of_forall (stage_finite_drift hb heven hj χ hχ Y))
  have hcost : (h : ℝ) * n * u ^ 2 * (1 / M) ^ 2 / 2 = 2 * n :=
    stage_cost_identity n h hh M hM
  have hsum (U : Fin n → ℝ) : u * ∑ j ∈ range h, S j U =
      (∑ j ∈ range h, stageMass b h hb Y j U) / (2 * (b : ℝ) * Real.sqrt h) := by
    simp only [S, ← sum_div]
    exact stage_drift_factor_identity b M (Real.sqrt h) _ hbR hM hroot
  rw [hcost] at hc
  simp_rw [hsum] at hc
  convert hc using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun U ↦ by
    dsimp only [u, Z, M]
    congr 1
    ring)

end
end Oscillation
