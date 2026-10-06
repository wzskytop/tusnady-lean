import Oscillation.RealGrid
import Oscillation.GeometryBounds
import Mathlib.Probability.Process.Adapted

/-! Actual truncated base-b stages on iid horizontal real coordinates. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Riesz Riesz.PointSets

def stagePotential {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (Y : Fin n → ℕ) (j : ℕ) (U : Fin n → ℝ) : ℝ :=
  actualPotential (b ^ min j h) (b ^ (h - min j h)) (b ^ min j h)
    (pow_pos hb _) (pow_pos hb _) χ Y U

def stageMass {n : ℕ} (b h : ℕ) (hb : 0 < b) (Y : Fin n → ℕ)
    (j : ℕ) (U : Fin n → ℝ) : ℝ :=
  if j < h then interiorMass (b ^ j) (b ^ (h-j-1)) b (b ^ j)
    (sampleCells n (b ^ j) (pow_pos hb _) U) Y else 0

lemma sampleGridSigma_mono_pow (n b : ℕ) (hb : 0 < b) :
    Monotone (fun j ↦ sampleGridSigma n (b ^ j)) := by
  intro i j hij
  change sampleGridSigma n (b^i) ≤ sampleGridSigma n (b^j)
  have he : b ^ j = b ^ i * b ^ (j-i) := by rw [← pow_add, Nat.add_sub_of_le hij]
  rw [he]
  exact sampleGridSigma_le_mul n (b^i) (b^(j-i)) (pow_pos hb _)

def stageFiltration (n b h : ℕ) (hb : 0 < b) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → ℝ)) where
  seq j := sampleGridSigma n (b ^ min j h)
  mono' := fun _i _j hij ↦ sampleGridSigma_mono_pow n b hb (min_le_min_right h hij)
  le' j := (measurable_sampleGridIndex n (b ^ min j h)).comap_le

@[simp] lemma stageFiltration_apply (n b h : ℕ) (hb : 0 < b) (j : ℕ) :
    stageFiltration n b h hb j = sampleGridSigma n (b ^ min j h) := rfl

lemma stagePotential_adapted {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) :
    StronglyAdapted (stageFiltration n b h hb) (stagePotential b h hb χ Y) := by
  intro j
  apply Measurable.stronglyMeasurable
  exact (measurable_of_countable (fun p : Fin n → ℕ ↦
    gridPotential (b ^ min j h) (b ^ (h-min j h)) (b ^ min j h)
      (pow_pos hb _) χ p Y)).comp
    (measurable_sampleCells_grid n (b ^ min j h) (pow_pos hb _))

lemma stageMass_adapted {n : ℕ} (b h : ℕ) (hb : 0 < b) (Y : Fin n → ℕ) :
    StronglyAdapted (stageFiltration n b h hb) (stageMass b h hb Y) := by
  intro j
  by_cases hj : j < h
  · have he : min j h = j := Nat.min_eq_left hj.le
    have hf : stageMass b h hb Y j = fun U ↦ interiorMass (b^j) (b^(h-j-1)) b (b^j)
        (sampleCells n (b^j) (pow_pos hb _) U) Y := by funext U; simp [stageMass, hj]
    rw [hf]
    have hmeas := (measurable_of_countable (fun p : Fin n → ℕ ↦
      interiorMass (b^j) (b^(h-j-1)) b (b^j) p Y)).comp
        (measurable_sampleCells_grid n (b^j) (pow_pos hb _))
    change StronglyMeasurable[sampleGridSigma n (b ^ min j h)]
      (fun U ↦ interiorMass (b^j) (b^(h-j-1)) b (b^j) (sampleCells n (b^j) (pow_pos hb _) U) Y)
    exact hmeas.stronglyMeasurable.mono (by rw [he])
  · have hf : stageMass b h hb Y j = fun _ ↦ (0 : ℝ) := by funext U; simp [stageMass, hj]
    rw [hf]
    exact stronglyMeasurable_const

lemma stagePotential_measurable {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) (j : ℕ) :
    Measurable (stagePotential b h hb χ Y j) :=
  ((stagePotential_adapted b h hb χ Y j).mono ((stageFiltration n b h hb).le j)).measurable

lemma stageMass_measurable {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (Y : Fin n → ℕ) (j : ℕ) : Measurable (stageMass b h hb Y j) :=
  ((stageMass_adapted b h hb Y j).mono ((stageFiltration n b h hb).le j)).measurable

lemma stagePotential_nonneg {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (Y : Fin n → ℕ) (j : ℕ) (U : Fin n → ℝ) : 0 ≤ stagePotential b h hb χ Y j U :=
  gridPotential_nonneg _ _ _ _ _ _ _

lemma stagePotential_abs_le {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (hχ : ∀ i, |χ i| ≤ 1) (Y : Fin n → ℕ) (j : ℕ) (U : Fin n → ℝ) :
    |stagePotential b h hb χ Y j U| ≤ 2 * n := by
  rw [abs_of_nonneg (stagePotential_nonneg b h hb χ Y j U)]
  exact gridPotential_le_two_n _ _ _ _ χ hχ _ _

lemma stageMass_nonneg {n : ℕ} (b h : ℕ) (hb : 0 < b) (Y : Fin n → ℕ)
    (j : ℕ) (U : Fin n → ℝ) : 0 ≤ stageMass b h hb Y j U := by
  unfold stageMass
  split_ifs
  · exact interiorMass_nonneg _ _ _ _ _ _
  · rfl

lemma stage_rectangles (b h j : ℕ) (hj : j < h) : b ^ j * b ^ (h-j-1) = b ^ (h-1) := by
  rw [← pow_add]
  congr 1
  omega

lemma stage_fine_vertical (b h j : ℕ) (hj : j < h) : b ^ (h-j-1) * (b * b ^ j) = b ^ h := by
  rw [← pow_succ', ← pow_add]
  congr 1
  omega

lemma stageMass_abs_le {n : ℕ} (b h : ℕ) (hb : 0 < b) (Y : Fin n → ℕ)
    (j : ℕ) (U : Fin n → ℝ) : |stageMass b h hb Y j U| ≤ (b ^ (h-1) : ℕ) * Real.sqrt n := by
  rw [abs_of_nonneg (stageMass_nonneg b h hb Y j U)]
  unfold stageMass
  split_ifs with hj
  · exact (interiorMass_le_sqrt _ _ _ _ _ _).trans_eq (by rw [stage_rectangles b h j hj])
  · positivity

lemma stagePotential_zero {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (Y : Fin n → ℕ) (U : Fin n → ℝ) : stagePotential b h hb χ Y 0 U = 0 := by
  simp only [stagePotential, Nat.zero_min, pow_zero, actualPotential]
  exact gridPotential_one _ _ _ _ _

lemma stagePotential_terminal {n : ℕ} (b h : ℕ) (hb : 0 < b) (χ : Fin n → ℝ)
    (Y : Fin n → ℕ) (U : Fin n → ℝ) : stagePotential b h hb χ Y h U =
      actualPotential (b^h) 1 (b^h) (pow_pos hb _) (pow_pos hb _) χ Y U := by
  simp [stagePotential]

end
end Oscillation
