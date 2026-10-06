import Oscillation.DirectAccumulation

namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset Riesz
open scoped ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The centered error, with the actual conditional expectation, not a drift lower bound. -/
def centeredError (F : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ) (h : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ range h, (Z (j+1) ω - (μ[Z (j+1) | F j]) ω)

omit [IsProbabilityMeasure μ] in
/-- Finite conditional means identify the centered sum almost everywhere. -/
lemma centeredError_eq {α : Type*} [Fintype α]
    (F : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ) (Y : ℕ → Ω → α → ℝ) (h : ℕ)
    (hlaw : ∀ j < h, HasFiniteConditionalLaw (μ := μ) (F j) (Z (j+1)) (Y j)) :
    centeredError (μ := μ) F Z h =ᵐ[μ]
      (fun ω => ∑ j ∈ range h, (Z (j+1) ω - finAvg (Y j ω))) := by
  have he : ∀ j ∈ range h, μ[Z (j+1) | F j] =ᵐ[μ] (fun ω => finAvg (Y j ω)) := by
    intro j hj
    simpa using hlaw j (mem_range.mp hj) id continuous_id
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (he j))] with ω hω
  exact sum_congr rfl (fun j hj => by rw [hω j hj])

/-- Centered accumulation needs no drift and no assumption that Z_0 is zero. -/
theorem integral_exp_centered_le {α : Type*} [Fintype α] [Nonempty α]
    (F : Filtration ℕ mΩ) (n h : ℕ) (Z : ℕ → Ω → ℝ)
    (Y : ℕ → Ω → (Fin n → α) → ℝ)
    (hZ : StronglyAdapted F Z)
    (hmean : StronglyAdapted F (fun j ω => finAvg (Y j ω)))
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ j ω, |Z j ω| ≤ K ∧ |finAvg (Y j ω)| ≤ K)
    {d : ℝ} (hd : 0 ≤ d) (u : ℝ) (hu : 0 ≤ u)
    (hlaw : ∀ j < h, HasFiniteConditionalLaw (μ := μ) (F j) (Z (j+1)) (Y j))
    (hosc : ∀ j < h, ∀ᵐ ω ∂μ, CoordinateOscillation (Y j ω) d) :
    (∫ ω, Real.exp (-u * centeredError (μ := μ) F Z h ω) ∂μ) ≤
      Real.exp ((h:ℝ)*n*u^2*d^2/2) := by
  let c := (n:ℝ)*u^2*d^2/2
  let W : ℕ → Ω → ℝ := fun j ω => Real.exp (-u*(Z (j+1) ω-finAvg (Y j ω))-c)
  have hW (j) : StronglyMeasurable[F (j+1)] (W j) := by
    have hz := (hZ (j+1)).measurable
    have hm := ((hmean j).mono (F.mono (Nat.le_succ j))).measurable
    apply Measurable.stronglyMeasurable
    dsimp [W]; fun_prop
  have hWbound : ∀ j ω, 0 ≤ W j ω ∧ W j ω ≤ Real.exp (2*u*K+|c|) := by
    intro j ω
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩
    have hz := (abs_le.mp (hbound (j+1) ω).1).1
    have hm := (abs_le.mp (hbound j ω).2).2
    have hc := neg_le_abs c
    change -u*(Z (j+1) ω-finAvg (Y j ω))-c ≤ _
    nlinarith
  have hcond : ∀ j < h, ∀ᵐ ω ∂μ, (μ[W j | F j]) ω ≤ 1 := by
    intro j hj
    have H := condExp_exp_drift_le_of_finite_law (F.le j) n (Z (j+1))
      (fun ω => finAvg (Y j ω)) (fun _ => 0) (Y j)
      ((hZ (j+1)).mono (F.le (j+1))).measurable (hmean j) stronglyMeasurable_const
      K (fun ω => ⟨(hbound (j+1) ω).1, (hbound j ω).2, by simpa using hK⟩)
      hd u hu (hlaw j hj) (hosc j hj) (Filter.Eventually.of_forall (fun _ => by simp))
    simpa [W,c] using H
  have hp := integral_prefixProduct_le_of_cond F W (Real.exp (2*u*K+|c|)) hW hWbound h hcond
  have he (ω) : Riesz.prefixProduct W h ω =
      Real.exp (-u*(∑ j ∈ range h, (Z (j+1) ω-finAvg (Y j ω)))-h*c) := by
    simp only [Riesz.prefixProduct, W, ← Real.exp_sum]
    congr 1
    simp only [sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have ht := centeredError_eq F Z Y h hlaw
  have hp' : (∫ ω, Real.exp (-u*centeredError (μ := μ) F Z h ω-h*c) ∂μ) ≤ 1 := by
    convert hp using 1
    apply integral_congr_ae
    filter_upwards [ht] with ω hω
    rw [he, hω]
  calc
    _ = Real.exp (h*c) * ∫ ω, Real.exp (-u*centeredError (μ := μ) F Z h ω-h*c) ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by dsimp only; rw [← Real.exp_add]; congr 1; ring)
    _ ≤ Real.exp (h*c)*1 := mul_le_mul_of_nonneg_left hp' (Real.exp_nonneg _)
    _ = _ := by dsimp [c]; rw [mul_one]; congr 1; ring

/-- The paper's centered tail, with arbitrary initial potential. -/
theorem centered_lower_tail {α : Type*} [Fintype α] [Nonempty α]
    (F : Filtration ℕ mΩ) {n h : ℕ} (hn : 0 < n) (hh : 0 < h)
    (Z : ℕ → Ω → ℝ) (Y : ℕ → Ω → (Fin n → α) → ℝ)
    (hZ : StronglyAdapted F Z)
    (hmean : StronglyAdapted F (fun j ω => finAvg (Y j ω)))
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ j ω, |Z j ω| ≤ K ∧ |finAvg (Y j ω)| ≤ K)
    (M : ℝ) (hM : 0 < M)
    (hlaw : ∀ j < h, HasFiniteConditionalLaw (μ := μ) (F j) (Z (j+1)) (Y j))
    (hosc : ∀ j < h, ∀ᵐ ω ∂μ, CoordinateOscillation (Y j ω) (1/M))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | centeredError (μ := μ) F Z h ω ≤ -t} ≤
      Real.exp (-t^2*M^2/(2*h*n)) := by
  by_cases ht0 : t = 0
  · simp only [ht0, zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_mul, zero_div, Real.exp_zero]
    exact measureReal_le_one
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let u := t*M^2/(h*n)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hu : 0 < u := by dsimp [u]; positivity
  let T := fun ω => ∑ j ∈ range h, (Z (j+1) ω-finAvg (Y j ω))
  have hT : Measurable T := Finset.measurable_sum _ (fun j _ =>
    ((hZ (j+1)).mono (F.le (j+1))).measurable.sub ((hmean j).mono (F.le j)).measurable)
  have hTb (ω) : -(h:ℝ)*(2*K) ≤ T ω := by
    calc
      _ = ∑ _j ∈ range h, -(2*K) := by simp
      _ ≤ _ := sum_le_sum (fun j _ => by
        have hz := (abs_le.mp (hbound (j+1) ω).1).1
        have hm := (abs_le.mp (hbound j ω).2).2
        linarith)
  have hiT := integrable_exp_of_bounded (μ := μ) (hT.const_mul (-u)) (u*h*(2*K))
    (fun ω => by have := hTb ω; nlinarith)
  have he := centeredError_eq F Z Y h hlaw
  have hi : Integrable (fun ω => Real.exp (-u*centeredError (μ := μ) F Z h ω)) μ := by
    apply hiT.congr
    filter_upwards [he] with ω hω
    dsimp [T]; rw [hω]
  have H := small_event_of_laplace μ (centeredError (μ := μ) F Z h) u (-t)
    (Real.exp ((h:ℝ)*n*u^2*(1/M)^2/2)) hu hi
    (integral_exp_centered_le F n h Z Y hZ hmean K hK hbound (by positivity) u hu.le hlaw hosc)
  have hex : Real.exp (u*(-t))*Real.exp ((h:ℝ)*n*u^2*(1/M)^2/2) =
      Real.exp (-t^2*M^2/(2*h*n)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [u]; field_simp; ring
  rw [hex] at H
  simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top H

/-- Continuations are truncated after the last transition to match the filtration. -/
def centeredStageContinuation {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) (j : ℕ) (U : Fin n → ℝ) (r : Fin n → Fin b) : ℝ :=
  if j < h then stageContinuation b h hb χ Y j U r else 0

lemma centeredStageContinuation_eq {n b h j : ℕ} (hb : 0 < b) (hj : j < h)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) :
    centeredStageContinuation b h hb χ Y j = stageContinuation b h hb χ Y j := by
  funext U r
  simp [centeredStageContinuation,hj]

lemma centeredStage_mean_adapted {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (χ : Fin n → ℝ) (Y : Fin n → ℕ) :
    StronglyAdapted (stageFiltration n b h hb)
      (fun j U => finAvg (centeredStageContinuation b h hb χ Y j U)) := by
  intro j
  by_cases hj : j < h
  · have hm := (measurable_of_countable (fun p : Fin n → ℕ =>
      finAvg (fun r : Fin n → Fin b => gridPotential (b*b^j) (b^(h-j-1)) (b*b^j)
        (Nat.mul_pos hb (pow_pos hb _)) χ (refinedPositions p r) Y))).comp
      (measurable_sampleCells_grid n (b^j) (pow_pos hb _))
    change StronglyMeasurable[sampleGridSigma n (b ^ min j h)]
      (fun U => finAvg (fun r => centeredStageContinuation b h hb χ Y j U r))
    rw [Nat.min_eq_left hj.le]
    convert hm.stronglyMeasurable using 1
    funext U
    apply congrArg finAvg
    funext r
    simp [centeredStageContinuation,hj,stageContinuation]
  · simpa [centeredStageContinuation,hj,finAvg] using
      (stronglyMeasurable_const : StronglyMeasurable[stageFiltration n b h hb j]
        (fun _ : Fin n → ℝ => (0:ℝ)))

lemma centeredStage_mean_bound {n : ℕ} (b h : ℕ) (hb : 0 < b)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1) (Y : Fin n → ℕ) (j : ℕ) (U : Fin n → ℝ) :
    |finAvg (centeredStageContinuation b h hb χ Y j U)| ≤ 2*n := by
  let : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
  apply (abs_finAvg_le _).trans
  apply (finAvg_mono (fun r => ?_)).trans_eq (finAvg_const (2*n))
  by_cases hj : j < h
  · simp only [centeredStageContinuation, ite_eq_left hj, stageContinuation]
    rw [abs_of_nonneg (gridPotential_nonneg _ _ _ _ _ _ _)]
    exact gridPotential_le_two_n _ _ _ _ χ hχ _ _
  · simp [centeredStageContinuation,hj]

/-- Actual horizontal iid samples, with vertical labels fixed: the bound is
for the sum centered by conditional expectations, not for `Direct.loss`. -/
theorem stage_centered_lower_tail {n b h : ℕ} (hn : 0 < n) (hb : 0 < b) (hh : 0 < h)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1) (Y : Fin n → ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin n => Riesz.PointSets.μI)).real
      {U | centeredError (μ := Measure.pi (fun _ : Fin n => Riesz.PointSets.μI))
        (stageFiltration n b h hb) (stagePotential b h hb χ Y) h U ≤ -t} ≤
      Real.exp (-t^2*(b^(h-1):ℕ)^2/(2*h*n)) := by
  let : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
  apply centered_lower_tail (stageFiltration n b h hb) hn hh
    (stagePotential b h hb χ Y) (centeredStageContinuation b h hb χ Y)
    (stagePotential_adapted b h hb χ Y) (centeredStage_mean_adapted b h hb χ Y)
    (2*n) (by positivity)
    (fun j U => ⟨stagePotential_abs_le b h hb χ hχ Y j U,
      centeredStage_mean_bound b h hb χ hχ Y j U⟩)
    (b^(h-1):ℕ) (by positivity) ?_ ?_ t ht
  · intro j hj
    simpa only [centeredStageContinuation_eq hb hj] using stage_finiteConditionalLaw hb hj χ hχ Y
  · intro j hj
    exact Filter.Eventually.of_forall (fun U => by
      simpa only [centeredStageContinuation_eq hb hj] using stage_coordinateOscillation hb hj χ hχ Y U)

/-- The old drift-compensated loss dominates the centered error; a loss tail
alone therefore cannot be used to infer a centered-error tail. -/
theorem stage_centered_le_loss {n b h : ℕ} (hb : 0 < b) (heven : Even b)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (Y : Fin n → ℕ) :
    ∀ᵐ U ∂Measure.pi (fun _ : Fin n => Riesz.PointSets.μI),
      centeredError (μ := Measure.pi (fun _ : Fin n => Riesz.PointSets.μI))
        (stageFiltration n b h hb) (stagePotential b h hb χ Y) h U ≤
      stagePotential b h hb χ Y h U -
        (∑ j ∈ range h, stageMass b h hb Y j U)/(4*b*(b^(h-1):ℕ)) := by
  let Z := stagePotential b h hb χ Y
  let Q := stageContinuation b h hb χ Y
  have he := centeredError_eq (μ := Measure.pi (fun _ : Fin n => Riesz.PointSets.μI))
    (stageFiltration n b h hb) Z Q h
    (fun j hj => stage_finiteConditionalLaw hb hj χ (fun i => (hχ i).le) Y)
  filter_upwards [he] with U hU
  rw [hU]
  calc
    _ ≤ ∑ j ∈ range h, (Z (j+1) U-Z j U-stageMass b h hb Y j U/(4*b*(b^(h-1):ℕ))) := by
      apply sum_le_sum
      intro j hj
      have H := stage_finite_drift hb heven (mem_range.mp hj) χ hχ Y U
      dsimp [Z,Q] at *
      linarith
    _ = _ := by
      rw [sum_sub_distrib, sum_increments, ← sum_div]
      dsimp [Z]
      rw [stagePotential_zero,sub_zero]

end
end Oscillation
