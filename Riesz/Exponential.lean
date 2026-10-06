import Mathlib.Probability.Moments.SubGaussian

/-!
# Exponential bounds for the Riesz-product remainder

The lemmas below use genuine measure-theoretic expectations.  In particular,
the conditional result assumes zero conditional means and bounded increments,
and derives the exponential estimate rather than assuming it.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace Riesz

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : Ω → ℝ}

/-- Hoeffding's lemma in the symmetric interval used in Section 4. -/
theorem hasSubgaussianMGF_centered_bounded [IsProbabilityMeasure μ]
    (d : ℝ≥0) (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ d) (hzero : ∫ ω, X ω ∂μ = 0) :
    HasSubgaussianMGF X (d ^ 2) μ := by
  have hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-(d : ℝ)) d := by
    filter_upwards [hbound] with ω hω
    exact abs_le.mp hω
  have heq : (‖(d : ℝ) - -(d : ℝ)‖₊ / 2) ^ 2 = d ^ 2 := by
    ext
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith [d.coe_nonneg] : 0 ≤ (d : ℝ) - -(d : ℝ))]
    ring
  simpa only [heq] using
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hX hb hzero

/-- The paper's one-step bound, valid for every real exponential parameter. -/
theorem integral_exp_le_of_centered_bounded [IsProbabilityMeasure μ]
    (d : ℝ≥0) (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ d) (hzero : ∫ ω, X ω ∂μ = 0) (t : ℝ) :
    (∫ ω, exp (t * X ω) ∂μ) ≤ exp (t ^ 2 * (d : ℝ) ^ 2 / 2) := by
  have h := (hasSubgaussianMGF_centered_bounded d hX hbound hzero).mgf_le t
  simpa only [mgf, NNReal.coe_pow, mul_comm ((d : ℝ) ^ 2) (t ^ 2)] using h

section Conditional

variable [StandardBorelSpace Ω] [IsProbabilityMeasure μ]

/-- Conditional Hoeffding: zero conditional mean and an almost-sure bound imply
the conditional exponential estimate.  No independence assumption is used. -/
theorem hasCondSubgaussianMGF_of_condCentered_bounded
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (d : ℝ≥0)
    (hX : Measurable[mΩ] X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ d)
    (hzero : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X (d ^ 2) μ := by
  let : MeasurableSpace Ω := mΩ
  have hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-(d : ℝ)) d := by
    filter_upwards [hbound] with ω hω
    exact abs_le.mp hω
  have hi : Integrable X μ := Integrable.of_mem_Icc _ _ hX.aemeasurable hb
  have hmean := condExp_ae_eq_trim_integral_condExpKernel hm hi
  have hztrim : μ[X | m] =ᵐ[μ.trim hm] 0 :=
    StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
      stronglyMeasurable_condExp stronglyMeasurable_zero hzero
  have hbkernel : ∀ᵐ ω' ∂μ.trim hm,
      ∀ᵐ ω ∂condExpKernel μ m ω', |X ω| ≤ d := by
    apply Measure.ae_ae_of_ae_comp
    rwa [condExpKernel_comp_trim hm]
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hX.aemeasurable hb
  · filter_upwards [hbkernel, hmean, hztrim] with ω hbω hmω hzω
    have hz : ∫ y, X y ∂condExpKernel μ m ω = 0 := hmω.symm.trans hzω
    exact (hasSubgaussianMGF_centered_bounded d hX.aemeasurable hbω hz).mgf_le

/-- A finite adapted sum of bounded conditionally centered increments is
subgaussian with the sum of the squared bounds as variance parameter. -/
theorem hasSubgaussianMGF_sum_of_condCentered_bounded
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ) (d : ℕ → ℝ≥0) (n : ℕ)
    (hadapted : StronglyAdapted ℱ Y)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |Y i ω| ≤ d i)
    (hzero : ∫ ω, Y 0 ω ∂μ = 0)
    (hcondzero : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω)
      (∑ i ∈ Finset.range n, (d i) ^ 2) μ := by
  by_cases hn : n = 0
  · subst n
    simp
  have h0 : HasSubgaussianMGF (Y 0) ((d 0) ^ 2) μ :=
    hasSubgaussianMGF_centered_bounded (d 0)
      ((hadapted 0).mono (ℱ.le 0)).measurable.aemeasurable
      (hbound 0 (Nat.pos_of_ne_zero hn)) hzero
  apply HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF hadapted h0 n
  intro i hi
  exact hasCondSubgaussianMGF_of_condCentered_bounded (ℱ.le i) (d (i + 1))
    ((hadapted (i + 1)).mono (ℱ.le (i + 1))).measurable
    (hbound (i + 1) (by omega)) (hcondzero i hi)

/-- The finite accumulation estimate from Section 4. Its hypotheses are
boundedness and zero conditional means, not exponential-moment bounds. -/
theorem integral_exp_sum_le_of_condCentered_bounded
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ) (d : ℝ≥0) (n : ℕ)
    (hadapted : StronglyAdapted ℱ Y)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |Y i ω| ≤ d)
    (hzero : ∫ ω, Y 0 ω ∂μ = 0)
    (hcondzero : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0) (t : ℝ) :
    (∫ ω, exp (t * ∑ i ∈ Finset.range n, Y i ω) ∂μ) ≤
      exp (n * t ^ 2 * (d : ℝ) ^ 2 / 2) := by
  have h := (hasSubgaussianMGF_sum_of_condCentered_bounded ℱ Y (fun _ ↦ d) n
    hadapted hbound hzero hcondzero).mgf_le t
  simpa only [mgf, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, mul_right_comm] using h

/-- An increment may be measurable only at the next level of the filtration.
This is the indexing used for finite conditional cell averages. -/
theorem integral_exp_sum_le_of_bounded_increments
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ) (d : ℝ≥0) (n : ℕ)
    (hmeasurable : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i))
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |Y i ω| ≤ d)
    (hcondzero : ∀ i < n, μ[Y i | ℱ i] =ᵐ[μ] 0) (t : ℝ) :
    (∫ ω, exp (t * ∑ i ∈ Finset.range n, Y i ω) ∂μ) ≤
      exp (n * t ^ 2 * (d : ℝ) ^ 2 / 2) := by
  by_cases hn : n = 0
  · subst n
    simp
  let ℱ' : Filtration ℕ mΩ :=
    { seq := fun i ↦ ℱ (i + 1)
      mono' := fun _ _ hij ↦ ℱ.mono (Nat.add_le_add_right hij 1)
      le' := fun i ↦ ℱ.le (i + 1) }
  have hzero : ∫ ω, Y 0 ω ∂μ = 0 := by
    calc
      _ = ∫ ω, (μ[Y 0 | ℱ 0]) ω ∂μ := (integral_condExp (ℱ.le 0)).symm
      _ = 0 := by
        rw [integral_congr_ae (hcondzero 0 (Nat.pos_of_ne_zero hn))]
        simp
  apply integral_exp_sum_le_of_condCentered_bounded ℱ' Y d n
    hmeasurable hbound hzero
  intro i hi
  exact hcondzero (i + 1) (by omega)

/-- A terminal variable represented by finitely many bounded, conditionally
centered differences satisfies the Section 4 exponential bound.  The process
starts at zero almost surely; no independence of its differences is required. -/
theorem integral_exp_terminal_le_of_bounded_differences
    (ℱ : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ) (d : ℝ≥0) (n : ℕ)
    (hadapted : StronglyAdapted ℱ Z) (hstart : Z 0 =ᵐ[μ] 0)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |Z (i + 1) ω - Z i ω| ≤ d)
    (hcondzero : ∀ i < n,
      μ[(fun ω ↦ Z (i + 1) ω - Z i ω) | ℱ i] =ᵐ[μ] 0) (t : ℝ) :
    (∫ ω, exp (t * Z n ω) ∂μ) ≤ exp (n * t ^ 2 * (d : ℝ) ^ 2 / 2) := by
  have hsum (k : ℕ) (ω : Ω) :
      ∑ i ∈ Finset.range k, (Z (i + 1) ω - Z i ω) = Z k ω - Z 0 ω := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  have heq : (fun ω ↦ exp (t * Z n ω)) =ᵐ[μ]
      (fun ω ↦ exp (t * ∑ i ∈ Finset.range n, (Z (i + 1) ω - Z i ω))) := by
    filter_upwards [hstart] with ω hω
    simp [hsum, hω]
  rw [integral_congr_ae heq]
  apply integral_exp_sum_le_of_bounded_increments ℱ
    (fun i ω ↦ Z (i + 1) ω - Z i ω) d n ?_ hbound hcondzero t
  intro i
  exact (hadapted (i + 1)).sub ((hadapted i).mono (ℱ.mono (Nat.le_succ i)))

end Conditional

end Riesz
