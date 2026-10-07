import Oscillation
import R56Audit.SymmetricSumsGeneral

/-!
# Fact 2.2 for functions of independent uniform digits

Auditor's supplement (not part of the audited archive).

In the local experiment of Section 2.3 the randomness consists of independent uniform digits.
`fact_2_2_uniform` is Fact 2.2 (`fact_2_2_general`) in this setting: the probability space is
`ι → D` with the law `digitLaw ι D` of independent uniform digits, where `D` carries the
discrete σ-algebra. Its expectation is the finite average `Oscillation.finAvg`
(`integral_digitLaw`), the digits are independent (`ProbabilityTheory.iIndepFun_pi`), and a
function of one digit that is negated by a permutation of the digits is symmetric
(`identDistrib_coord_neg`).
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory Oscillation

noncomputable section

/-! ### Independent uniform digits -/

section Uniform

variable {ι D : Type*} [Fintype ι] [Fintype D] [Nonempty D] [MeasurableSpace D]

/-- The law of independent uniform digits: the product over `ι` of the uniform law on `D`. -/
abbrev digitLaw (ι D : Type*) [Fintype ι] [Fintype D] [Nonempty D] [MeasurableSpace D] :
    Measure (ι → D) :=
  Measure.pi fun _ : ι => (PMF.uniformOfFintype D).toMeasure

/-- The law of a function of one of the independent uniform digits. -/
lemma map_digitLaw_coord {β : Type*} [MeasurableSpace β] (i : ι) {g : D → β}
    (hg : Measurable g) :
    Measure.map (fun r : ι → D => g (r i)) (digitLaw ι D) =
      Measure.map g (PMF.uniformOfFintype D).toMeasure := by
  have h := measurePreserving_eval (fun _ : ι => (PMF.uniformOfFintype D).toMeasure) i
  have h1 := Measure.map_map (μ := digitLaw ι D) hg h.measurable
  rw [h.map_eq] at h1
  exact h1.symm

variable [MeasurableSingletonClass D]

/-- The uniform law on a finite set is invariant under permutations. -/
lemma map_equiv_uniform (e : D ≃ D) :
    (PMF.uniformOfFintype D).toMeasure.map e = (PMF.uniformOfFintype D).toMeasure := by
  refine Measure.ext_of_singleton fun a => ?_
  have hpre : e ⁻¹' {a} = {e.symm a} := by
    ext d
    simp [Equiv.eq_symm_apply]
  rw [Measure.map_apply .of_discrete (measurableSet_singleton a), hpre,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]

/-- Independent uniform digits are jointly uniform: the product of the uniform laws on `D` is
the uniform law on `ι → D`. -/
lemma digitLaw_eq_uniform [DecidableEq ι] :
    digitLaw ι D = (PMF.uniformOfFintype (ι → D)).toMeasure := by
  refine Measure.ext_of_singleton fun r => ?_
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton r),
    PMF.uniformOfFintype_apply]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Nat.cast_pow, ENNReal.inv_pow]

/-- For independent uniform digits the expectation is the finite average. -/
lemma integral_digitLaw [DecidableEq ι] (f : (ι → D) → ℝ) :
    ∫ r, f r ∂digitLaw ι D = finAvg f := by
  rw [digitLaw_eq_uniform, integral_uniform_eq_finAvg]

/-- The expectation of a function of one of the independent uniform digits. -/
lemma integral_digitLaw_coord (i : ι) (g : D → ℝ) :
    ∫ r, g (r i) ∂digitLaw ι D = finAvg g := by
  have h := measurePreserving_eval (fun _ : ι => (PMF.uniformOfFintype D).toMeasure) i
  have h1 := integral_map h.aemeasurable (f := g) (Measurable.of_discrete.aestronglyMeasurable)
  rw [h.map_eq, integral_uniform_eq_finAvg] at h1
  exact h1.symm

/-- A function of one of the independent uniform digits that is negated by a permutation of
the digits is symmetric. -/
lemma identDistrib_coord_neg (i : ι) (g : D → ℝ) (φ : D ≃ D) (hφ : ∀ d, g (φ d) = -g d) :
    IdentDistrib (fun r : ι → D => g (r i)) (fun r => -g (r i)) (digitLaw ι D)
      (digitLaw ι D) := by
  have hg : Measurable g := .of_discrete
  have hng : Measurable fun d => -g d := .of_discrete
  have e : (fun d => -g d) = g ∘ φ := by
    funext d
    exact (hφ d).symm
  refine ⟨(hg.comp (measurable_pi_apply i)).aemeasurable,
    (hng.comp (measurable_pi_apply i)).aemeasurable, ?_⟩
  rw [map_digitLaw_coord i hg, map_digitLaw_coord i hng, e,
    ← Measure.map_map hg .of_discrete, map_equiv_uniform]

end Uniform

/-- **Fact 2.2 for functions of independent uniform digits.** The probability space is the
finite product `ι → D` with the uniform law (`Oscillation.finAvg` is the expectation),
`X_i = x_i(r_i)` is a function of the `i`-th digit, and the symmetry of `X_i` is witnessed
by a permutation `φ_i` of the digits with `x_i ∘ φ_i = -x_i`. This is an instance of
`fact_2_2_general`. -/
theorem fact_2_2_uniform {ι D : Type*} [Fintype ι] [DecidableEq ι] [Fintype D] [Nonempty D]
    (x : ι → D → ℝ) (φ : ι → D ≃ D) (hφ : ∀ i d, x i (φ i d) = -x i d) {σ : ℝ} (hσ : 0 < σ)
    (h2 : ∀ i, finAvg (fun d => x i d ^ 2) = σ ^ 2)
    (h4 : ∀ i, finAvg (fun d => x i d ^ 4) ≤ 3 * σ ^ 4) (θ : ℝ) :
    σ * Real.sqrt (Fintype.card ι / 3) ≤ finAvg (fun r : ι → D => |θ + ∑ i, x i (r i)|) := by
  -- the digits carry the discrete σ-algebra, and `ι → D` the law of independent uniform digits
  let _ : MeasurableSpace D := ⊤
  have h := fact_2_2_general (μ := digitLaw ι D) (fun i r => x i (r i))
    (iIndepFun_pi (X := x) fun _ => Measurable.of_discrete.aemeasurable)
    (fun i => identDistrib_coord_neg i (x i) (φ i) (hφ i)) hσ
    (fun i => (integral_digitLaw_coord i fun d => x i d ^ 2).trans (h2 i))
    (fun _ => Integrable.of_finite)
    (fun i => (integral_digitLaw_coord i fun d => x i d ^ 4).trans_le (h4 i)) θ
  rwa [integral_digitLaw] at h

end

end R56Audit
