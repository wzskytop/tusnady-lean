import Oscillation.BoundedDifferences
import Riesz.ConditionalProduct
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma integrable_exp_of_bounded [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (B : ℝ) (hb : ∀ ω, f ω ≤ B) : Integrable (fun ω ↦ Real.exp (f ω)) μ := by
  exact Integrable.of_mem_Icc 0 (Real.exp B) (hf.exp.aemeasurable)
    (Filter.Eventually.of_forall (fun ω ↦ ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (hb ω)⟩))

lemma memLp_exp_of_bounded [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (B : ℝ) (hb : ∀ ω, f ω ≤ B) (p : ℝ≥0∞) : MemLp (fun ω ↦ Real.exp (f ω)) p μ := by
  apply MemLp.of_bound hf.exp.aestronglyMeasurable (Real.exp B)
  exact Filter.Eventually.of_forall (fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hb ω))

/-- Conditional factors need not be bounded by one pointwise. Only their
conditional averages are at most one. -/
theorem integral_prefixProduct_le_of_cond [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (W : ℕ → Ω → ℝ) (B : ℝ)
    (hW : ∀ j, StronglyMeasurable[ℱ (j + 1)] (W j))
    (hbound : ∀ j ω, 0 ≤ W j ω ∧ W j ω ≤ B) (h : ℕ)
    (hcond : ∀ j < h, ∀ᵐ ω ∂μ, (μ[W j | ℱ j]) ω ≤ 1) :
    (∫ ω, Riesz.prefixProduct W h ω ∂μ) ≤ 1 := by
  induction h with
  | zero => simp [Riesz.prefixProduct]
  | succ h ih =>
    have hind := ih (fun j hj ↦ hcond j (by omega))
    have hP := Riesz.integrable_prefixProduct_bounded (μ := μ) ℱ W hW B hbound h
    have hWh : Integrable (W h) μ := Integrable.of_mem_Icc 0 B
      ((hW h).mono (ℱ.le (h + 1))).measurable.aemeasurable
      (Filter.Eventually.of_forall (hbound h))
    have hprod : Integrable (Riesz.prefixProduct W h * W h) μ := by
      rw [← Riesz.prefixProduct_succ]
      exact Riesz.integrable_prefixProduct_bounded (μ := μ) ℱ W hW B hbound (h + 1)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (Riesz.stronglyMeasurable_prefixProduct ℱ W hW h) hprod hWh
    have hright : Integrable (Riesz.prefixProduct W h * μ[W h | ℱ h]) μ :=
      integrable_condExp.congr hpull
    calc
      _ = ∫ ω, (μ[Riesz.prefixProduct W h * W h | ℱ h]) ω ∂μ := by
        rw [integral_condExp (ℱ.le h), Riesz.prefixProduct_succ]
      _ = ∫ ω, Riesz.prefixProduct W h ω * (μ[W h | ℱ h]) ω ∂μ := integral_congr_ae hpull
      _ ≤ ∫ ω, Riesz.prefixProduct W h ω ∂μ := by
        apply integral_mono_ae hright hP
        filter_upwards [hcond h (by omega)] with ω hω
        simpa only [Pi.mul_apply, mul_one] using mul_le_mul_of_nonneg_left hω
          (Riesz.prefixProduct_bounds_general W B hbound h ω).1
      _ ≤ 1 := hind

lemma exp_finAvg_le_finAvg_exp {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) :
    Real.exp (finAvg a) ≤ finAvg (fun i ↦ Real.exp (a i)) := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hj := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) (p := a)
    (fun _ _ ↦ by positivity) (by simp [hc]) (fun _ _ ↦ Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  simpa only [finAvg, div_eq_mul_inv, mul_comm] using hj

/-- Cauchy--Schwarz in the form needed to remove a random positive drift. -/
theorem integral_exp_split_le [IsFiniteMeasure μ] (A B : Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B) (CA CB : ℝ)
    (hAb : ∀ ω, A ω ≤ CA) (hBb : ∀ ω, B ω ≤ CB) :
    (∫ ω, Real.exp ((A ω + B ω) / 2) ∂μ) ≤
      Real.sqrt (∫ ω, Real.exp (A ω) ∂μ) * Real.sqrt (∫ ω, Real.exp (B ω) ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hf : MemLp (fun ω ↦ Real.exp (A ω / 2)) (ENNReal.ofReal 2) μ :=
    memLp_exp_of_bounded (hA.div_const 2) (CA / 2) (fun ω ↦ by linarith [hAb ω]) _
  have hg : MemLp (fun ω ↦ Real.exp (B ω / 2)) (ENNReal.ofReal 2) μ :=
    memLp_exp_of_bounded (hB.div_const 2) (CB / 2) (fun ω ↦ by linarith [hBb ω]) _
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Filter.Eventually.of_forall (fun ω ↦ (Real.exp_pos (A ω / 2)).le))
    (Filter.Eventually.of_forall (fun ω ↦ (Real.exp_pos (B ω / 2)).le)) hf hg
  have hs (x : ℝ) : (Real.exp (x / 2)) ^ (2 : ℝ) = Real.exp x := by
    rw [← Real.exp_mul]
    congr 1
    ring
  simp_rw [hs] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  convert hh using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω ↦ by dsimp only; rw [← Real.exp_add]; congr 1; ring)

/-- The conditional law of a layer is a finite uniform average. This is a
law-identification premise, not a bound on an exponential moment. -/
def HasFiniteConditionalLaw {α : Type*} [Fintype α] (m : MeasurableSpace Ω)
    (X : Ω → ℝ) (Y : Ω → α → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Continuous φ →
    μ[(fun ω ↦ φ (X ω)) | m] =ᵐ[μ] (fun ω ↦ finAvg (fun r ↦ φ (Y ω r)))

/-- A genuine finite conditional law, coordinate oscillations, and a lower
conditional drift imply the one-step exponential estimate. -/
theorem condExp_exp_drift_le_of_finite_law [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [Nonempty α] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (n : ℕ) (X z s : Ω → ℝ) (Y : Ω → (Fin n → α) → ℝ)
    (hX : Measurable[mΩ] X) (hz : StronglyMeasurable[m] z) (hs : StronglyMeasurable[m] s)
    (K : ℝ) (hbound : ∀ ω, |X ω| ≤ K ∧ |z ω| ≤ K ∧ |s ω| ≤ K)
    {d : ℝ} (hd : 0 ≤ d) (u : ℝ) (hu : 0 ≤ u)
    (hlaw : HasFiniteConditionalLaw (μ := μ) m X Y)
    (hosc : ∀ᵐ ω ∂μ, CoordinateOscillation (Y ω) d)
    (hmean : ∀ᵐ ω ∂μ, s ω ≤ finAvg (Y ω) - z ω) :
    ∀ᵐ ω ∂μ, (μ[(fun ω ↦ Real.exp (-u * (X ω - z ω) + u * s ω -
      n * u ^ 2 * d ^ 2 / 2)) | m]) ω ≤ 1 := by
  let c := (n : ℝ) * u ^ 2 * d ^ 2 / 2
  let A : Ω → ℝ := fun ω ↦ Real.exp (u * z ω + u * s ω - c)
  let E : Ω → ℝ := fun ω ↦ Real.exp (-u * X ω)
  have hA : StronglyMeasurable[m] A :=
    ((((hz.const_mul u).add (hs.const_mul u)).sub
      (stronglyMeasurable_const : StronglyMeasurable[m] (fun _ : Ω ↦ c))).measurable.exp).stronglyMeasurable
  have hE : Integrable E μ := integrable_exp_of_bounded (hX.const_mul (-u)) (u * K) (fun ω ↦ by
    have hh := (abs_le.mp (hbound ω).1).1
    nlinarith)
  have hprod : Integrable (A * E) μ := by
    have hz0 := (hz.mono hm).measurable
    have hs0 := (hs.mono hm).measurable
    have hfn : Measurable[mΩ] (fun ω ↦ u * z ω + u * s ω - c + -u * X ω) := by fun_prop
    have hi := integrable_exp_of_bounded (μ := μ) hfn (3 * u * K + |c|) (fun ω ↦ by
      have hx := (abs_le.mp (hbound ω).1).1
      have hz' := (abs_le.mp (hbound ω).2.1).2
      have hs' := (abs_le.mp (hbound ω).2.2).2
      have hc := neg_le_abs c
      nlinarith)
    exact hi.congr (Filter.Eventually.of_forall (fun ω ↦ by
      dsimp [A, E]
      rw [Real.exp_add]))
  have hpull := condExp_mul_of_stronglyMeasurable_left hA hprod hE
  have hl := hlaw (fun x ↦ Real.exp (-u * x)) (by fun_prop)
  have heq : (fun ω ↦ Real.exp (-u * (X ω - z ω) + u * s ω -
      n * u ^ 2 * d ^ 2 / 2)) = A * E := by
    funext ω
    dsimp [A, E, c]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  filter_upwards [hpull, hl, hosc, hmean] with ω hp hl' ho hm'
  rw [hp]
  simp only [Pi.mul_apply]
  rw [hl']
  change Real.exp (u * z ω + u * s ω - c) *
    finAvg (fun r ↦ Real.exp (-u * Y ω r)) ≤ 1
  rw [← finAvg_const_mul]
  have he : (fun r ↦ Real.exp (u * z ω + u * s ω - c) * Real.exp (-u * Y ω r)) =
      (fun r ↦ Real.exp (-u * (Y ω r - z ω) + u * s ω - n * u ^ 2 * d ^ 2 / 2)) := by
    funext r
    rw [← Real.exp_add]
    congr 1
    dsimp [c]
    ring
  rw [he]
  exact finAvg_exp_drift_le n (Y ω) hd ho (z ω) (s ω) u hu hm'

end
end Oscillation
