import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Iterating the coefficient Laplace bound across shapes

For nonnegative factors bounded by one, a conditional expectation bound at each
layer implies a product expectation bound. The factors may share all previously
exposed randomness; they are not assumed independent across layers.
-/

namespace Riesz
open MeasureTheory Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def prefixProduct (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ range n, Y i ω

lemma prefixProduct_succ (Y : ℕ → Ω → ℝ) (n : ℕ) :
    prefixProduct Y (n + 1) = prefixProduct Y n * Y n := by
  funext ω
  simp [prefixProduct, Finset.prod_range_succ, Pi.mul_apply]

lemma prefixProduct_bounds (Y : ℕ → Ω → ℝ)
    (hY : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ 1) (n : ℕ) (ω : Ω) :
    0 ≤ prefixProduct Y n ω ∧ prefixProduct Y n ω ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (hY i ω).1),
    Finset.prod_le_one₀ (fun i _ => (hY i ω).1) (fun i _ => (hY i ω).2)⟩

lemma stronglyMeasurable_prefixProduct (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i)) (n : ℕ) :
    StronglyMeasurable[ℱ n] (prefixProduct Y n) := by
  unfold prefixProduct
  apply Finset.stronglyMeasurable_fun_prod
  intro i hi
  exact (hY i).mono (ℱ.mono (by simpa [Finset.mem_range] using hi))

lemma integrable_prefixProduct (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i))
    (hbound : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ 1) (n : ℕ) :
    Integrable (prefixProduct Y n) μ := by
  apply Integrable.of_mem_Icc 0 1
    ((stronglyMeasurable_prefixProduct ℱ Y hY n).mono (ℱ.le n)).measurable.aemeasurable
  exact Filter.Eventually.of_forall (prefixProduct_bounds Y hbound n)

/-- A genuine conditional iteration, with no independence across layers. -/
theorem integral_prefixProduct_le (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i))
    (hbound : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ 1)
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ)
    (hcond : ∀ i < n, ∀ᵐ ω ∂μ, (μ[Y i | ℱ i]) ω ≤ q) :
    (∫ ω, prefixProduct Y n ω ∂μ) ≤ q ^ n := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
    have hind := ih (fun i hi => hcond i (by omega))
    have hP := integrable_prefixProduct (μ := μ) ℱ Y hY hbound n
    have hYn : Integrable (Y n) μ := Integrable.of_mem_Icc 0 1
      ((hY n).mono (ℱ.le (n + 1))).measurable.aemeasurable
      (Filter.Eventually.of_forall (hbound n))
    have hprod : Integrable (prefixProduct Y n * Y n) μ := by
      rw [← prefixProduct_succ]
      exact integrable_prefixProduct (μ := μ) ℱ Y hY hbound (n + 1)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (stronglyMeasurable_prefixProduct ℱ Y hY n) hprod hYn
    have hright : Integrable (prefixProduct Y n * μ[Y n | ℱ n]) μ :=
      integrable_condExp.congr hpull
    calc
      (∫ ω, prefixProduct Y (n + 1) ω ∂μ) =
          ∫ ω, (μ[prefixProduct Y n * Y n | ℱ n]) ω ∂μ := by
        rw [integral_condExp (ℱ.le n)]
        rw [prefixProduct_succ]
      _ = ∫ ω, prefixProduct Y n ω * (μ[Y n | ℱ n]) ω ∂μ := integral_congr_ae hpull
      _ ≤ ∫ ω, prefixProduct Y n ω * q ∂μ := by
        apply integral_mono_ae hright (hP.mul_const q)
        filter_upwards [hcond n (by omega)] with ω hω
        exact mul_le_mul_of_nonneg_left hω (prefixProduct_bounds Y hbound n ω).1
      _ = q * ∫ ω, prefixProduct Y n ω ∂μ := by rw [integral_mul_const]; ring
      _ ≤ q * q ^ n := mul_le_mul_of_nonneg_left hind hq
      _ = q ^ (n + 1) := by rw [pow_succ]; ring

end Riesz

namespace Riesz
open MeasureTheory Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

lemma prefixProduct_bounds_general (Y : ℕ → Ω → ℝ) (B : ℝ)
    (hY : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ B) (n : ℕ) (ω : Ω) :
    0 ≤ prefixProduct Y n ω ∧ prefixProduct Y n ω ≤ B ^ n := by
  refine ⟨Finset.prod_nonneg (fun i _ => (hY i ω).1), ?_⟩
  calc
    prefixProduct Y n ω ≤ ∏ _i ∈ range n, B :=
      Finset.prod_le_prod₀ (fun i _ => (hY i ω).1) (fun i _ => (hY i ω).2)
    _ = B ^ n := by simp

lemma integrable_prefixProduct_bounded (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i)) (B : ℝ)
    (hbound : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ B) (n : ℕ) :
    Integrable (prefixProduct Y n) μ := by
  apply Integrable.of_mem_Icc 0 (B ^ n)
    ((stronglyMeasurable_prefixProduct ℱ Y hY n).mono (ℱ.le n)).measurable.aemeasurable
  exact Filter.Eventually.of_forall (prefixProduct_bounds_general Y B hbound n)

/-- Conditionally mean-one bounded factors have a mean-one product. This holds
for every finite measure, so a restriction to a vertical cell gives its actual
local mass without introducing a new normalization assumption. -/
theorem integral_prefixProduct_eq_mass (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i)) (B : ℝ)
    (hbound : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ B) (n : ℕ)
    (hcond : ∀ i < n, μ[Y i | ℱ i] =ᵐ[μ] (1 : Ω → ℝ)) :
    (∫ ω, prefixProduct Y n ω ∂μ) = μ.real Set.univ := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
    have hind := ih (fun i hi => hcond i (by omega))
    have hYn : Integrable (Y n) μ := Integrable.of_mem_Icc 0 B
      ((hY n).mono (ℱ.le (n + 1))).measurable.aemeasurable
      (Filter.Eventually.of_forall (hbound n))
    have hprod : Integrable (prefixProduct Y n * Y n) μ := by
      rw [← prefixProduct_succ]
      exact integrable_prefixProduct_bounded (μ := μ) ℱ Y hY B hbound (n + 1)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (stronglyMeasurable_prefixProduct ℱ Y hY n) hprod hYn
    calc
      (∫ ω, prefixProduct Y (n + 1) ω ∂μ) =
          ∫ ω, (μ[prefixProduct Y n * Y n | ℱ n]) ω ∂μ := by
        rw [integral_condExp (ℱ.le n), prefixProduct_succ]
      _ = ∫ ω, prefixProduct Y n ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hpull, hcond n (by omega)] with ω hp hc
        simpa only [Pi.mul_apply, Pi.one_apply, hc, mul_one] using hp
      _ = μ.real Set.univ := hind


/-- Conditionally mean-one factors have conditional product mean one on the
initial sigma algebra. This supplies local masses on its measurable cells. -/
theorem condExp_prefixProduct_eq_one (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i)) (B : ℝ)
    (hbound : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ B) (n : ℕ)
    (hcond : ∀ i < n, μ[Y i | ℱ i] =ᵐ[μ] (1 : Ω → ℝ)) :
    μ[prefixProduct Y n | ℱ 0] =ᵐ[μ] (1 : Ω → ℝ) := by
  induction n with
  | zero =>
    have hz : prefixProduct Y 0 = (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      simp [prefixProduct]
    rw [hz, condExp_const (ℱ.le 0)]
    rfl
  | succ n ih =>
    have hind := ih (fun i hi => hcond i (by omega))
    have hYn : Integrable (Y n) μ := Integrable.of_mem_Icc 0 B
      ((hY n).mono (ℱ.le (n + 1))).measurable.aemeasurable
      (Filter.Eventually.of_forall (hbound n))
    have hprod : Integrable (prefixProduct Y n * Y n) μ := by
      rw [← prefixProduct_succ]
      exact integrable_prefixProduct_bounded (μ := μ) ℱ Y hY B hbound (n + 1)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (stronglyMeasurable_prefixProduct ℱ Y hY n) hprod hYn
    have hstep : μ[prefixProduct Y (n + 1) | ℱ n] =ᵐ[μ] prefixProduct Y n := by
      rw [prefixProduct_succ]
      filter_upwards [hpull, hcond n (by omega)] with ω hp hc
      simpa only [Pi.mul_apply, Pi.one_apply, hc, mul_one] using hp
    calc
      μ[prefixProduct Y (n + 1) | ℱ 0] =ᵐ[μ]
          μ[μ[prefixProduct Y (n + 1) | ℱ n] | ℱ 0] :=
        (condExp_condExp_of_le (ℱ.mono (Nat.zero_le n)) (ℱ.le n)).symm
      _ =ᵐ[μ] μ[prefixProduct Y n | ℱ 0] := condExp_congr_ae hstep
      _ =ᵐ[μ] (1 : Ω → ℝ) := hind

/-- The product integrates to the measure of every initial measurable cell. -/
theorem setIntegral_prefixProduct_eq_mass (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i)) (B : ℝ)
    (hbound : ∀ i ω, 0 ≤ Y i ω ∧ Y i ω ≤ B) (n : ℕ)
    (hcond : ∀ i < n, μ[Y i | ℱ i] =ᵐ[μ] (1 : Ω → ℝ))
    (s : Set Ω) (hs : MeasurableSet[ℱ 0] s) :
    (∫ ω in s, prefixProduct Y n ω ∂μ) = μ.real s := by
  have hP := integrable_prefixProduct_bounded (μ := μ) ℱ Y hY B hbound n
  have hmean := condExp_prefixProduct_eq_one (μ := μ) ℱ Y hY B hbound n hcond
  calc
    (∫ ω in s, prefixProduct Y n ω ∂μ) = ∫ ω in s, (μ[prefixProduct Y n | ℱ 0]) ω ∂μ :=
      (setIntegral_condExp (ℱ.le 0) hP hs).symm
    _ = ∫ _ω in s, (1 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hmean] with ω hω
      exact hω
    _ = μ.real s := by simp

end Riesz
