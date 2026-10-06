import Oscillation.Histogram
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Exact transport from iid points to their finite bucket labels. -/
namespace Oscillation
open scoped BigOperators
open MeasureTheory
noncomputable section

variable {α Ω : Type*} [MeasurableSpace α] [Fintype Ω] [DecidableEq Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The actual probability of a classification bucket. -/
def bucketProbability (μ : Measure α) (cell : α → Ω) (c : Ω) : ℝ :=
  (μ {x | cell x = c}).toReal

omit [DecidableEq Ω] in
/-- Mapping each iid point to its bucket gives the genuine product of bucket probabilities. -/
theorem integral_iid_buckets (μ : Measure α) [IsFiniteMeasure μ]
    (cell : α → Ω) (hcell : Measurable cell) (n : ℕ) (F : (Fin n → Ω) → ℝ) :
    (∫ P : Fin n → α, F (fun i => cell (P i)) ∂Measure.pi (fun _ => μ)) =
      ∑ x : Fin n → Ω, productWeight (bucketProbability μ cell) x * F x := by
  have hm : Measurable (fun P : Fin n → α => fun i => cell (P i)) :=
    Measurable.of_eval (fun i => hcell.comp (measurable_pi_apply i))
  rw [← integral_map hm.aemeasurable (.of_discrete)]
  rw [Measure.pi_map_pi (fun _ => hcell.aemeasurable)]
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod, smul_eq_mul, productWeight]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.map_apply hcell (measurableSet_singleton _)]
  rfl

/-- Sum of square roots of the actual interior bucket counts in a sample. -/
def bucketSquareRootSum {n M : ℕ} (cell : α → Option (Fin M)) (P : Fin n → α) : ℝ :=
  ∑ c : Fin M, Real.sqrt ((Finset.univ.filter (fun i => cell (P i) = some c)).card)

omit [MeasurableSpace α] in
lemma bucketSquareRootSum_eq {n M : ℕ} (cell : α → Option (Fin M)) (P : Fin n → α) :
    bucketSquareRootSum cell P = interiorSum (histogram (fun i => cell (P i))) := by
  simp only [bucketSquareRootSum, interiorSum, histogramCount_eq_card]

/-- The paper's one-layer Laplace bound for actual iid samples of any finite measure. -/
theorem integral_iid_interior_laplace (μ : Measure α) [IsFiniteMeasure μ]
    {n M : ℕ} [MeasurableSpace (Option (Fin M))]
    [MeasurableSingletonClass (Option (Fin M))] (hn : 0 < n) (hM : 0 < M) {b : ℝ} (hb : 0 < b)
    (cell : α → Option (Fin M)) (hcell : Measurable cell)
    (hgood : ∀ c, (μ {x | cell x = some c}).toReal ≤ 1/M)
    (hbad : (μ {x | cell x = none}).toReal ≤ 4/b) :
    (∫ P : Fin n → α, Real.exp (-Real.sqrt (b*n/M) * bucketSquareRootSum cell P)
      ∂Measure.pi (fun _ => μ)) ≤ (2:ℝ)^(n+M) * (4/b)^n := by
  simp_rw [bucketSquareRootSum_eq]
  rw [integral_iid_buckets μ cell hcell n
    (fun x => Real.exp (-Real.sqrt (b*n/M) * interiorSum (histogram x)))]
  exact iid_interior_laplace hn hM hb (bucketProbability μ cell)
    (fun _ => ENNReal.toReal_nonneg) hgood hbad


omit [DecidableEq Ω] in
lemma measurable_iid_bucket_function (cell : α → Ω) (hcell : Measurable cell)
    (n : ℕ) (F : (Fin n → Ω) → ℝ) :
    Measurable (fun P : Fin n → α => F (fun i => cell (P i))) :=
  (measurable_of_countable F).comp (Measurable.of_eval fun i => hcell.comp (measurable_pi_apply i))

omit [DecidableEq Ω] in
lemma integrable_iid_bucket_function (μ : Measure α) [IsFiniteMeasure μ]
    (cell : α → Ω) (hcell : Measurable cell) (n : ℕ) (F : (Fin n → Ω) → ℝ) :
    Integrable (fun P : Fin n → α => F (fun i => cell (P i))) (Measure.pi (fun _ => μ)) := by
  have hm : Measurable (fun P : Fin n → α => fun i => cell (P i)) :=
    Measurable.of_eval (fun i => hcell.comp (measurable_pi_apply i))
  exact Integrable.of_finite.comp_measurable hm

/-- Version whose assumptions are bounds on the genuine ENNReal bucket measures. -/
theorem integral_iid_interior_laplace_of_measure (μ : Measure α) [IsFiniteMeasure μ]
    {n M : ℕ} [MeasurableSpace (Option (Fin M))] [MeasurableSingletonClass (Option (Fin M))]
    (hn : 0 < n) (hM : 0 < M) {b : ℝ} (hb : 0 < b)
    (cell : α → Option (Fin M)) (hcell : Measurable cell)
    (hgood : ∀ c, μ {x | cell x = some c} ≤ ENNReal.ofReal (1/M))
    (hbad : μ {x | cell x = none} ≤ ENNReal.ofReal (4/b)) :
    (∫ P : Fin n → α, Real.exp (-Real.sqrt (b*n/M) * bucketSquareRootSum cell P)
      ∂Measure.pi (fun _ => μ)) ≤ (2:ℝ)^(n+M) * (4/b)^n := by
  apply integral_iid_interior_laplace μ hn hM hb cell hcell
  · intro c
    simpa only [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1/(M:ℝ))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgood c)
  · simpa only [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 4/b)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad

end
end Oscillation
