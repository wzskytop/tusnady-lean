import Oscillation.FiniteAverage
import Riesz.Exponential

/-! Bounded differences for actual finite independent coordinates. -/
namespace Oscillation
noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped NNReal
set_option maxHeartbeats 800000

variable {α : Type*} [Fintype α] [Nonempty α]

/-- A finite function whose range has diameter at most `d` satisfies the
centered Hoeffding bound. -/
theorem finAvg_exp_centered_le (f : α → ℝ) {d : ℝ} (hd : 0 ≤ d)
    (hosc : ∀ x y, |f x - f y| ≤ d) (t : ℝ) :
    finAvg (fun x ↦ Real.exp (t * (f x - finAvg f))) ≤ Real.exp (t ^ 2 * d ^ 2 / 2) := by
  let : MeasurableSpace α := ⊤
  let μ := (PMF.uniformOfFintype α).toMeasure
  have hb : ∀ x, |f x - finAvg f| ≤ d := by
    intro x
    simpa only [finAvg_const] using abs_finAvg_sub_le (fun _ ↦ f x) f (hosc x)
  have hz : (∫ x, (f x - finAvg f) ∂μ) = 0 := by
    rw [integral_uniform_eq_finAvg, finAvg_sub, finAvg_const, sub_self]
  have hh := Riesz.integral_exp_le_of_centered_bounded (μ := μ) (X := fun x ↦ f x - finAvg f)
    (⟨d, hd⟩ : ℝ≥0) (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall hb) hz t
  change (∫ x, Real.exp (t * (f x - finAvg f)) ∂μ) ≤ Real.exp (t ^ 2 * d ^ 2 / 2) at hh
  rw [show μ = (PMF.uniformOfFintype α).toMeasure from rfl, integral_uniform_eq_finAvg] at hh
  exact hh

/-- Each coordinate can change the value by at most `d`. -/
def CoordinateOscillation {n : ℕ} (f : (Fin n → α) → ℝ) (d : ℝ) : Prop :=
  ∀ x i a, |f (Function.update x i a) - f x| ≤ d

lemma coordinateOscillation_finAvg_last {n : ℕ} (f : (Fin (n + 1) → α) → ℝ) {d : ℝ}
    (hf : CoordinateOscillation f d) :
    CoordinateOscillation (fun x : Fin n → α ↦ finAvg (fun a ↦ f (Fin.snoc x a))) d := by
  intro x i a
  apply abs_finAvg_sub_le
  intro z
  rw [Fin.snoc_update]
  exact hf (Fin.snoc x z) i.castSucc a

/-- A finite-product bounded-differences theorem. The exponential estimate is
derived from the coordinate oscillations by successively averaging coordinates. -/
theorem finAvg_exp_boundedDifferences (n : ℕ) (f : (Fin n → α) → ℝ)
    {d : ℝ} (hd : 0 ≤ d) (hf : CoordinateOscillation f d) (t : ℝ) :
    finAvg (fun x ↦ Real.exp (t * (f x - finAvg f))) ≤
      Real.exp (t ^ 2 * n * d ^ 2 / 2) := by
  induction n with
  | zero =>
    have hsame (x : Fin 0 → α) : f x = finAvg f := by
      rw [← finAvg_const (α := Fin 0 → α) (f x)]
      apply finAvg_congr
      intro y
      congr 1
      exact Subsingleton.elim x y
    have he : finAvg (fun x ↦ Real.exp (t * (f x - finAvg f))) = 1 := by
      calc
        _ = finAvg (fun _ : Fin 0 → α ↦ (1 : ℝ)) := by
          apply finAvg_congr
          intro x
          rw [hsame x, sub_self, mul_zero, Real.exp_zero]
        _ = 1 := finAvg_const 1
    simp [he]
  | succ n ih =>
    let g : (Fin n → α) → ℝ := fun x ↦ finAvg (fun a ↦ f (Fin.snoc x a))
    have hg : CoordinateOscillation g d := coordinateOscillation_finAvg_last f hf
    have hm : finAvg g = finAvg f := (finAvg_pi_succ f).symm
    have hlast (x : Fin n → α) :
        finAvg (fun a ↦ Real.exp (t * (f (Fin.snoc x a) - g x))) ≤
          Real.exp (t ^ 2 * d ^ 2 / 2) := by
      apply finAvg_exp_centered_le _ hd
      intro a z
      have hh := hf (Fin.snoc x z) (Fin.last n) a
      simpa only [Fin.update_snoc_last] using hh
    rw [finAvg_pi_succ (α := α) (n := n)
      (fun x : Fin (n + 1) → α ↦ Real.exp (t * (f x - finAvg f)))]
    calc
      _ = finAvg (fun x ↦ Real.exp (t * (g x - finAvg f)) *
          finAvg (fun a ↦ Real.exp (t * (f (Fin.snoc x a) - g x)))) := by
        apply finAvg_congr
        intro x
        rw [← finAvg_const_mul]
        apply finAvg_congr
        intro a
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ finAvg (fun x ↦ Real.exp (t * (g x - finAvg f)) *
          Real.exp (t ^ 2 * d ^ 2 / 2)) :=
        finAvg_mono (fun x ↦ mul_le_mul_of_nonneg_left (hlast x) (Real.exp_pos _).le)
      _ = finAvg (fun x ↦ Real.exp (t * (g x - finAvg f))) *
          Real.exp (t ^ 2 * d ^ 2 / 2) := finAvg_mul_const _ _
      _ ≤ Real.exp (t ^ 2 * n * d ^ 2 / 2) * Real.exp (t ^ 2 * d ^ 2 / 2) := by
        rw [← hm]
        exact mul_le_mul_of_nonneg_right (ih g hg) (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (n + 1 : ℕ) * d ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

/-- A lower bound for the finite mean turns the centered bound into the
one-sided drift estimate used at a layer. -/
theorem finAvg_exp_drift_le (n : ℕ) (f : (Fin n → α) → ℝ)
    {d : ℝ} (hd : 0 ≤ d) (hf : CoordinateOscillation f d)
    (z s u : ℝ) (hu : 0 ≤ u) (hmean : s ≤ finAvg f - z) :
    finAvg (fun x ↦ Real.exp (-u * (f x - z) + u * s - n * u ^ 2 * d ^ 2 / 2)) ≤ 1 := by
  let A := (n : ℝ) * u ^ 2 * d ^ 2 / 2
  have hh := finAvg_exp_boundedDifferences n f hd hf (-u)
  have hcenter : finAvg (fun x ↦ Real.exp (-u * (f x - finAvg f))) ≤ Real.exp A := by
    convert hh using 1
    dsimp [A]
    congr 1
    ring
  calc
    _ ≤ finAvg (fun x ↦ Real.exp (-A) * Real.exp (-u * (f x - finAvg f))) := by
      apply finAvg_mono
      intro x
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [A]
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hmean)]
    _ = Real.exp (-A) * finAvg (fun x ↦ Real.exp (-u * (f x - finAvg f))) := finAvg_const_mul _ _
    _ ≤ Real.exp (-A) * Real.exp A := mul_le_mul_of_nonneg_left hcenter (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end
end Oscillation
