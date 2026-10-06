import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

namespace Oscillation
noncomputable section
open Finset MeasureTheory
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The normalized average on a finite set. -/
def finAvg (f : α → ℝ) : ℝ := (∑ x, f x) / Fintype.card α

lemma finAvg_congr {f g : α → ℝ} (h : ∀ x, f x = g x) : finAvg f = finAvg g := by
  unfold finAvg
  congr 1
  exact Finset.sum_congr rfl (fun x _ ↦ h x)

@[simp] lemma finAvg_const [Nonempty α] (c : ℝ) : finAvg (fun _ : α ↦ c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finAvg, hc]

lemma finAvg_add (f g : α → ℝ) : finAvg (fun x ↦ f x + g x) = finAvg f + finAvg g := by
  simp [finAvg, Finset.sum_add_distrib, add_div]

lemma finAvg_sub (f g : α → ℝ) : finAvg (fun x ↦ f x - g x) = finAvg f - finAvg g := by
  simp [finAvg, Finset.sum_sub_distrib, sub_div]

lemma finAvg_mul_const (f : α → ℝ) (c : ℝ) : finAvg (fun x ↦ f x * c) = finAvg f * c := by
  simp only [finAvg, ← Finset.sum_mul]
  ring

lemma finAvg_const_mul (c : ℝ) (f : α → ℝ) : finAvg (fun x ↦ c * f x) = c * finAvg f := by
  simp only [finAvg, ← Finset.mul_sum]
  ring

lemma finAvg_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : finAvg f ≤ finAvg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ ↦ h x)) (Nat.cast_nonneg _)

lemma finAvg_nonneg {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ finAvg f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ ↦ h x)) (Nat.cast_nonneg _)

lemma abs_finAvg_le (f : α → ℝ) : |finAvg f| ≤ finAvg (fun x ↦ |f x|) := by
  unfold finAvg
  have hc : |(Fintype.card α : ℝ)| = (Fintype.card α : ℝ) := abs_of_nonneg (by positivity)
  rw [abs_div, hc]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

lemma abs_finAvg_sub_le [Nonempty α] (f g : α → ℝ) {d : ℝ}
    (h : ∀ x, |f x - g x| ≤ d) : |finAvg f - finAvg g| ≤ d := by
  rw [← finAvg_sub]
  exact (abs_finAvg_le _).trans ((finAvg_mono h).trans_eq (finAvg_const d))

lemma finAvg_equiv (e : α ≃ β) (f : β → ℝ) : finAvg (fun x ↦ f (e x)) = finAvg f := by
  rw [finAvg, finAvg, Fintype.card_congr e, e.sum_comp]

lemma finAvg_prod (f : α × β → ℝ) :
    finAvg f = finAvg (fun x : α ↦ finAvg (fun y : β ↦ f (x,y))) := by
  simp only [finAvg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

lemma finAvg_pi_succ {n : ℕ} (f : (Fin (n + 1) → α) → ℝ) :
    finAvg f = finAvg (fun x : Fin n → α ↦ finAvg (fun y : α ↦ f (Fin.snoc x y))) := by
  let e : ((Fin n → α) × α) ≃ (Fin (n + 1) → α) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ α))
  rw [← finAvg_equiv e f, finAvg_prod]
  rfl

lemma integral_uniform_eq_finAvg [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ) : (∫ x, f x ∂(PMF.uniformOfFintype α).toMeasure) = finAvg f := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, finAvg]
  ring

lemma finAvg_sum {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    finAvg (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, finAvg (f i) := by
  simp only [finAvg, ← Finset.sum_div]
  rw [Finset.sum_comm]

lemma finAvg_div_const (f : α → ℝ) (c : ℝ) :
    finAvg (fun x ↦ f x / c) = finAvg f / c := by
  simp only [finAvg, ← Finset.sum_div]
  ring

lemma finAvg_finAvg_comm (f : α → β → ℝ) :
    finAvg (fun x ↦ finAvg (f x)) = finAvg (fun y ↦ finAvg (fun x ↦ f x y)) := by
  simp only [finAvg, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

end
end Oscillation
