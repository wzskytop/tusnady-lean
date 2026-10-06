import Oscillation.RowComparison
import Oscillation.MatrixAverage

namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 1000000

lemma averaged_refined_weight {n : ℕ} (d : ℕ) (hd : 0 < d)
    (p : Fin n → ℕ) (i : Fin n) (c : ℕ) :
    finAvg (fun k : Fin (2 * d) => finAvg (fun r : Fin n → Fin (2 * d) =>
      endpointWeight (refinedPositions p r i) (2 * d * c + k.val))) = endpointWeight (p i) c := by
  letI : Nonempty (Fin (2 * d)) := ⟨⟨0, by omega⟩⟩
  simp only [refinedPositions]
  have hev (k : Fin (2 * d)) := finAvg_eval i
    (fun r : Fin (2 * d) => endpointWeight (2 * d * p i + r.val) (2 * d * c + k.val))
  simp_rw [hev, endpointWeight_refine (by omega : 0 < 2 * d)]
  by_cases hlt : p i < c
  · simp [hlt, endpointWeight, ne_of_lt hlt]
  · by_cases he : p i = c
    · simp only [he, lt_self_iff_false, ite_false, ite_true]
      rw [matrix_double_mean d hd]
      norm_num [endpointWeight]
    · simp [hlt, he, endpointWeight]

lemma averaged_endpoint_baseline {n : ℕ} (d : ℕ) (hd : 0 < d)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (c y : ℕ) :
    finAvg (fun r : Fin n → Fin (2 * d) => finAvg (fun k : Fin (2 * d) =>
      endpointValue χ (refinedPositions p r) Y (2 * d * c + k.val) y)) =
      endpointValue χ p Y c y := by
  rw [finAvg_finAvg_comm]
  unfold endpointValue
  simp_rw [finAvg_sum, finAvg_const_mul]
  simp_rw [averaged_refined_weight d hd]

lemma half_averaged_rowDifference {n : ℕ} (d : ℕ) (hd : 0 < d)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (c : ℕ) (y : Fin (2 * d) → ℕ)
    (k : Fin (2 * d)) (ξ : Fin n → Bool) :
    finAvg (fun ρ : Fin n → Fin d => rowDifference χ
      (refinedPositions p (fun i => halfDigit d hd (ξ i) (ρ i))) Y (2 * d * c + k.val) y) =
      -(∑ i, χ i * representativeKernel y (Y i) *
        (if p i < c then 1 else if p i = c then rowMean d k else 0)) +
      rademacherSum (fun i => -halfGain d k * kernelWeights χ p Y c y i) ξ := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  simp_rw [rowDifference_eq, show ∀ (ρ : Fin n → Fin d) (i : Fin n),
      refinedPositions p (fun i => halfDigit d hd (ξ i) (ρ i)) i =
        2 * d * p i + (halfDigit d hd (ξ i) (ρ i)).val from fun _ _ => rfl]
  simp_rw [show ∀ ρ : Fin n → Fin d,
      -(∑ i, χ i * representativeKernel y (Y i) *
          endpointWeight (2 * d * p i + (halfDigit d hd (ξ i) (ρ i)).val) (2 * d * c + k.val)) =
      (-1 : ℝ) * (∑ i, χ i * representativeKernel y (Y i) *
          endpointWeight (2 * d * p i + (halfDigit d hd (ξ i) (ρ i)).val) (2 * d * c + k.val))
      from fun _ => by ring]
  rw [finAvg_const_mul]
  simp_rw [finAvg_sum, finAvg_const_mul]
  have hev (i : Fin n) := finAvg_eval i
    (fun s : Fin d => endpointWeight (2 * d * p i + (halfDigit d hd (ξ i) s).val)
      (2 * d * c + k.val))
  simp_rw [hev, endpointWeight_refine (by omega : 0 < 2 * d)]
  have hav : ∀ i : Fin n, finAvg (fun s : Fin d =>
      if p i < c then (1 : ℝ) else if p i = c then
        endpointWeight (halfDigit d hd (ξ i) s).val k.val else 0) =
      (if p i < c then 1 else if p i = c then rowMean d k else 0) +
        (if p i = c then halfGain d k * boolSign (ξ i) else 0) := by
    intro i
    by_cases hlt : p i < c
    · simp [hlt, ne_of_lt hlt]
    · by_cases he : p i = c
      · simp [hlt, he, halfDigit_mean]
      · simp [hlt, he]
  simp_rw [hav]
  unfold rademacherSum kernelWeights
  rw [← sum_neg_distrib, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp_all <;> ring

lemma rowDifference_abs_gain {n d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (p Y : Fin n → ℕ)
    (c v : ℕ) (k : Fin (2 * d)) :
    halfGain d k * Real.sqrt (interiorCount (2 * d) m p Y c v) / 2 ≤
      finAvg (fun r : Fin n → Fin (2 * d) => |rowDifference χ (refinedPositions p r) Y
        (2 * d * c + k.val) (representativeHeight (b := 2 * d) hm χ p Y c v)|) := by
  let y := representativeHeight (b := 2 * d) hm χ p Y c v
  let a : Fin n → ℝ := fun i => -halfGain d k * kernelWeights χ p Y c y i
  let offset : ℝ := -(∑ i, χ i * representativeKernel y (Y i) *
    (if p i < c then 1 else if p i = c then rowMean d k else 0))
  have hκ := kernelWeights_variance hd hm χ hχ p Y c v
  have hcg := halfGain_nonneg d hd k
  have hs : (halfGain d k)^2 * (interiorCount (2 * d) m p Y c v : ℝ) ≤ ∑ i, (a i)^2 := by
    calc
      _ ≤ (halfGain d k)^2 * ∑ i, (kernelWeights χ p Y c y i)^2 :=
        mul_le_mul_of_nonneg_left hκ (sq_nonneg _)
      _ = _ := by simp [a, mul_pow, mul_sum]
  have hsqrt : halfGain d k * Real.sqrt (interiorCount (2 * d) m p Y c v) ≤
      Real.sqrt (∑ i, (a i)^2) := by
    have := Real.sqrt_le_sqrt hs
    simpa only [Real.sqrt_mul (sq_nonneg (halfGain d k)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hcg] using this
  calc
    _ ≤ Real.sqrt (∑ i, (a i)^2) / 2 :=
      div_le_div_of_nonneg_right hsqrt (by norm_num)
    _ ≤ finAvg (fun ξ : Fin n → Bool => |offset + rademacherSum a ξ|) :=
      shifted_rademacher_abs n a offset
    _ = finAvg (fun ξ : Fin n → Bool => |finAvg (fun ρ : Fin n → Fin d =>
        rowDifference χ (refinedPositions p (fun i => halfDigit d hd (ξ i) (ρ i))) Y
          (2 * d * c + k.val) y)|) := by
      apply finAvg_congr
      intro ξ
      exact congrArg abs (half_averaged_rowDifference d hd χ p Y c y k ξ).symm
    _ ≤ finAvg (fun ξ : Fin n → Bool => finAvg (fun ρ : Fin n → Fin d =>
        |rowDifference χ (refinedPositions p (fun i => halfDigit d hd (ξ i) (ρ i))) Y
          (2 * d * c + k.val) y|)) := finAvg_mono (fun _ => abs_finAvg_le _)
    _ = _ := (halfDigits_finAvg d hd (fun r : Fin n → Fin (2 * d) =>
      |rowDifference χ (refinedPositions p r) Y (2 * d * c + k.val) y|)).symm

end
end Oscillation
