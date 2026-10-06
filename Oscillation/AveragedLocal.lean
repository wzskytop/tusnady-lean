import Oscillation.LocalDrift

namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 300000

lemma finAvg_neg {α : Type*} [Fintype α] (f : α → ℝ) :
    finAvg (fun x => -f x) = -finAvg f := by simp [finAvg, sum_neg_distrib, neg_div]

lemma sum_digit_values (d : ℕ) :
    2 * (∑ s : Fin d, (s.val : ℝ)) = (d:ℝ)*((d:ℝ)-1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Average all children before conditioning on a point's half choice. -/
lemma averaged_child_weight {b : ℕ} (hb : 0 < b) (r : Fin b) :
    finAvg (fun k : Fin b => endpointWeight r.val k.val) =
      1 - ((r.val:ℝ)+1/2)/b := by
  have hs (k : Fin b) : endpointWeight r.val k.val = 1-endpointWeight k.val r.val := by
    unfold endpointWeight
    split_ifs <;> norm_num at * <;> omega
  simp_rw [hs]
  unfold finAvg
  rw [sum_sub_distrib, sum_endpointWeight_inside]
  simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin, mul_one]
  field_simp

lemma averaged_half_weight (d : ℕ) (hd : 0 < d) (ξ : Bool) :
    finAvg (fun s : Fin d => finAvg (fun k : Fin (2*d) =>
      endpointWeight (halfDigit d hd ξ s).val k.val)) = 1/2 + boolSign ξ/4 := by
  simp_rw [averaged_child_weight (by omega : 0 < 2*d)]
  have hs := sum_digit_values d
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  cases ξ <;>
    simp only [halfDigit, Bool.false_eq_true, ↓reduceIte, boolSign, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] <;>
    unfold finAvg <;>
    simp only [sum_sub_distrib, sum_add_distrib, ← sum_div, sum_const,
      nsmul_eq_mul, card_univ, Fintype.card_fin, mul_one] <;>
    field_simp <;> nlinarith

lemma half_averaged_child_difference {n : ℕ} (d : ℕ) (hd : 0 < d)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (c : ℕ) (y : Fin (2*d) → ℕ)
    (ξ : Fin n → Bool) :
    finAvg (fun ρ : Fin n → Fin d => finAvg (fun k : Fin (2*d) =>
      rowDifference χ (refinedPositions p (fun i => halfDigit d hd (ξ i) (ρ i))) Y
        (2*d*c+k.val) y)) = rowDifference χ p Y c y +
      rademacherSum (fun i => -(1/4:ℝ)*kernelWeights χ p Y c y i) ξ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : Nonempty (Fin (2*d)) := ⟨⟨0,by omega⟩⟩
  simp_rw [rowDifference_eq, finAvg_neg, finAvg_sum]
  simp_rw [refinedPositions, endpointWeight_refine (by omega : 0<2*d)]
  have hi (i : Fin n) :
      finAvg (fun ρ : Fin n → Fin d => finAvg (fun k : Fin (2*d) =>
        χ i * representativeKernel y (Y i) *
        (if p i < c then 1 else if p i = c then endpointWeight (halfDigit d hd (ξ i) (ρ i)).val k.val else 0))) =
      χ i * representativeKernel y (Y i) *
        (endpointWeight (p i) c + (if p i = c then boolSign (ξ i)/4 else 0)) := by
    simp_rw [finAvg_const_mul]
    rw [finAvg_eval i (fun s : Fin d => finAvg (fun k : Fin (2*d) =>
      if p i < c then (1:ℝ) else if p i = c then endpointWeight (halfDigit d hd (ξ i) s).val k.val else 0))]
    by_cases hlt : p i < c
    · simp [hlt,ne_of_lt hlt,endpointWeight]
    · by_cases he : p i = c
      · simp only [hlt,he,lt_self_iff_false,ite_false,ite_true,averaged_half_weight]
        simp [endpointWeight]
      · simp [hlt,he,endpointWeight]
  simp_rw [hi]
  unfold rademacherSum kernelWeights
  simp only [← sum_neg_distrib]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  split_ifs <;> ring

lemma averaged_child_difference_gain {n d m : ℕ} (hd : 0<d) (hm : 0<m)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i|=1) (p Y : Fin n → ℕ) (c v : ℕ) :
    Real.sqrt (interiorCount (2*d) m p Y c v)/8 ≤
      finAvg (fun r : Fin n → Fin (2*d) => |finAvg (fun k : Fin (2*d) =>
        rowDifference χ (refinedPositions p r) Y (2*d*c+k.val)
          (representativeHeight (b:=2*d) hm χ p Y c v))|) := by
  let y := representativeHeight (b:=2*d) hm χ p Y c v
  let a := fun i => -(1/4:ℝ)*kernelWeights χ p Y c y i
  have hv := kernelWeights_variance hd hm χ hχ p Y c v
  have hs : (1/4:ℝ)^2*(interiorCount (2*d) m p Y c v:ℝ) ≤ ∑ i, (a i)^2 := by
    calc
      _ ≤ (1/4:ℝ)^2*∑ i, (kernelWeights χ p Y c y i)^2 := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = _ := by simp [a,mul_pow,mul_sum]
  have hr := Real.sqrt_le_sqrt hs
  simp only [Real.sqrt_mul (sq_nonneg (1/4:ℝ)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by norm_num : (0:ℝ)≤1/4)] at hr
  calc
    _ ≤ Real.sqrt (∑ i, (a i)^2)/2 := by linarith
    _ ≤ finAvg (fun ξ : Fin n → Bool => |rowDifference χ p Y c y + rademacherSum a ξ|) :=
      shifted_rademacher_abs n a _
    _ = finAvg (fun ξ : Fin n → Bool => |finAvg (fun ρ : Fin n → Fin d =>
        finAvg (fun k : Fin (2*d) => rowDifference χ
          (refinedPositions p (fun i => halfDigit d hd (ξ i) (ρ i))) Y (2*d*c+k.val) y))|) := by
      apply finAvg_congr
      intro ξ
      exact congrArg abs (half_averaged_child_difference d hd χ p Y c y ξ).symm
    _ ≤ finAvg (fun ξ : Fin n → Bool => finAvg (fun ρ : Fin n → Fin d =>
        |finAvg (fun k : Fin (2*d) => rowDifference χ
          (refinedPositions p (fun i => halfDigit d hd (ξ i) (ρ i))) Y (2*d*c+k.val) y)|)) :=
      finAvg_mono (fun _ => abs_finAvg_le _)
    _ = _ := (halfDigits_finAvg d hd (fun r : Fin n → Fin (2*d) =>
      |finAvg (fun k : Fin (2*d) => rowDifference χ (refinedPositions p r) Y (2*d*c+k.val) y)|)).symm

end
end Oscillation
