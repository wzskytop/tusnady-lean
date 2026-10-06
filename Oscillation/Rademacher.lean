import Oscillation.FiniteAverage
import Riesz.FiniteProducts

/-! A finite, shifted Khintchine bound derived from genuine product moments. -/
namespace Oscillation
noncomputable section
open scoped BigOperators
open Riesz.Moments
set_option maxHeartbeats 1000000

def boolSign (x : Bool) : ℝ := if x then 1 else -1

def boolLaw : FiniteLaw Bool where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  total := by norm_num

def rademacherSum {n : ℕ} (a : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, a i * boolSign (x i)

lemma bool_product_expectation (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    expectation (independentLaw boolLaw n)
      (fun x ↦ f (sampleSpaceEquiv Bool n x)) = finAvg f := by
  rw [expectation_independentLaw_vector boolLaw (1 / 2) (fun _ ↦ rfl)]
  simp only [finAvg, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, one_div_pow]
  ring

lemma rademacher_second (n : ℕ) (a : Fin n → ℝ) :
    finAvg (fun x ↦ rademacherSum a x ^ 2) = ∑ i, a i ^ 2 := by
  rw [← bool_product_expectation]
  simp only [rademacherSum, ← weightedSum_eq_vector_sum]
  rw [weightedSum_second boolLaw boolSign (by norm_num [expectation, boolLaw, boolSign])]
  norm_num [expectation, boolLaw, boolSign]

lemma rademacher_fourth (n : ℕ) (a : Fin n → ℝ) :
    finAvg (fun x ↦ rademacherSum a x ^ 4) ≤ 4 * (∑ i, a i ^ 2) ^ 2 := by
  rw [← rademacher_second n a, ← bool_product_expectation, ← bool_product_expectation]
  simp only [rademacherSum, ← weightedSum_eq_vector_sum]
  exact weightedSum_fourth_le boolLaw boolSign
    (by norm_num [expectation, boolLaw, boolSign])
    (by norm_num [expectation, boolLaw, boolSign]) n a

lemma abs_mean_of_fourth {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (X : Ω → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hsecond : expectation μ (fun x ↦ X x ^ 2) = v)
    (hfourth : expectation μ (fun x ↦ X x ^ 4) ≤ 4 * v ^ 2) :
    Real.sqrt v / 2 ≤ expectation μ (fun x ↦ |X x|) := by
  let A := expectation μ (fun x ↦ |X x|)
  let B := expectation μ (fun x ↦ |X x| ^ 3)
  have hA : 0 ≤ A := expectation_nonneg μ (fun _ ↦ abs_nonneg _)
  have hB : 0 ≤ B := expectation_nonneg μ (fun _ ↦ by positivity)
  have hcs₁ : v ^ 2 ≤ A * B := by
    rw [← hsecond]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun x _ ↦ mul_nonneg (μ.nonneg x) (abs_nonneg _))
      (fun x _ ↦ mul_nonneg (μ.nonneg x) (by positivity))
    intro x _
    rcases le_total 0 (X x) with hx | hx
    · simp only [abs_of_nonneg hx]; exact le_of_eq (by ring)
    · simp only [abs_of_nonpos hx]; exact le_of_eq (by ring)
  have hcs₂ : B ^ 2 ≤ v * (4 * v ^ 2) := by
    have hc : B ^ 2 ≤ expectation μ (fun x ↦ X x ^ 2) *
        expectation μ (fun x ↦ X x ^ 4) := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (fun x _ ↦ mul_nonneg (μ.nonneg x) (sq_nonneg _))
        (fun x _ ↦ mul_nonneg (μ.nonneg x) (by positivity))
      intro x _
      rcases le_total 0 (X x) with hx | hx
      · simp only [abs_of_nonneg hx]; exact le_of_eq (by ring)
      · simp only [abs_of_nonpos hx]; exact le_of_eq (by ring)
    rw [hsecond] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hfourth hv)
  have hs := Real.sq_sqrt hv
  have hroot := Real.sqrt_nonneg v
  by_cases hv0 : v = 0
  · simpa [hv0] using hA
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have hsq : v ^ 4 ≤ A ^ 2 * B ^ 2 := by
    nlinarith [sq_nonneg (A * B - v ^ 2)]
  have hmul := mul_le_mul_of_nonneg_left hcs₂ (sq_nonneg A)
  have hrel : v ≤ 4 * A ^ 2 := by
    have hv3 : 0 < v ^ 3 := by positivity
    apply (mul_le_mul_iff_left₀ hv3).mp
    nlinarith [hsq, hmul]
  change Real.sqrt v / 2 ≤ A
  nlinarith

lemma rademacher_abs (n : ℕ) (a : Fin n → ℝ) :
    Real.sqrt (∑ i, a i ^ 2) / 2 ≤ finAvg (fun x ↦ |rademacherSum a x|) := by
  let μ := independentLaw boolLaw n
  have he (f : (Fin n → Bool) → ℝ) := bool_product_expectation n f
  have hs := rademacher_second n a
  have hf := rademacher_fourth n a
  rw [← he] at hs hf ⊢
  exact abs_mean_of_fourth μ _ _ (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)) hs hf

lemma rademacher_negate {n : ℕ} (a : Fin n → ℝ) (x : Fin n → Bool) :
    rademacherSum a (fun i ↦ !(x i)) = -rademacherSum a x := by
  simp only [rademacherSum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolSign]

lemma shifted_rademacher_abs (n : ℕ) (a : Fin n → ℝ) (d : ℝ) :
    Real.sqrt (∑ i, a i ^ 2) / 2 ≤
      finAvg (fun x ↦ |d + rademacherSum a x|) := by
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun x i ↦ !(x i)
      invFun := fun x i ↦ !(x i)
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp }
  have he := finAvg_equiv e (fun x ↦ |d + rademacherSum a x|)
  change finAvg (fun x : Fin n → Bool ↦ |d + rademacherSum a (fun i ↦ !(x i))|) =
    finAvg (fun x : Fin n → Bool ↦ |d + rademacherSum a x|) at he
  simp only [rademacher_negate, ← sub_eq_add_neg] at he
  have hh : finAvg (fun x ↦ 2 * |rademacherSum a x|) ≤
      finAvg (fun x ↦ |d + rademacherSum a x| + |d - rademacherSum a x|) := by
    apply finAvg_mono
    intro x
    have ht := abs_sub (d + rademacherSum a x) (d - rademacherSum a x)
    have hid : d + rademacherSum a x - (d - rademacherSum a x) =
        2 * rademacherSum a x := by ring
    rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    exact ht
  rw [finAvg_const_mul, finAvg_add, he] at hh
  exact (rademacher_abs n a).trans (by linarith)

end
end Oscillation
