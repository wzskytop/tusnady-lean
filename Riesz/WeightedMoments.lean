import Riesz.ProfileLaw

namespace Riesz.Moments

open scoped BigOperators

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

noncomputable def productLaw (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) : FiniteLaw (Ω × Γ) where
  weight ω := μ.weight ω.1 * ν.weight ω.2
  nonneg ω := mul_nonneg (μ.nonneg ω.1) (ν.nonneg ω.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.total, mul_one]
    exact μ.total

lemma expectation_add (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    expectation μ (fun ω ↦ X ω + Y ω) = expectation μ X + expectation μ Y := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_const_mul (μ : FiniteLaw Ω) (a : ℝ) (X : Ω → ℝ) :
    expectation μ (fun ω ↦ a * X ω) = a * expectation μ X := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma expectation_product_mul (μ : FiniteLaw Ω) (ν : FiniteLaw Γ)
    (X : Ω → ℝ) (Y : Γ → ℝ) :
    expectation (productLaw μ ν) (fun ω ↦ X ω.1 * Y ω.2) =
      expectation μ X * expectation ν Y := by
  simp only [expectation, productLaw, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  ring

lemma expectation_product_left (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (X : Ω → ℝ) :
    expectation (productLaw μ ν) (fun ω ↦ X ω.1) = expectation μ X := by
  simpa using expectation_product_mul μ ν X (fun _ ↦ 1)

lemma expectation_product_right (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (Y : Γ → ℝ) :
    expectation (productLaw μ ν) (fun ω ↦ Y ω.2) = expectation ν Y := by
  simpa using expectation_product_mul μ ν (fun _ ↦ 1) Y

lemma product_sum_mean (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (X : Ω → ℝ) (Y : Γ → ℝ) :
    expectation (productLaw μ ν) (fun ω ↦ X ω.1 + Y ω.2) =
      expectation μ X + expectation ν Y := by
  rw [expectation_add, expectation_product_left, expectation_product_right]

lemma product_sum_second (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (X : Ω → ℝ) (Y : Γ → ℝ)
    (hX : expectation μ X = 0) (hY : expectation ν Y = 0) :
    expectation (productLaw μ ν) (fun ω ↦ (X ω.1 + Y ω.2) ^ 2) =
      expectation μ (fun ω ↦ X ω ^ 2) + expectation ν (fun ω ↦ Y ω ^ 2) := by
  have hf : (fun ω : Ω × Γ ↦ (X ω.1 + Y ω.2) ^ 2) =
      (fun ω ↦ X ω.1 ^ 2 + 2 * (X ω.1 * Y ω.2) + Y ω.2 ^ 2) := by
    funext ω
    ring
  rw [hf]
  simp only [expectation_add, expectation_const_mul, expectation_product_mul,
    hX, hY, mul_zero, add_zero]
  rw [expectation_product_left μ ν (fun ω ↦ X ω ^ 2),
    expectation_product_right μ ν (fun ω ↦ Y ω ^ 2)]

lemma product_sum_fourth (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (X : Ω → ℝ) (Y : Γ → ℝ)
    (hX : expectation μ X = 0) (hY : expectation ν Y = 0) :
    expectation (productLaw μ ν) (fun ω ↦ (X ω.1 + Y ω.2) ^ 4) =
      expectation μ (fun ω ↦ X ω ^ 4) +
      6 * (expectation μ (fun ω ↦ X ω ^ 2) * expectation ν (fun ω ↦ Y ω ^ 2)) +
      expectation ν (fun ω ↦ Y ω ^ 4) := by
  have hf : (fun ω : Ω × Γ ↦ (X ω.1 + Y ω.2) ^ 4) =
      (fun ω ↦ X ω.1 ^ 4 + 4 * (X ω.1 ^ 3 * Y ω.2) +
        6 * (X ω.1 ^ 2 * Y ω.2 ^ 2) + 4 * (X ω.1 * Y ω.2 ^ 3) + Y ω.2 ^ 4) := by
    funext ω
    ring
  rw [hf]
  simp only [expectation_add, expectation_const_mul]
  rw [expectation_product_left μ ν (fun ω ↦ X ω ^ 4),
    expectation_product_right μ ν (fun ω ↦ Y ω ^ 4),
    expectation_product_mul μ ν (fun ω ↦ X ω ^ 3) Y,
    expectation_product_mul μ ν (fun ω ↦ X ω ^ 2) (fun ω ↦ Y ω ^ 2),
    expectation_product_mul μ ν X (fun ω ↦ Y ω ^ 3)]
  simp only [hX, hY, mul_zero, zero_mul, add_zero]

/-- Independent centered variables satisfying the fourth-moment bound retain
it under addition. Independence here is implemented by the actual product law. -/
theorem product_sum_fourth_le (μ : FiniteLaw Ω) (ν : FiniteLaw Γ)
    (X : Ω → ℝ) (Y : Γ → ℝ)
    (hX : expectation μ X = 0) (hY : expectation ν Y = 0)
    (hX4 : expectation μ (fun ω ↦ X ω ^ 4) ≤
      4 * (expectation μ (fun ω ↦ X ω ^ 2)) ^ 2)
    (hY4 : expectation ν (fun ω ↦ Y ω ^ 4) ≤
      4 * (expectation ν (fun ω ↦ Y ω ^ 2)) ^ 2) :
    expectation (productLaw μ ν) (fun ω ↦ (X ω.1 + Y ω.2) ^ 4) ≤
      4 * (expectation (productLaw μ ν) (fun ω ↦ (X ω.1 + Y ω.2) ^ 2)) ^ 2 := by
  rw [product_sum_fourth μ ν X Y hX hY, product_sum_second μ ν X Y hX hY]
  have hx2 := expectation_nonneg μ (fun ω ↦ sq_nonneg (X ω))
  have hy2 := expectation_nonneg ν (fun ω ↦ sq_nonneg (Y ω))
  nlinarith [mul_nonneg hx2 hy2]

lemma weighted_fourth_le (μ : FiniteLaw Ω) (X : Ω → ℝ) (a : ℝ)
    (h4 : expectation μ (fun ω ↦ X ω ^ 4) ≤
      4 * (expectation μ (fun ω ↦ X ω ^ 2)) ^ 2) :
    expectation μ (fun ω ↦ (a * X ω) ^ 4) ≤
      4 * (expectation μ (fun ω ↦ (a * X ω) ^ 2)) ^ 2 := by
  simp only [mul_pow, expectation_const_mul]
  have hh := mul_le_mul_of_nonneg_left h4 (pow_nonneg (sq_nonneg a) 2)
  nlinarith

universe u

/-- The sample space of `n` genuinely independent draws, built as an iterated product. -/
def SampleSpace (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => SampleSpace Ω n × Ω

instance sampleSpaceFintype (Ω : Type*) [Fintype Ω] (n : ℕ) :
    Fintype (SampleSpace Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact @instFintypeProd _ _ ih inferInstance

noncomputable def independentLaw (μ : FiniteLaw Ω) : (n : ℕ) → FiniteLaw (SampleSpace Ω n)
  | 0 => { weight := fun _ => 1, nonneg := fun _ => by norm_num, total := by change (∑ _ : PUnit, (1 : ℝ)) = 1; simp }
  | n + 1 => productLaw (independentLaw μ n) μ

/-- The sum of deterministic weights times independent copies of `W`. -/
noncomputable def weightedSum (W : Ω → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → SampleSpace Ω n → ℝ
  | 0, _, _ => 0
  | n + 1, a, ω => weightedSum W n (fun i => a i.castSucc) ω.1 + a (Fin.last n) * W ω.2

lemma weightedSum_centered (μ : FiniteLaw Ω) (W : Ω → ℝ)
    (hmean : expectation μ W = 0) (n : ℕ) (a : Fin n → ℝ) :
    expectation (independentLaw μ n) (weightedSum W n a) = 0 := by
  induction n with
  | zero => simp [weightedSum]
  | succ n ih =>
    change expectation (productLaw (independentLaw μ n) μ)
      (fun ω => weightedSum W n (fun i => a i.castSucc) ω.1 + a (Fin.last n) * W ω.2) = 0
    rw [product_sum_mean (independentLaw μ n) μ
      (weightedSum W n (fun i => a i.castSucc)) (fun ω => a (Fin.last n) * W ω),
      ih, expectation_const_mul, hmean]
    ring

lemma weightedSum_second (μ : FiniteLaw Ω) (W : Ω → ℝ)
    (hmean : expectation μ W = 0) (n : ℕ) (a : Fin n → ℝ) :
    expectation (independentLaw μ n) (fun ω => weightedSum W n a ω ^ 2) =
      expectation μ (fun ω => W ω ^ 2) * ∑ i, a i ^ 2 := by
  induction n with
  | zero => simp [weightedSum]
  | succ n ih =>
    change expectation (productLaw (independentLaw μ n) μ)
      (fun ω => (weightedSum W n (fun i => a i.castSucc) ω.1 + a (Fin.last n) * W ω.2) ^ 2) = _
    rw [product_sum_second (independentLaw μ n) μ
      (weightedSum W n (fun i => a i.castSucc)) (fun ω => a (Fin.last n) * W ω)
      (weightedSum_centered μ W hmean n _)]
    · rw [ih, Fin.sum_univ_castSucc]
      simp only [mul_pow, expectation_const_mul]
      ring
    · rw [expectation_const_mul, hmean, mul_zero]

theorem weightedSum_fourth_le (μ : FiniteLaw Ω) (W : Ω → ℝ)
    (hmean : expectation μ W = 0)
    (hfourth : expectation μ (fun ω => W ω ^ 4) ≤
      4 * (expectation μ (fun ω => W ω ^ 2)) ^ 2) (n : ℕ) (a : Fin n → ℝ) :
    expectation (independentLaw μ n) (fun ω => weightedSum W n a ω ^ 4) ≤
      4 * (expectation (independentLaw μ n) (fun ω => weightedSum W n a ω ^ 2)) ^ 2 := by
  induction n with
  | zero => simp [weightedSum]
  | succ n ih =>
    exact product_sum_fourth_le (independentLaw μ n) μ
      (weightedSum W n (fun i => a i.castSucc)) (fun ω => a (Fin.last n) * W ω)
      (weightedSum_centered μ W hmean n _) (by rw [expectation_const_mul, hmean, mul_zero])
      (ih _) (weighted_fourth_le μ W _ hfourth)

/-- Each good coefficient contributes at least `1 / C²` to the squared-weight sum. -/
lemma squared_weights_lower (n : ℕ) (a : Fin n → ℝ) (good : Finset (Fin n))
    (C : ℝ) (hC : 0 < C) (hgood : ∀ i ∈ good, 1 / C ≤ |a i|) :
    (good.card : ℝ) / C ^ 2 ≤ ∑ i, a i ^ 2 := by
  have hi (i : Fin n) (hig : i ∈ good) : 1 / C ^ 2 ≤ a i ^ 2 := by
    have hh := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1 / C) (abs_nonneg (a i))).mpr
      (hgood i hig)
    simpa only [one_div_pow, sq_abs] using hh
  calc
    (good.card : ℝ) / C ^ 2 = ∑ _i ∈ good, (1 : ℝ) / C ^ 2 := by simp [div_eq_mul_inv]
    _ ≤ ∑ i ∈ good, a i ^ 2 := Finset.sum_le_sum hi
    _ ≤ ∑ i, a i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      (fun i _ _ => sq_nonneg (a i))

theorem weightedSum_variance_lower (μ : FiniteLaw Ω) (W : Ω → ℝ)
    (hmean : expectation μ W = 0)
    (hvariance : 1 / 64 ≤ expectation μ (fun ω => W ω ^ 2))
    (n : ℕ) (a : Fin n → ℝ) (good : Finset (Fin n)) (C : ℝ) (hC : 0 < C)
    (hgood : ∀ i ∈ good, 1 / C ≤ |a i|) :
    (good.card : ℝ) / (64 * C ^ 2) ≤
      expectation (independentLaw μ n) (fun ω => weightedSum W n a ω ^ 2) := by
  rw [weightedSum_second μ W hmean]
  have hs := squared_weights_lower n a good C hC hgood
  have hsn : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (a i))
  calc
    (good.card : ℝ) / (64 * C ^ 2) = (1 / 64 : ℝ) * ((good.card : ℝ) / C ^ 2) := by ring
    _ ≤ (1 / 64 : ℝ) * ∑ i, a i ^ 2 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ expectation μ (fun ω => W ω ^ 2) * ∑ i, a i ^ 2 :=
      mul_le_mul_of_nonneg_right hvariance hsn

/-- The manuscript's one-rectangle Laplace bound for actual independent copies
of a finite profile law.  The moment conclusions are derived from independence. -/
theorem independent_sum_laplace (μ : FiniteLaw Ω) (W : Ω → ℝ)
    (hmean : expectation μ W = 0)
    (hvariance : 1 / 64 ≤ expectation μ (fun ω => W ω ^ 2))
    (hfourth : expectation μ (fun ω => W ω ^ 4) ≤
      4 * (expectation μ (fun ω => W ω ^ 2)) ^ 2)
    (n : ℕ) (a : Fin n → ℝ) (good : Finset (Fin n)) (C lam b : ℝ)
    (hC : 20 < C) (hlam : 1 ≤ lam) (hb : 0 < b)
    (hbC : b ≤ 1 / (512 * C ^ (3 / 2 : ℝ)))
    (hgood : ∀ i ∈ good, 1 / C ≤ |a i|) (hcount : (good.card : ℝ) / lam ≤ C) :
    expectation (independentLaw μ n) (fun ω => Real.exp (-|weightedSum W n a ω| / Real.sqrt lam)) ≤
      Real.exp (-b * (good.card : ℝ) / lam) := by
  apply one_rectangle_laplace (independentLaw μ n) (weightedSum W n a)
    (expectation (independentLaw μ n) (fun ω => weightedSum W n a ω ^ 2)) lam C
    (good.card : ℝ) b hlam hC (Nat.cast_nonneg _) hcount hb hbC rfl
    (weightedSum_fourth_le μ W hmean hfourth n a)
  exact weightedSum_variance_lower μ W hmean hvariance n a good C (by linarith) hgood

/-- Specialization to the actual dyadic profile whose values are cell averages
of the continuous profile, as verified in `Dyadic.lean` and `ProfileLaw.lean`. -/
theorem dyadic_profile_sum_laplace (m : ℕ) (hm : 0 < m)
    (n : ℕ) (a : Fin n → ℝ) (good : Finset (Fin n)) (C lam b : ℝ)
    (hC : 20 < C) (hlam : 1 ≤ lam) (hb : 0 < b)
    (hbC : b ≤ 1 / (512 * C ^ (3 / 2 : ℝ)))
    (hgood : ∀ i ∈ good, 1 / C ≤ |a i|) (hcount : (good.card : ℝ) / lam ≤ C) :
    expectation (independentLaw (profileLaw m hm) n)
      (fun ω => Real.exp (-|weightedSum (profileValue m) n a ω| / Real.sqrt lam)) ≤
      Real.exp (-b * (good.card : ℝ) / lam) :=
  independent_sum_laplace (profileLaw m hm) (profileValue m)
    (profileLaw_centered hm) (profileLaw_variance_lower hm) (profileLaw_fourth_moment hm)
    n a good C lam b hC hlam hb hbC hgood hcount

end Riesz.Moments
