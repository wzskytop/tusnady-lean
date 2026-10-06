import Riesz.UniformGrid
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Conditional fresh blocks for independent real samples

The coarse cells are the actual grid cells of all sample coordinates. The
product identities derive conditional independence from the product measure;
no independence between different shape levels is assumed.
-/

namespace Riesz
noncomputable section
open MeasureTheory PointSets Occupancy
open scoped ENNReal

/-- Normalized averages of coordinate products factor over the actual product
partition, including zero-measure fibers. -/
theorem fiberMean_pi_product {ι α κ : Type*} [Fintype ι]
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p : α → κ) (f : ι → α → ℝ) (x : ι → α) :
    fiberMean (Measure.pi (fun _ : ι => μ)) (fun y i => p (y i))
      (fun y => ∏ i, f i (y i)) x = ∏ i, fiberMean μ p (f i) (x i) := by
  have hcell : (fun y : ι → α => fun i => p (y i)) ⁻¹' {fun i => p (x i)} =
      Set.univ.pi (fun i => p ⁻¹' {p (x i)}) := by
    ext y
    simp [funext_iff]
  unfold fiberMean
  rw [hcell, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod,
    Measure.pi_pi, ENNReal.toReal_prod, Finset.prod_div_distrib]

/-- The information in the first `k` horizontal cells for every sample point. -/
def sampleGridIndex (n k : ℕ) (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i => gridIndex k (x i)

abbrev sampleGridSigma (n k : ℕ) : MeasurableSpace (Fin n → ℝ) :=
  (inferInstance : MeasurableSpace (Fin n → ℤ)).comap (sampleGridIndex n k)

lemma measurable_sampleGridIndex (n k : ℕ) : Measurable (sampleGridIndex n k) := by
  exact measurable_pi_iff.mpr (fun i => (measurable_gridIndex k).comp (measurable_pi_apply i))

/-- A product of functions of fresh blocks has the product of their uniform
averages, even after every coarse sample cell has been revealed. -/
theorem condExp_freshGrid_product (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (f : Fin n → Fin m → ℝ) :
    (Measure.pi (fun _ : Fin n => μI))[
      (fun x => ∏ i, f i (freshGridIndex k m hm (x i))) | sampleGridSigma n k] =ᵐ[
        Measure.pi (fun _ : Fin n => μI)] (fun _ => ∏ i, (∑ a, f i a) / m) := by
  let μ := Measure.pi (fun _ : Fin n => μI)
  have hf (i : Fin n) : Integrable (fun x => f i (freshGridIndex k m hm x)) μI :=
    integrable_freshGridFunction k m hm (f i)
  have hi (i : Fin n) : ∀ᵐ x ∂μI,
      fiberMean μI (gridIndex k) (fun y => f i (freshGridIndex k m hm y)) x =
        (∑ a, f i a) / m :=
    (condExp_ae_eq_fiberMean (measurable_gridIndex k) (hf i)).symm.trans
      (condExp_freshGridIndex k m hk hm (f i))
  have hiall : ∀ᵐ x ∂μ, ∀ i : Fin n,
      fiberMean μI (gridIndex k) (fun y => f i (freshGridIndex k m hm y)) (x i) =
        (∑ a, f i a) / m := by
    apply ae_all_iff.mpr
    intro i
    exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μI) (i := i) (hi i)
  have hcond := condExp_ae_eq_fiberMean (μ := μ) (measurable_sampleGridIndex n k)
    (Integrable.fintype_prod hf)
  filter_upwards [hcond, hiall] with x hx hxi
  rw [hx]
  change fiberMean μ (fun y i => gridIndex k (y i))
    (fun y => ∏ i, f i (freshGridIndex k m hm (y i))) x = _
  rw [fiberMean_pi_product μI (gridIndex k) (fun i y => f i (freshGridIndex k m hm y)) x]
  exact Finset.prod_congr rfl (fun i _ => hxi i)

lemma finiteFunction_delta_expansion {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α]
    (H : (ι → α) → ℝ) (a : ι → α) :
    H a = ∑ b : ι → α, H b * ∏ i, (if a i = b i then (1 : ℝ) else 0) := by
  classical
  have hb (b : ι → α) : (∏ i, (if a i = b i then (1 : ℝ) else 0)) =
      if a = b then 1 else 0 := by
    simp only [Fintype.prod_boole, ← funext_iff]
  simp_rw [hb, mul_ite, mul_one, mul_zero]
  simp

/-- An arbitrary statistic of all fresh digit blocks has the uniform product
law conditionally on all old blocks. This is stronger than pairwise independence. -/
theorem condExp_freshGrid_vector (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (H : (Fin n → Fin m) → ℝ) :
    (Measure.pi (fun _ : Fin n => μI))[
      (fun x => H (fun i => freshGridIndex k m hm (x i))) | sampleGridSigma n k] =ᵐ[
        Measure.pi (fun _ : Fin n => μI)] (fun _ => (∑ a, H a) / (m : ℝ) ^ n) := by
  classical
  let μ := Measure.pi (fun _ : Fin n => μI)
  let δ : (Fin n → Fin m) → (Fin n → ℝ) → ℝ := fun b x =>
    ∏ i, if freshGridIndex k m hm (x i) = b i then 1 else 0
  have hδ (b : Fin n → Fin m) : Integrable (δ b) μ :=
    Integrable.fintype_prod (fun i =>
      integrable_freshGridFunction k m hm (fun a => if a = b i then 1 else 0))
  have hmean (b : Fin n → Fin m) : μ[δ b | sampleGridSigma n k] =ᵐ[μ]
      (fun _ => 1 / (m : ℝ) ^ n) := by
    have h := condExp_freshGrid_product n k m hk hm
      (fun i a => if a = b i then 1 else 0)
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, one_div_pow] using h
  have hscaled (b : Fin n → Fin m) :
      μ[(fun x => H b * δ b x) | sampleGridSigma n k] =ᵐ[μ]
        (fun _ => H b / (m : ℝ) ^ n) := by
    have hsm := condExp_smul (μ := μ) (H b) (δ b) (sampleGridSigma n k)
    filter_upwards [hsm, hmean b] with x hx hy
    change μ[H b • δ b | sampleGridSigma n k] x = _
    simpa only [Pi.smul_apply, smul_eq_mul, hy, mul_one_div] using hx
  have heq : (fun x => H (fun i => freshGridIndex k m hm (x i))) =
      ∑ b : Fin n → Fin m, (fun x => H b * δ b x) := by
    funext x
    simpa only [Finset.sum_apply, δ] using
      finiteFunction_delta_expansion H (fun i => freshGridIndex k m hm (x i))
  rw [heq]
  have hsum := condExp_finsetSum (μ := μ)
    (s := Finset.univ) (fun b _ => (hδ b).const_mul (H b)) (sampleGridSigma n k)
  filter_upwards [hsum, ae_all_iff.mpr hscaled] with x hx hxs
  simp only [Finset.sum_apply] at hx
  rw [hx]
  simp_rw [hxs]
  rw [Finset.sum_div]


/-- The vector of freshly exposed block indices. -/
def sampleFreshIndex (n k m : ℕ) (hm : 0 < m) (x : Fin n → ℝ) : Fin n → Fin m :=
  fun i => freshGridIndex k m hm (x i)

lemma measurable_sampleFreshIndex (n k m : ℕ) (hm : 0 < m) :
    Measurable (sampleFreshIndex n k m hm) := by
  exact measurable_pi_iff.mpr
    (fun i => (measurable_freshGridIndex k m hm).comp (measurable_pi_apply i))

lemma integrable_sampleFreshFunction (n k m : ℕ) (hm : 0 < m)
    (H : (Fin n → Fin m) → ℝ) :
    Integrable (fun x => H (sampleFreshIndex n k m hm x)) (Measure.pi (fun _ : Fin n => μI)) := by
  apply Integrable.of_bound
    ((measurable_of_countable H).comp (measurable_sampleFreshIndex n k m hm)).aestronglyMeasurable
    (∑ a, |H a|)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun a _ => abs_nonneg (H a)) (Finset.mem_univ _)

/-- The statistic may depend arbitrarily on the revealed coarse sample cells.
Its fresh variables still have the uniform product law in each such cell. -/
theorem condExp_freshGrid_with_past (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (H : (Fin n → ℤ) → (Fin n → Fin m) → ℝ)
    (hH : Integrable (fun x => H (sampleGridIndex n k x) (sampleFreshIndex n k m hm x))
      (Measure.pi (fun _ : Fin n => μI))) :
    (Measure.pi (fun _ : Fin n => μI))[
      (fun x => H (sampleGridIndex n k x) (sampleFreshIndex n k m hm x)) | sampleGridSigma n k] =ᵐ[
        Measure.pi (fun _ : Fin n => μI)]
      (fun x => (∑ a, H (sampleGridIndex n k x) a) / (m : ℝ) ^ n) := by
  let μ := Measure.pi (fun _ : Fin n => μI)
  let p := sampleGridIndex n k
  let q := sampleFreshIndex n k m hm
  have hp : Measurable p := measurable_sampleGridIndex n k
  have hf (b : Fin n → ℤ) : Integrable (fun x => H b (q x)) μ :=
    integrable_sampleFreshFunction n k m hm (H b)
  have hfixed (b : Fin n → ℤ) : ∀ᵐ x ∂μ,
      fiberMean μ p (fun y => H b (q y)) x = (∑ a, H b a) / (m : ℝ) ^ n :=
    (condExp_ae_eq_fiberMean hp (hf b)).symm.trans
      (condExp_freshGrid_vector n k m hk hm (H b))
  have hbase := condExp_ae_eq_fiberMean hp hH
  filter_upwards [hbase, ae_all_iff.mpr hfixed] with x hx hxf
  rw [hx]
  change fiberMean μ p (fun y => H (p y) (q y)) x = _
  calc
    fiberMean μ p (fun y => H (p y) (q y)) x =
        fiberMean μ p (fun y => H (p x) (q y)) x := by
      unfold fiberMean
      congr 1
      apply setIntegral_congr_fun (hp (measurableSet_singleton _))
      intro y hy
      change p y = p x at hy
      change H (p y) (q y) = H (p x) (q y)
      rw [hy]
    _ = _ := hxf (p x)


lemma sampleGridSigma_le_mul (n k m : ℕ) (hm : 0 < m) :
    sampleGridSigma n k ≤ sampleGridSigma n (k * m) := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun b : Fin n → ℤ => fun i => b i / (m : ℤ)) (measurable_of_countable _)
  funext x i
  exact (gridIndex_mul_ediv k m hm (x i)).symm

lemma sampleGridIndex_grid_measurable (n k : ℕ) :
    Measurable[sampleGridSigma n k] (sampleGridIndex n k) :=
  Measurable.of_comap_le le_rfl

lemma sampleFreshIndex_grid_measurable (n k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    Measurable[sampleGridSigma n (k * m)] (sampleFreshIndex n k m hm) := by
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  let g : ℤ → Fin m := fun z => ⟨(z % (m : ℤ)).toNat, by
    have hlo := Int.emod_nonneg z hmz.ne'
    have hhi := Int.emod_lt_of_pos z hmz
    omega⟩
  have heq : sampleFreshIndex n k m hm =
      fun x i => g (sampleGridIndex n (k * m) x i) := by
    funext x i
    apply Fin.ext
    have hi := freshGridIndex_eq_emod k m hk hm (x i)
    change (freshGridIndex k m hm (x i) : ℕ) = (gridIndex (k * m) (x i) % (m : ℤ)).toNat
    omega
  rw [heq]
  let : MeasurableSpace (Fin n → ℝ) := sampleGridSigma n (k * m)
  exact measurable_pi_iff.mpr (fun i => (measurable_of_countable g).comp
    ((measurable_pi_apply i).comp (sampleGridIndex_grid_measurable n (k * m))))

/-- Both past-dependent coefficients and the fresh block are known at the next
sample grid. This provides the adaptedness required by the iteration lemma. -/
theorem freshGrid_statistic_grid_measurable (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (H : (Fin n → ℤ) → (Fin n → Fin m) → ℝ) :
    Measurable[sampleGridSigma n (k * m)]
      (fun x => H (sampleGridIndex n k x) (sampleFreshIndex n k m hm x)) := by
  have hp : Measurable[sampleGridSigma n (k * m)] (sampleGridIndex n k) :=
    (sampleGridIndex_grid_measurable n k).mono (sampleGridSigma_le_mul n k m hm) le_rfl
  exact (measurable_of_countable (fun z : (Fin n → ℤ) × (Fin n → Fin m) => H z.1 z.2)).comp
    (hp.prodMk (sampleFreshIndex_grid_measurable n k m hk hm))


end
end Riesz
