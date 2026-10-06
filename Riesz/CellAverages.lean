import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor
import Riesz.PointSets

/-!
# Cell averages as conditional expectations

A countable measurable cell index determines a partition sigma-algebra.  On
each positive-measure fiber, conditional expectation is exactly the integral
over that fiber divided by its measure. Null fibers are removed only on an
explicit almost-everywhere set; no positivity assumption is made on all cells.
-/

open MeasureTheory
open scoped ENNReal

namespace Riesz

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {mι : MeasurableSpace ι}
  {μ : Measure Ω} {p : Ω → ι} {f : Ω → ℝ}

/-- The normalized integral over the cell containing a point. -/
noncomputable def fiberMean (μ : Measure Ω) (p : Ω → ι) (f : Ω → ℝ) (x : Ω) : ℝ :=
  (∫ y in p ⁻¹' {p x}, f y ∂μ) / (μ (p ⁻¹' {p x})).toReal

/-- A function measurable for the cell-index sigma-algebra is constant on
each fiber, as an exact pointwise statement. -/
theorem measurable_comap_eq_of_index_eq {g : Ω → ℝ}
    (hg : Measurable[mι.comap p] g) {x y : Ω} (hxy : p x = p y) : g x = g y := by
  obtain ⟨s, _, hs⟩ := hg (measurableSet_singleton (g x))
  have hx : p x ∈ s := by
    have hx' : x ∈ g ⁻¹' {g x} := rfl
    rw [← hs] at hx'
    exact hx'
  have hy : y ∈ g ⁻¹' {g x} := by
    rw [← hs]
    change p y ∈ s
    rwa [← hxy]
  exact hy.symm

/-- The conditional expectation has the cell-average value at every point
whose fiber has positive measure. -/
theorem condExp_eq_fiberMean_of_measure_ne_zero [IsFiniteMeasure μ]
    [MeasurableSingletonClass ι] (hp : Measurable p) (hf : Integrable f μ)
    (x : Ω) (hcell : μ (p ⁻¹' {p x}) ≠ 0) :
    (μ[f | mι.comap p]) x = fiberMean μ p f x := by
  have hs : MeasurableSet (p ⁻¹' {p x}) := hp (measurableSet_singleton _)
  have hsc : MeasurableSet[mι.comap p] (p ⁻¹' {p x}) :=
    ⟨{p x}, measurableSet_singleton _, rfl⟩
  have hconstant : ∫ y in p ⁻¹' {p x}, (μ[f | mι.comap p]) y ∂μ =
      μ.real (p ⁻¹' {p x}) * (μ[f | mι.comap p]) x := by
    calc
      _ = ∫ _ in p ⁻¹' {p x}, (μ[f | mι.comap p]) x ∂μ := by
        apply setIntegral_congr_fun hs
        intro y hy
        exact measurable_comap_eq_of_index_eq stronglyMeasurable_condExp.measurable hy
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  have hμ : (μ (p ⁻¹' {p x})).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hcell, measure_ne_top _ _⟩
  apply (eq_div_iff hμ).mpr
  calc
    _ = ∫ y in p ⁻¹' {p x}, (μ[f | mι.comap p]) y ∂μ := by
      simpa [measureReal_def, mul_comm] using hconstant.symm
    _ = _ := setIntegral_condExp hp.comap_le hf hsc

/-- For a countable index, null fibers form a null set, even if some endpoints
or empty cells are assigned a separate index. -/
theorem ae_fiber_measure_ne_zero [Countable ι] :
    ∀ᵐ x ∂μ, μ (p ⁻¹' {p x}) ≠ 0 := by
  have hi (i : ι) : ∀ᵐ x ∂μ, p x = i → μ (p ⁻¹' {i}) ≠ 0 := by
    by_cases hz : μ (p ⁻¹' {i}) = 0
    · have havoid : ∀ᵐ x ∂μ, p x ≠ i := by
        simpa only [ae_iff, not_not, Set.preimage, Set.mem_singleton_iff] using hz
      filter_upwards [havoid] with x hx heq
      exact (hx heq).elim
    · exact Filter.Eventually.of_forall fun _ _ ↦ hz
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact hx (p x) rfl

/-- Conditional expectation for any countable measurable partition is the
normalized integral on its cells, with zero-measure cells handled a.e. -/
theorem condExp_ae_eq_fiberMean [IsFiniteMeasure μ] [Countable ι]
    [MeasurableSingletonClass ι] (hp : Measurable p) (hf : Integrable f μ) :
    μ[f | mι.comap p] =ᵐ[μ] fiberMean μ p f := by
  filter_upwards [ae_fiber_measure_ne_zero (μ := μ) (p := p)] with x hx
  exact condExp_eq_fiberMean_of_measure_ne_zero hp hf x hx

/-- The explicit average is measurable for the cell-index sigma-algebra. -/
theorem stronglyMeasurable_fiberMean [Countable ι] [MeasurableSingletonClass ι] :
    StronglyMeasurable[mι.comap p] (fiberMean μ p f) := by
  have hg : Measurable (fun i : ι ↦
      (∫ y in p ⁻¹' {i}, f y ∂μ) / (μ (p ⁻¹' {i})).toReal) :=
    measurable_of_countable _
  exact (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

theorem integrable_fiberMean [IsFiniteMeasure μ] [Countable ι]
    [MeasurableSingletonClass ι] (hp : Measurable p) (hf : Integrable f μ) :
    Integrable (fiberMean μ p f) μ :=
  integrable_condExp.congr (condExp_ae_eq_fiberMean hp hf)

/-- Vanishing integrals on cells imply zero conditional expectation; this
turns the local centering identities of the proof into conditional centering. -/
theorem condExp_ae_eq_zero_of_cell_integrals [IsFiniteMeasure μ] [Countable ι]
    [MeasurableSingletonClass ι] (hp : Measurable p) (hf : Integrable f μ)
    (hzero : ∀ i, ∫ y in p ⁻¹' {i}, f y ∂μ = 0) :
    μ[f | mι.comap p] =ᵐ[μ] 0 := by
  refine (condExp_ae_eq_fiberMean hp hf).trans ?_
  filter_upwards [] with x
  simp [fiberMean, hzero]

/-- Refining a cell partition and then averaging back recovers the coarse
cell averages. The premise concerns the sigma-algebras, not expectations. -/
theorem condExp_fiberMean_of_refinement {κ : Type*} {mκ : MeasurableSpace κ}
    {q : Ω → κ} [IsFiniteMeasure μ] [Countable ι] [Countable κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    (hp : Measurable p) (hq : Measurable q) (hf : Integrable f μ)
    (hrefines : mι.comap p ≤ mκ.comap q) :
    μ[fiberMean μ q f | mι.comap p] =ᵐ[μ] fiberMean μ p f := by
  exact (condExp_congr_ae (condExp_ae_eq_fiberMean hq hf).symm).trans
    ((condExp_condExp_of_le hrefines hq.comap_le).trans (condExp_ae_eq_fiberMean hp hf))

/-- Differences of nested cell averages have zero conditional mean at the
coarser level; this is the martingale-difference input to `Exponential.lean`. -/
theorem condExp_fiberMean_sub_of_refinement {κ : Type*} {mκ : MeasurableSpace κ}
    {q : Ω → κ} [IsFiniteMeasure μ] [Countable ι] [Countable κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    (hp : Measurable p) (hq : Measurable q) (hf : Integrable f μ)
    (hrefines : mι.comap p ≤ mκ.comap q) :
    μ[(fiberMean μ q f - fiberMean μ p f) | mι.comap p] =ᵐ[μ] 0 := by
  have hcoarse : μ[fiberMean μ p f | mι.comap p] = fiberMean μ p f :=
    condExp_of_stronglyMeasurable hp.comap_le stronglyMeasurable_fiberMean
      (integrable_fiberMean hp hf)
  refine (condExp_sub (integrable_fiberMean hq hf) (integrable_fiberMean hp hf) _).trans ?_
  filter_upwards [condExp_fiberMean_of_refinement hp hq hf hrefines] with x hx
  simp [Pi.sub_apply, hcoarse, hx]

end Riesz

namespace Riesz

open PointSets

/-- Right-closed grid cells. The point zero lies in a separate null fiber
under the uniform measure on the unit interval. -/
noncomputable def gridIndex (n : ℕ) (x : ℝ) : ℤ := ⌈(n : ℝ) * x⌉ - 1

def gridCell (n : ℕ) (k : ℤ) : Set ℝ :=
  Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)

noncomputable def gridMean (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  n * ∫ y in gridCell n (gridIndex n x), f y

noncomputable abbrev gridSigma (n : ℕ) : MeasurableSpace ℝ :=
  (inferInstance : MeasurableSpace ℤ).comap (gridIndex n)

theorem measurable_gridIndex (n : ℕ) : Measurable (gridIndex n) := by
  exact ((measurable_const.mul measurable_id).ceil.sub_const 1)

theorem gridIndex_fiber (n : ℕ) (hn : 0 < n) (k : ℤ) :
    gridIndex n ⁻¹' {k} = gridCell n k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, gridIndex, sub_eq_iff_eq_add,
    Int.ceil_eq_iff, Int.cast_add, Int.cast_one, add_sub_cancel_right,
    gridCell, Set.mem_Ioc, div_lt_iff₀ hn', le_div_iff₀ hn', mul_comm]

theorem gridCell_subset_unit (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : (0 : ℝ) ≤ k) (hkn : (k : ℝ) + 1 ≤ n) :
    gridCell n k ⊆ Set.Icc 0 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rintro x ⟨hx0, hx1⟩
  constructor
  · exact (div_nonneg hk hn'.le).trans hx0.le
  · exact hx1.trans ((div_le_one hn').mpr hkn)

theorem gridCell_measure (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : (0 : ℝ) ≤ k) (hkn : (k : ℝ) + 1 ≤ n) :
    μI (gridCell n k) = ENNReal.ofReal (1 / (n : ℝ)) := by
  rw [μI, Measure.restrict_eq_self _ (gridCell_subset_unit n hn k hk hkn),
    gridCell, Real.volume_Ioc]
  congr 1
  ring

theorem gridIndex_bounds (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Ioc 0 1) :
    (0 : ℝ) ≤ gridIndex n x ∧ (gridIndex n x : ℝ) + 1 ≤ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : (1 : ℤ) ≤ ⌈(n : ℝ) * x⌉ :=
    Int.one_le_ceil_iff.mpr (mul_pos hn' hx.1)
  have hhi : ⌈(n : ℝ) * x⌉ ≤ (n : ℤ) := by
    apply Int.ceil_le.mpr
    simpa using mul_le_of_le_one_right hn'.le hx.2
  constructor
  · exact_mod_cast (show (0 : ℤ) ≤ gridIndex n x by unfold gridIndex; omega)
  · have hhi' : (⌈(n : ℝ) * x⌉ : ℝ) ≤ n := by exact_mod_cast hhi
    simpa [gridIndex] using hhi'

theorem fiberMean_gridIndex_eq_gridMean (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Set.Ioc 0 1) :
    fiberMean μI (gridIndex n) f x = gridMean f n x := by
  obtain ⟨hk, hkn⟩ := gridIndex_bounds n hn hx
  have hsub := gridCell_subset_unit n hn (gridIndex n x) hk hkn
  unfold fiberMean gridMean
  rw [gridIndex_fiber n hn, gridCell_measure n hn _ hk hkn,
    ENNReal.toReal_ofReal (by positivity)]
  have hint : (∫ y in gridCell n (gridIndex n x), f y ∂μI) =
      ∫ y in gridCell n (gridIndex n x), f y := by
    rw [μI, Measure.restrict_restrict_of_subset hsub]
  rw [hint]
  simp [div_eq_mul_inv, mul_comm]

/-- The actual uniform-grid average is conditional expectation on the
sigma-algebra generated by its cell index. The endpoint zero is excluded by
the already proved null-measure endpoint fact, not a pointwise convention. -/
theorem condExp_ae_eq_gridMean (n : ℕ) (hn : 0 < n) {f : ℝ → ℝ}
    (hf : Integrable f μI) : μI[f | gridSigma n] =ᵐ[μI] gridMean f n := by
  have hcell := condExp_ae_eq_fiberMean (measurable_gridIndex n) hf
  have hunit : ∀ᵐ x ∂μI, x ∈ Set.Ioc (0 : ℝ) 1 := by
    exact ae_iff.mpr μI_compl_Ioc
  filter_upwards [hcell, hunit] with x hx hxunit
  exact hx.trans (fiberMean_gridIndex_eq_gridMean n hn f hxunit)

theorem stronglyMeasurable_gridMean (f : ℝ → ℝ) (n : ℕ) :
    StronglyMeasurable[gridSigma n] (gridMean f n) := by
  have hg : Measurable (fun k : ℤ ↦ (n : ℝ) * ∫ y in gridCell n k, f y) :=
    measurable_of_countable _
  exact (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

theorem integrable_gridMean (n : ℕ) (hn : 0 < n) {f : ℝ → ℝ}
    (hf : Integrable f μI) : Integrable (gridMean f n) μI :=
  integrable_condExp.congr (condExp_ae_eq_gridMean n hn hf)

/-- Dyadic cells are the special case with `2^r` equal grid cells. -/
theorem condExp_ae_eq_dyadicMean (r : ℕ) {f : ℝ → ℝ}
    (hf : Integrable f μI) :
    μI[f | gridSigma (2 ^ r)] =ᵐ[μI] gridMean f (2 ^ r) :=
  condExp_ae_eq_gridMean (2 ^ r) (pow_pos (by norm_num) r) hf

end Riesz
