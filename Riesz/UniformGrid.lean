import Riesz.Occupancy
import Riesz.ProfileLaw
import Riesz.GridRefinement

/-!
# The distribution of the actual finite grid index

These identities connect uniform real samples with the finite laws used by the
moment argument. The cell endpoints use the same right-closed convention as
`CellAverages`; the exceptional complement of `(0,1]` is handled by its null measure.
-/

namespace Riesz
noncomputable section
open MeasureTheory PointSets Occupancy
open scoped ENNReal

lemma measurable_finiteGridIndex (m : ℕ) (hm : 0 < m) :
    Measurable (finiteGridIndex m hm) := by
  let g : ℤ → Fin m := fun k => ⟨k.toNat % m, Nat.mod_lt _ hm⟩
  have heq : finiteGridIndex m hm = fun x =>
      if x ∈ Set.Ioc (0 : ℝ) 1 then g (gridIndex m x) else ⟨0, hm⟩ := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · simp only [finiteGridIndex, hx, dite_true, ite_true]
      apply Fin.ext
      dsimp [g]
      rw [Nat.mod_eq_of_lt]
      obtain ⟨hk, hkn⟩ := gridIndex_bounds m hm hx
      have hk0 : (0 : ℤ) ≤ gridIndex m x := by exact_mod_cast hk
      have hk1 : gridIndex m x < (m : ℤ) := by
        exact_mod_cast (show (gridIndex m x : ℝ) < m by linarith)
      omega
    · simp [finiteGridIndex, hx]
  rw [heq]
  exact Measurable.ite measurableSet_Ioc
    ((measurable_of_countable g).comp (measurable_gridIndex m)) measurable_const

lemma finiteGridIndex_fiber_mass (m : ℕ) (hm : 0 < m) (j : Fin m) :
    μI {x | finiteGridIndex m hm x = j} = ENNReal.ofReal (1 / (m : ℝ)) := by
  apply le_antisymm (finiteGridIndex_mass m hm j)
  have hsub : gridCell m (j : ℤ) ⊆ {x | finiteGridIndex m hm x = j} := by
    intro x hx
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hxunit : x ∈ Set.Ioc (0 : ℝ) 1 := by
      refine ⟨lt_of_le_of_lt (div_nonneg (by positivity) hm'.le) hx.1, ?_⟩
      apply hx.2.trans
      apply (div_le_one hm').mpr
      exact_mod_cast j.isLt
    have hi := finiteGridIndex_eq hm hxunit
    have hj : gridIndex m x = (j : ℤ) := by
      rw [← gridIndex_fiber m hm] at hx
      exact hx
    apply Fin.ext
    exact_mod_cast hi.trans hj
  have hh := measure_mono (μ := μI) hsub
  rw [gridCell_measure m hm _ (by positivity) (by exact_mod_cast j.isLt)] at hh
  exact hh

/-- The expectation of any function of the actual grid cell is its uniform
finite average. This is an equality of Lebesgue integrals, not a distributional assumption. -/
theorem integral_finiteGridIndex (m : ℕ) (hm : 0 < m) (f : Fin m → ℝ) :
    (∫ x, f (finiteGridIndex m hm x) ∂μI) = (∑ j, f j) / m := by
  have hi := measurable_finiteGridIndex m hm
  rw [← integral_map hi.aemeasurable (measurable_of_countable f).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  simp_rw [measureReal_def, Measure.map_apply hi (measurableSet_singleton _),
    show ∀ j : Fin m, finiteGridIndex m hm ⁻¹' {j} = {x | finiteGridIndex m hm x = j} from
      fun _ => rfl,
    finiteGridIndex_fiber_mass, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (m : ℝ)),
    smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Splitting a uniformly chosen grid cell into quarter and within-quarter
indices gives exactly the finite profile law used by the moment estimates. -/
theorem integral_quarterGrid (m : ℕ) (hm : 0 < m) (f : Fin 4 × Fin m → ℝ) :
    (∫ x, f (finProdFinEquiv.symm (finiteGridIndex (4 * m) (by omega) x)) ∂μI) =
      Moments.expectation (profileLaw m hm) f := by
  rw [integral_finiteGridIndex (4 * m) (by omega) (fun j => f (finProdFinEquiv.symm j))]
  unfold Moments.expectation profileLaw
  simp only [← Finset.mul_sum]
  have hs : (∑ j : Fin (4 * m), f (finProdFinEquiv.symm j)) = ∑ j, f j :=
    Equiv.sum_comp finProdFinEquiv.symm f
  rw [hs]
  push_cast
  ring

/-- A quarter-grid profile value is the actual average of `profile` over its
cell. This connects the finite probability calculation with the manuscript's `w_L`. -/
theorem gridMean_profile_eq_cellValue (m : ℕ) (hm : 0 < m) {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    gridMean profile (4 * m) x =
      profileValue m (finProdFinEquiv.symm (finiteGridIndex (4 * m) (by omega) x)) := by
  let a := finProdFinEquiv.symm (finiteGridIndex (4 * m) (by omega) x)
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hidx : gridIndex (4 * m) x = ((a.2 : ℕ) + m * (a.1 : ℕ) : ℤ) := by
    have h := (finiteGridIndex_eq (by omega : 0 < 4 * m) hx).symm
    have he : finProdFinEquiv a = finiteGridIndex (4 * m) (by omega) x :=
      finProdFinEquiv.apply_symm_apply _
    rw [← he] at h
    exact h
  have hleft : (((a.2 : ℕ) + m * (a.1 : ℕ) : ℤ) : ℝ) / (4 * m : ℕ) =
      (a.1 : ℕ) / 4 + (a.2 : ℕ) / (4 * m : ℝ) := by
    push_cast
    field_simp
    ring
  have hright : ((((a.2 : ℕ) + m * (a.1 : ℕ) : ℤ) : ℝ) + 1) / (4 * m : ℕ) =
      (a.1 : ℕ) / 4 + ((a.2 : ℕ) + 1) / (4 * m : ℝ) := by
    push_cast
    field_simp
    ring
  change gridMean profile (4 * m) x = profileValue m a
  unfold gridMean gridCell
  rw [hidx, hleft, hright]
  have hab : ((a.1 : ℕ) / 4 + (a.2 : ℕ) / (4 * m : ℝ)) ≤
      ((a.1 : ℕ) / 4 + ((a.2 : ℕ) + 1) / (4 * m : ℝ)) := by
    gcongr
    exact le_add_of_nonneg_right (by norm_num)
  rw [← intervalIntegral.integral_of_le hab]
  simpa only [profileValue, Nat.cast_mul, Nat.cast_ofNat] using profile_cell_average a.1 a.2

/-- All moments of the actual averaged continuous profile have the already
proved finite law. No limiting argument is used. -/
theorem integral_gridMean_profile (m : ℕ) (hm : 0 < m) (f : ℝ → ℝ) :
    (∫ x, f (gridMean profile (4 * m) x) ∂μI) =
      Moments.expectation (profileLaw m hm) (fun a => f (profileValue m a)) := by
  rw [← integral_quarterGrid m hm (fun a => f (profileValue m a))]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr μI_compl_Ioc] with x hx
  rw [gridMean_profile_eq_cellValue m hm hx]


/-- The fresh block index after the `n`-cell coarse index has been exposed.
Its value depends on the position rescaled inside that actual coarse cell. -/
def freshGridIndex (n m : ℕ) (hm : 0 < m) (x : ℝ) : Fin m :=
  finiteGridIndex m hm ((n : ℝ) * x - gridIndex n x)

lemma measurable_freshGridIndex (n m : ℕ) (hm : 0 < m) :
    Measurable (freshGridIndex n m hm) := by
  exact (measurable_finiteGridIndex m hm).comp
    ((measurable_const.mul measurable_id).sub
      ((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp (measurable_gridIndex n)))

lemma integrable_freshGridFunction (n m : ℕ) (hm : 0 < m) (f : Fin m → ℝ) :
    Integrable (fun x => f (freshGridIndex n m hm x)) μI := by
  apply Integrable.of_bound
    ((measurable_of_countable f).comp (measurable_freshGridIndex n m hm)).aestronglyMeasurable
    (∑ j, |f j|)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_univ _)

/-- Every coarse cell contains the same uniform distribution of fresh indices.
This calculation is pointwise in the coarse cell and includes grid boundaries. -/
theorem gridMean_freshGridIndex (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (f : Fin m → ℝ) (x : ℝ) :
    gridMean (fun y => f (freshGridIndex n m hm y)) n x = (∑ j, f j) / m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let k : ℤ := gridIndex n x
  have hab : (k : ℝ) / n ≤ ((k : ℝ) + 1) / n := by
    gcongr
    exact le_add_of_nonneg_right (by norm_num)
  have hcell : (∫ y in gridCell n k, f (freshGridIndex n m hm y)) =
      ∫ y in gridCell n k, f (finiteGridIndex m hm ((n : ℝ) * y - k)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    have hk : gridIndex n y = k := by
      change y ∈ gridCell n k at hy
      rw [← gridIndex_fiber n hn] at hy
      exact hy
    simp only [freshGridIndex, hk]
  unfold gridMean
  change (n : ℝ) * (∫ y in gridCell n k, f (freshGridIndex n m hm y)) = _
  rw [hcell]
  unfold gridCell
  rw [← intervalIntegral.integral_of_le hab]
  simp_rw [sub_eq_add_neg]
  rw [intervalIntegral.integral_comp_mul_add (fun y => f (finiteGridIndex m hm y)) hn'.ne' (-(k : ℝ))]
  have hleft : (n : ℝ) * ((k : ℝ) / n) + -(k : ℝ) = 0 := by field_simp; ring
  have hright : (n : ℝ) * (((k : ℝ) + 1) / n) + -(k : ℝ) = 1 := by field_simp; ring
  rw [hleft, hright, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hint : (∫ y in Set.Ioc (0 : ℝ) 1, f (finiteGridIndex m hm y)) =
      ∫ y, f (finiteGridIndex m hm y) ∂μI := by
    rw [μI, ← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rw [hint, integral_finiteGridIndex]

/-- The newly exposed block is conditionally uniform given the genuine coarse
grid sigma-algebra. The average is proved, not assumed as conditional independence. -/
theorem condExp_freshGridIndex (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (f : Fin m → ℝ) :
    μI[(fun x => f (freshGridIndex n m hm x)) | gridSigma n] =ᵐ[μI]
      (fun _ => (∑ j, f j) / m) := by
  refine (condExp_ae_eq_gridMean n hn (integrable_freshGridFunction n m hm f)).trans ?_
  exact Filter.Eventually.of_forall (gridMean_freshGridIndex n m hn hm f)


lemma coarseLocalCoordinate_mem (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (n : ℝ) * x - gridIndex n x ∈ Set.Ioc (0 : ℝ) 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx := mem_gridCell_gridIndex n hn x
  change (gridIndex n x : ℝ) / n < x ∧ x ≤ ((gridIndex n x : ℝ) + 1) / n at hx
  rw [div_lt_iff₀ hn', le_div_iff₀ hn'] at hx
  constructor <;> nlinarith [hx.1, hx.2]

/-- The fresh block is exactly the remainder of the refined cell index. -/
theorem freshGridIndex_eq_emod (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (x : ℝ) :
    ((freshGridIndex n m hm x : ℕ) : ℤ) = gridIndex (n * m) x % (m : ℤ) := by
  rw [freshGridIndex, finiteGridIndex_eq hm (coarseLocalCoordinate_mem n hn x)]
  have hshift : (m : ℝ) * ((n : ℝ) * x - gridIndex n x) =
      ((n * m : ℕ) : ℝ) * x - (((m : ℤ) * gridIndex n x : ℤ) : ℝ) := by
    push_cast
    ring
  unfold gridIndex at hshift ⊢
  rw [hshift, Int.ceil_sub_intCast]
  change ⌈((n * m : ℕ) : ℝ) * x⌉ - (m : ℤ) * gridIndex n x - 1 =
    gridIndex (n * m) x % (m : ℤ)
  rw [Int.emod_def, gridIndex_mul_ediv n m hm]
  unfold gridIndex
  ring

/-- The fresh block is known after the refined grid has been exposed. -/
theorem freshGridIndex_grid_measurable (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    Measurable[gridSigma (n * m)] (freshGridIndex n m hm) := by
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  let g : ℤ → Fin m := fun k => ⟨(k % (m : ℤ)).toNat, by
    have hlo := Int.emod_nonneg k hmz.ne'
    have hhi := Int.emod_lt_of_pos k hmz
    omega⟩
  have heq : freshGridIndex n m hm = g ∘ gridIndex (n * m) := by
    funext x
    apply Fin.ext
    have he := freshGridIndex_eq_emod n m hn hm x
    dsimp [g]
    omega
  rw [heq]
  exact (measurable_of_countable g).comp (Measurable.of_comap_le le_rfl)


/-- The actual cell-averaged profile evaluated at the rescaled position inside
the current coarse cell. For `n=2^r` and `4m=2^L`, this is the fresh `w_L` factor. -/
def freshAveragedProfile (n m : ℕ) (x : ℝ) : ℝ :=
  gridMean profile (4 * m) ((n : ℝ) * x - gridIndex n x)

lemma freshAveragedProfile_eq (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (x : ℝ) :
    freshAveragedProfile n m x =
      profileValue m (finProdFinEquiv.symm (freshGridIndex n (4 * m) (by omega) x)) := by
  exact gridMean_profile_eq_cellValue m hm (coarseLocalCoordinate_mem n hn x)

lemma freshAveragedProfile_grid_measurable (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    Measurable[gridSigma (n * (4 * m))] (freshAveragedProfile n m) := by
  have heq : freshAveragedProfile n m = fun x =>
      profileValue m (finProdFinEquiv.symm (freshGridIndex n (4 * m) (by omega) x)) := by
    funext x
    exact freshAveragedProfile_eq n m hn hm x
  rw [heq]
  exact (measurable_of_countable (fun a : Fin (4 * m) => profileValue m (finProdFinEquiv.symm a))).comp
    (freshGridIndex_grid_measurable n (4 * m) hn (by omega))

/-- The conditional law of the actual profile average equals `profileLaw`.
This supplies all the conditional moment identities used in a fresh digit block. -/
theorem condExp_freshAveragedProfile (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (f : ℝ → ℝ) :
    μI[(fun x => f (freshAveragedProfile n m x)) | gridSigma n] =ᵐ[μI]
      (fun _ => Moments.expectation (profileLaw m hm) (fun a => f (profileValue m a))) := by
  have heq : (fun x => f (freshAveragedProfile n m x)) = fun x =>
      f (profileValue m (finProdFinEquiv.symm (freshGridIndex n (4 * m) (by omega) x))) := by
    funext x
    rw [freshAveragedProfile_eq n m hn hm x]
  rw [heq]
  have h := condExp_freshGridIndex n (4 * m) hn (by omega)
    (fun a => f (profileValue m (finProdFinEquiv.symm a)))
  have hmean : (∑ a : Fin (4 * m), f (profileValue m (finProdFinEquiv.symm a))) / (4 * m : ℕ) =
      Moments.expectation (profileLaw m hm) (fun a => f (profileValue m a)) := by
    rw [← integral_finiteGridIndex (4 * m) (by omega)
      (fun a => f (profileValue m (finProdFinEquiv.symm a)))]
    exact integral_quarterGrid m hm (fun a => f (profileValue m a))
  simpa only [hmean] using h


end
end Riesz
