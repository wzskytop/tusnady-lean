import Riesz.PointSets
import Mathlib.MeasureTheory.Integral.Prod

namespace Oscillation
noncomputable section
open MeasureTheory Riesz.PointSets

abbrev coordinateSampleLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => μI)

abbrev pointSampleLaw (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin n => μI.prod μI)

def splitCoordinates (n : ℕ) : (Fin n → ℝ × ℝ) ≃ᵐ ((Fin n → ℝ) × (Fin n → ℝ)) :=
  MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)

lemma splitCoordinates_apply {n : ℕ} (P : Fin n → ℝ × ℝ) :
    splitCoordinates n P = (fun i => (P i).1, fun i => (P i).2) := rfl

lemma splitCoordinates_symm_apply {n : ℕ} (UV : (Fin n → ℝ) × (Fin n → ℝ)) :
    (splitCoordinates n).symm UV = fun i => (UV.1 i, UV.2 i) := rfl

lemma splitCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (splitCoordinates n) (pointSampleLaw n)
      ((coordinateSampleLaw n).prod (coordinateSampleLaw n)) :=
  measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (fun _ => μI) (fun _ => μI)

lemma pairCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (splitCoordinates n).symm
      ((coordinateSampleLaw n).prod (coordinateSampleLaw n)) (pointSampleLaw n) :=
  MeasurePreserving.symm (splitCoordinates n) (splitCoordinates_measurePreserving n)

lemma pointSampleLaw_eq_unifPts (n : ℕ) : pointSampleLaw n = unifPts n := by
  unfold pointSampleLaw unifPts
  simp_rw [unitSq_eq]

/-- This identity holds for every set, without a measurability premise, since
the coordinate split is a measurable equivalence. -/
lemma point_event_eq_coordinate_event {n : ℕ} (S : Set (Fin n → ℝ × ℝ)) :
    pointSampleLaw n S = ((coordinateSampleLaw n).prod (coordinateSampleLaw n))
      {UV | (fun i => (UV.1 i, UV.2 i)) ∈ S} := by
  have h := pairCoordinates_measurePreserving n
  rw [← h.map_eq, (splitCoordinates n).symm.measurableEmbedding.map_apply]
  rfl

lemma integrable_pairCoordinates_iff {n : ℕ} (F : (Fin n → ℝ × ℝ) → ℝ) :
    Integrable (fun UV : (Fin n → ℝ) × (Fin n → ℝ) => F (fun i => (UV.1 i, UV.2 i)))
      ((coordinateSampleLaw n).prod (coordinateSampleLaw n)) ↔
      Integrable F (pointSampleLaw n) :=
  (pairCoordinates_measurePreserving n).integrable_comp_emb
    (splitCoordinates n).symm.measurableEmbedding

lemma integral_point_eq_product {n : ℕ} (F : (Fin n → ℝ × ℝ) → ℝ) :
    (∫ P, F P ∂pointSampleLaw n) =
      ∫ UV : (Fin n → ℝ) × (Fin n → ℝ), F (fun i => (UV.1 i, UV.2 i))
        ∂((coordinateSampleLaw n).prod (coordinateSampleLaw n)) :=
  ((pairCoordinates_measurePreserving n).integral_comp' F).symm

lemma integral_point_eq_vertical_horizontal {n : ℕ} (F : (Fin n → ℝ × ℝ) → ℝ)
    (hF : Integrable F (pointSampleLaw n)) :
    (∫ P, F P ∂pointSampleLaw n) =
      ∫ V, ∫ U, F (fun i => (U i, V i)) ∂coordinateSampleLaw n ∂coordinateSampleLaw n := by
  rw [integral_point_eq_product]
  exact integral_prod_symm _ ((integrable_pairCoordinates_iff F).mpr hF)

lemma ae_coordinateSampleLaw_mem_Ioc (n : ℕ) :
    ∀ᵐ U ∂coordinateSampleLaw n, ∀ i, U i ∈ Set.Ioc (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μI) (i := i)
    (ae_iff.mpr μI_compl_Ioc)

lemma ae_pointSampleLaw_mem_Ioc (n : ℕ) :
    ∀ᵐ P ∂pointSampleLaw n, ∀ i, (P i).1 ∈ Set.Ioc (0 : ℝ) 1 ∧
      (P i).2 ∈ Set.Ioc (0 : ℝ) 1 := by
  have hI : ∀ᵐ x ∂μI, x ∈ Set.Ioc (0 : ℝ) 1 := ae_iff.mpr μI_compl_Ioc
  have hprod : ∀ᵐ z ∂μI.prod μI, z.1 ∈ Set.Ioc (0 : ℝ) 1 ∧ z.2 ∈ Set.Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.prod measurableSet_Ioc)).mpr
    filter_upwards [hI] with u hu
    filter_upwards [hI] with v hv
    exact ⟨hu, hv⟩
  apply ae_all_iff.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μI.prod μI) (i := i) hprod

end
end Oscillation
