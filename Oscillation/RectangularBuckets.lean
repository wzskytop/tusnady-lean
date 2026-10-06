import Oscillation.HistogramTransport
import Riesz.UniformGrid
import Mathlib.Order.Interval.Finset.Fin

/-! Actual finite rectangular interior buckets and their Lebesgue probabilities. -/
namespace Oscillation
open scoped BigOperators ENNReal
open MeasureTheory Riesz Riesz.PointSets Riesz.Occupancy
noncomputable section

lemma finiteGridIndex_predicate_real (N : ℕ) (hN : 0 < N) (P : Fin N → Prop) [DecidablePred P] :
    (μI {x | P (finiteGridIndex N hN x)}).toReal =
      (∑ j : Fin N, if P j then (1:ℝ) else 0) / N := by
  have hm : MeasurableSet {x | P (finiteGridIndex N hN x)} :=
    (measurable_finiteGridIndex N hN) (Set.to_countable _).measurableSet
  rw [← measureReal_def, ← integral_indicator_one hm]
  simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using
    integral_finiteGridIndex N hN (fun j => if P j then (1:ℝ) else 0)

lemma coarseFineGrid_mass (V W : ℕ) (hV : 0 < V) (hW : 0 < W) (v : Fin V) :
    μI {y | (finProdFinEquiv.symm (finiteGridIndex (V*W) (Nat.mul_pos hV hW) y)).1 = v} =
      ENNReal.ofReal (1/(V:ℝ)) := by
  have hr := finiteGridIndex_predicate_real (V*W) (Nat.mul_pos hV hW)
    (fun a => (finProdFinEquiv.symm a).1 = v)
  have hsum : (∑ a : Fin (V*W), if (finProdFinEquiv.symm a).1 = v then (1:ℝ) else 0) = W := by
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun a : Fin V × Fin W => if a.1 = v then (1:ℝ) else 0)]
    rw [Fintype.sum_prod_type]
    change (∑ x : Fin V, ∑ _y : Fin W, if x = v then (1:ℝ) else 0) = W
    simp
  rw [hsum] at hr
  have heq : (W:ℝ)/(V*W:ℕ) = 1/(V:ℝ) := by
    push_cast
    field_simp
  rw [heq] at hr
  rw [← ENNReal.ofReal_toReal (measure_ne_top μI _), hr]

/-- The interior subcells remove one base-b child at each end of a vertical block. -/
def interiorSubcell (b m : ℕ) (r : Fin (b*m)) : Prop :=
  m ≤ r.val ∧ r.val < (b-1)*m

instance (b m : ℕ) : DecidablePred (interiorSubcell b m) :=
  fun r => inferInstanceAs (Decidable (m ≤ r.val ∧ r.val < (b-1)*m))

lemma boundarySubcell_card_le {b m : ℕ} (hb : 4 ≤ b) (hm : 0 < m) :
    (Finset.univ.filter (fun r : Fin (b*m) => ¬interiorSubcell b m r)).card ≤ 2*m := by
  have hlow : 1*m < b*m := Nat.mul_lt_mul_of_pos_right (by omega) hm
  have hhigh : (b-1)*m < b*m := Nat.mul_lt_mul_of_pos_right (by omega) hm
  let low : Fin (b*m) := ⟨m, by omega⟩
  let high : Fin (b*m) := ⟨(b-1)*m, hhigh⟩
  have heq : Finset.univ.filter (fun r : Fin (b*m) => ¬interiorSubcell b m r) =
      Finset.Iio low ∪ Finset.Ici high := by
    apply Finset.ext
    intro r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_Iio, Finset.mem_Ici]
    change (¬(m ≤ r.val ∧ r.val < (b-1)*m)) ↔ (r.val < m ∨ (b-1)*m ≤ r.val)
    omega
  rw [heq]
  calc
    _ ≤ (Finset.Iio low).card + (Finset.Ici high).card := Finset.card_union_le _ _
    _ ≤ 2*m := by
      rw [Fin.card_Iio, Fin.card_Ici]
      dsimp [low, high]
      rw [Nat.sub_mul]
      omega

lemma fineBoundary_mass {V b m : ℕ} (hV : 0 < V) (hb : 4 ≤ b) (hm : 0 < m) :
    μI {y | ¬interiorSubcell b m (finProdFinEquiv.symm
      (finiteGridIndex (V*(b*m)) (by positivity) y)).2} ≤ ENNReal.ofReal (2/(b:ℝ)) := by
  have hb0 : 0 < b := by omega
  have hbR : (0:ℝ) < b := by exact_mod_cast hb0
  have hVR : (0:ℝ) < V := by exact_mod_cast hV
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hr := finiteGridIndex_predicate_real (V*(b*m)) (by positivity)
    (fun a => ¬interiorSubcell b m (finProdFinEquiv.symm a).2)
  have hsum : (∑ a : Fin (V*(b*m)), if ¬interiorSubcell b m (finProdFinEquiv.symm a).2
      then (1:ℝ) else 0) = V * (Finset.univ.filter (fun r : Fin (b*m) => ¬interiorSubcell b m r)).card := by
    rw [Equiv.sum_comp finProdFinEquiv.symm
      (fun a : Fin V × Fin (b*m) => if ¬interiorSubcell b m a.2 then (1:ℝ) else 0)]
    rw [Fintype.sum_prod_type]
    change (∑ _x : Fin V, ∑ y : Fin (b*m), if ¬interiorSubcell b m y then (1:ℝ) else 0) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_boole]
  rw [hsum] at hr
  have hreal : (μI {y | ¬interiorSubcell b m (finProdFinEquiv.symm
      (finiteGridIndex (V*(b*m)) (by positivity) y)).2}).toReal ≤ 2/(b:ℝ) := by
    rw [hr]
    calc
      _ ≤ (V:ℝ)*(2*m)/(V*(b*m):ℕ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast boundarySubcell_card_le hb hm
      _ = _ := by push_cast; field_simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top μI _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Actual point-to-bucket map: horizontal cell and coarse vertical cell, with boundary strips removed. -/
def rectangularBucket (K V b m : ℕ) (hK : 0 < K) (hV : 0 < V) (hb : 0 < b) (hm : 0 < m)
    (z : ℝ × ℝ) : Option (Fin (K*V)) :=
  let vr := finProdFinEquiv.symm (finiteGridIndex (V*(b*m)) (by positivity) z.2)
  if interiorSubcell b m vr.2 then
    some (finProdFinEquiv (finiteGridIndex K hK z.1, vr.1)) else none

lemma rectangularBucket_measurable (K V b m : ℕ) (hK : 0 < K) (hV : 0 < V)
    (hb : 0 < b) (hm : 0 < m) [MeasurableSpace (Option (Fin (K*V)))] :
    Measurable (rectangularBucket K V b m hK hV hb hm) := by
  let f (a : Fin K × Fin (V*(b*m))) : Option (Fin (K*V)) :=
    let vr := finProdFinEquiv.symm a.2
    if interiorSubcell b m vr.2 then some (finProdFinEquiv (a.1, vr.1)) else none
  exact (measurable_of_countable f).comp
    (((measurable_finiteGridIndex K hK).comp measurable_fst).prodMk
      ((measurable_finiteGridIndex (V*(b*m)) (by positivity)).comp measurable_snd))


lemma rectangularBucket_good_mass (K V b m : ℕ) (hK : 0 < K) (hV : 0 < V)
    (hb : 0 < b) (hm : 0 < m) (c : Fin (K*V)) :
    (μI.prod μI) {z | rectangularBucket K V b m hK hV hb hm z = some c}
      ≤ ENNReal.ofReal (1/(K*V:ℕ)) := by
  let a := finProdFinEquiv.symm c
  have hsub : {z | rectangularBucket K V b m hK hV hb hm z = some c} ⊆
      {x | finiteGridIndex K hK x = a.1} ×ˢ
      {y | (finProdFinEquiv.symm (finiteGridIndex (V*(b*m)) (by positivity) y)).1 = a.2} := by
    intro z hz
    change rectangularBucket K V b m hK hV hb hm z = some c at hz
    dsimp only [rectangularBucket] at hz
    split_ifs at hz with hg
    · have he := congrArg finProdFinEquiv.symm (Option.some.inj hz)
      simp only [Equiv.symm_apply_apply] at he
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  calc
    _ ≤ (μI.prod μI) ({x | finiteGridIndex K hK x = a.1} ×ˢ
      {y | (finProdFinEquiv.symm (finiteGridIndex (V*(b*m)) (by positivity) y)).1 = a.2}) :=
      measure_mono hsub
    _ = _ := by
      rw [Measure.prod_prod, finiteGridIndex_fiber_mass,
        coarseFineGrid_mass V (b*m) hV (Nat.mul_pos hb hm),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/(K:ℝ))]
      congr 1
      push_cast
      ring

lemma rectangularBucket_bad_mass (K V b m : ℕ) (hK : 0 < K) (hV : 0 < V)
    (hb : 4 ≤ b) (hm : 0 < m) :
    (μI.prod μI) {z | rectangularBucket K V b m hK hV (by omega) hm z = none}
      ≤ ENNReal.ofReal (2/(b:ℝ)) := by
  have heq : {z | rectangularBucket K V b m hK hV (by omega) hm z = none} =
      Set.univ ×ˢ {y | ¬interiorSubcell b m (finProdFinEquiv.symm
        (finiteGridIndex (V*(b*m)) (by positivity) y)).2} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and, rectangularBucket]
    split_ifs <;> simp_all
  rw [heq, Measure.prod_prod, measure_univ, one_mul]
  exact fineBoundary_mass hV hb hm

/-- The one-layer count estimate for actual uniform points and the exact finite rectangular buckets. -/
theorem rectangularBucket_iid_laplace (K V b m : ℕ) (hK : 0 < K) (hV : 0 < V)
    (hb : 4 ≤ b) (hm : 0 < m) {n : ℕ} (hn : 0 < n) :
    (∫ P : Fin n → ℝ × ℝ,
      Real.exp (-Real.sqrt ((b:ℝ)*n/(K*V:ℕ)) *
        bucketSquareRootSum (rectangularBucket K V b m hK hV (by omega) hm) P)
      ∂Measure.pi (fun _ => μI.prod μI)) ≤ (2:ℝ)^(n+K*V) * (4/(b:ℝ))^n := by
  let : MeasurableSpace (Option (Fin (K*V))) := ⊤
  have hbR : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  exact integral_iid_interior_laplace_of_measure (μI.prod μI) hn (Nat.mul_pos hK hV) hbR
    (rectangularBucket K V b m hK hV (by omega) hm)
    (rectangularBucket_measurable K V b m hK hV (by omega) hm)
    (rectangularBucket_good_mass K V b m hK hV (by omega) hm)
    ((rectangularBucket_bad_mass K V b m hK hV hb hm).trans
      (ENNReal.ofReal_le_ofReal (by gcongr; norm_num)))

end
end Oscillation
