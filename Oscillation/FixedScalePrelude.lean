import Oscillation.BucketGeometry
import Oscillation.Tail

namespace Oscillation
open scoped BigOperators
open MeasureTheory Riesz Riesz.PointSets Riesz.Occupancy
noncomputable section

lemma measurable_joint_grid_function {n K N : ℕ} (hK : 0 < K) (hN : 0 < N)
    (F : (Fin n → ℕ) → (Fin n → ℕ) → ℝ) :
    Measurable (fun P : Fin n → ℝ × ℝ =>
      F (sampleCells n K hK (fun i => (P i).1))
        (sampleCells n N hN (fun i => (P i).2))) := by
  have hu : Measurable (fun P : Fin n → ℝ × ℝ => fun i => (P i).1) :=
    Measurable.of_eval fun i => (measurable_pi_apply i).fst
  have hv : Measurable (fun P : Fin n → ℝ × ℝ => fun i => (P i).2) :=
    Measurable.of_eval fun i => (measurable_pi_apply i).snd
  exact (measurable_of_countable (fun q : (Fin n → ℕ) × (Fin n → ℕ) => F q.1 q.2)).comp
    (((measurable_sampleCells n K hK).comp hu).prodMk ((measurable_sampleCells n N hN).comp hv))

lemma integrable_joint_grid_function {n K N : ℕ} (hK : 0 < K) (hN : 0 < N)
    (F : (Fin n → ℕ) → (Fin n → ℕ) → ℝ) :
    Integrable (fun P : Fin n → ℝ × ℝ =>
      F (sampleCells n K hK (fun i => (P i).1))
        (sampleCells n N hN (fun i => (P i).2))) (Measure.pi (fun _ => μI.prod μI)) := by
  let cell : ℝ × ℝ → Fin K × Fin N := fun z => (finiteGridIndex K hK z.1, finiteGridIndex N hN z.2)
  have hm : Measurable cell :=
    ((measurable_finiteGridIndex K hK).comp measurable_fst).prodMk
      ((measurable_finiteGridIndex N hN).comp measurable_snd)
  exact integrable_iid_bucket_function (μI.prod μI) cell hm n
    (fun x => F (fun i => (x i).1.val) (fun i => (x i).2.val))

lemma interiorMass_nonneg' {n : ℕ} (K V b m : ℕ) (p Y : Fin n → ℕ) :
    0 ≤ interiorMass K V b m p Y := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

lemma interiorMass_le_count_root {n : ℕ} (K V b m : ℕ) (p Y : Fin n → ℕ) :
    interiorMass K V b m p Y ≤ (K*V:ℕ) * Real.sqrt n := by
  unfold interiorMass
  calc
    _ ≤ ∑ _c : Fin K, ∑ _v : Fin V, Real.sqrt n := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro v _
      apply Real.sqrt_le_sqrt
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset
        (fun i : Fin n => p i = c.val ∧ v.val*(b*m)+m ≤ Y i ∧
          Y i < v.val*(b*m)+(b-1)*m) Finset.univ)).trans_eq (Finset.card_fin n)
    _ = _ := by simp; ring

lemma interiorMass_iid_laplace_larger_coefficient (K V b m : ℕ) (hK : 0 < K) (hV : 0 < V)
    (hb : 4 ≤ b) (hm : 0 < m) {n : ℕ} (hn : 0 < n) {a : ℝ}
    (ha : Real.sqrt ((b:ℝ)*n/(K*V:ℕ)) ≤ a) :
    (∫ P : Fin n → ℝ × ℝ,
      Real.exp (-a * interiorMass K V b m
        (sampleCells n K hK (fun i => (P i).1))
        (sampleCells n (V*(b*m)) (by positivity) (fun i => (P i).2)))
      ∂Measure.pi (fun _ => μI.prod μI)) ≤ (2:ℝ)^(n+K*V) * (4/(b:ℝ))^n := by
  apply le_trans _ (interiorMass_iid_laplace K V b m hK hV hb hm hn)
  apply integral_mono
    (integrable_joint_grid_function (n := n) (N := V*(b*m)) hK (by positivity)
      (fun p Y => Real.exp (-a * interiorMass K V b m p Y)))
    (integrable_joint_grid_function (n := n) (N := V*(b*m)) hK (by positivity)
      (fun p Y => Real.exp (-Real.sqrt ((b:ℝ)*n/(K*V:ℕ)) * interiorMass K V b m p Y)))
  intro P
  apply Real.exp_le_exp.mpr
  have hs := interiorMass_nonneg' K V b m
    (sampleCells n K hK (fun i => (P i).1))
    (sampleCells n (V*(b*m)) (by positivity) (fun i => (P i).2))
  nlinarith

end
end Oscillation
