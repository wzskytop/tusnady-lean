import Oscillation.RectangularBuckets
import Oscillation.RowComparison
import Oscillation.RealGrid

/-! The finite-oscillation interior counts are exactly the actual rectangular bucket counts. -/
namespace Oscillation
open scoped BigOperators
open MeasureTheory Riesz Riesz.PointSets Riesz.Occupancy
noncomputable section

lemma interior_div_mod_iff (b m y v : ℕ) :
    (y/(b*m) = v ∧ m ≤ y%(b*m) ∧ y%(b*m) < (b-1)*m) ↔
      (v*(b*m)+m ≤ y ∧ y < v*(b*m)+(b-1)*m) := by
  have hsub : (b-1)*m ≤ b*m := Nat.mul_le_mul_right m (Nat.sub_le b 1)
  have hid := Nat.mod_add_div' y (b*m)
  constructor
  · rintro ⟨hdiv, hlo, hhi⟩
    rw [hdiv] at hid
    omega
  · rintro ⟨hlo,hhi⟩
    have hdiv : y/(b*m) = v := Nat.div_eq_of_lt_le (by omega) (by
      rw [Nat.add_mul, Nat.one_mul]
      omega)
    rw [hdiv] at hid
    exact ⟨hdiv, by omega, by omega⟩

lemma rectangularBucket_some_iff (K V b m : ℕ) (hK : 0 < K) (hV : 0 < V)
    (hb : 0 < b) (hm : 0 < m) (z : ℝ × ℝ) (c : Fin K) (v : Fin V) :
    rectangularBucket K V b m hK hV hb hm z = some (finProdFinEquiv (c,v)) ↔
      (finiteGridIndex K hK z.1).val = c.val ∧
      v.val*(b*m)+m ≤ (finiteGridIndex (V*(b*m)) (by positivity) z.2).val ∧
      (finiteGridIndex (V*(b*m)) (by positivity) z.2).val < v.val*(b*m)+(b-1)*m := by
  let X := finiteGridIndex K hK z.1
  let Y := finiteGridIndex (V*(b*m)) (by positivity) z.2
  have he : rectangularBucket K V b m hK hV hb hm z = some (finProdFinEquiv (c,v)) ↔
      X = c ∧ (finProdFinEquiv.symm Y).1 = v ∧ interiorSubcell b m (finProdFinEquiv.symm Y).2 := by
    dsimp only [rectangularBucket, X, Y]
    split_ifs with hg
    · simp only [Option.some.injEq, Equiv.apply_eq_iff_eq, Prod.mk.injEq, hg, and_true]
    · simp
      intro _ _
      exact hg
  rw [he]
  simp only [Fin.ext_iff, finProdFinEquiv_symm_apply, interiorSubcell]
  change (X.val = c.val ∧ Y.val/(b*m) = v.val ∧
      m ≤ Y.val%(b*m) ∧ Y.val%(b*m) < (b-1)*m) ↔ _
  rw [interior_div_mod_iff]

/-- Exact identification of the proof's geometric interior mass with the sum of actual bucket counts. -/
lemma bucketSquareRootSum_eq_interiorMass (K V b m : ℕ) (hK : 0 < K) (hV : 0 < V)
    (hb : 0 < b) (hm : 0 < m) {n : ℕ} (P : Fin n → ℝ × ℝ) :
    bucketSquareRootSum (rectangularBucket K V b m hK hV hb hm) P =
      interiorMass K V b m
        (sampleCells n K hK (fun i => (P i).1))
        (sampleCells n (V*(b*m)) (by positivity) (fun i => (P i).2)) := by
  unfold bucketSquareRootSum interiorMass
  rw [← Equiv.sum_comp finProdFinEquiv (fun c : Fin (K*V) =>
    Real.sqrt ((Finset.univ.filter (fun i =>
      rectangularBucket K V b m hK hV hb hm (P i) = some c)).card))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro v _
  congr 2
  unfold interiorCount interiorIndices
  congr 1
  apply Finset.ext
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact rectangularBucket_some_iff K V b m hK hV hb hm (P i) c v


/-- The actual per-layer interior-mass Laplace estimate, directly in the notation of the drift lemma. -/
theorem interiorMass_iid_laplace (K V b m : ℕ) (hK : 0 < K) (hV : 0 < V)
    (hb : 4 ≤ b) (hm : 0 < m) {n : ℕ} (hn : 0 < n) :
    (∫ P : Fin n → ℝ × ℝ,
      Real.exp (-Real.sqrt ((b:ℝ)*n/(K*V:ℕ)) * interiorMass K V b m
        (sampleCells n K hK (fun i => (P i).1))
        (sampleCells n (V*(b*m)) (by positivity) (fun i => (P i).2)))
      ∂Measure.pi (fun _ => μI.prod μI)) ≤ (2:ℝ)^(n+K*V) * (4/(b:ℝ))^n := by
  simpa only [bucketSquareRootSum_eq_interiorMass] using
    rectangularBucket_iid_laplace K V b m hK hV hb hm hn

end
end Oscillation
