import Oscillation.RowComparison

namespace Oscillation
noncomputable section
open Finset MeasureTheory

lemma interiorCount_le {n : ℕ} (b m : ℕ) (p Y : Fin n → ℕ) (c v : ℕ) :
    interiorCount b m p Y c v ≤ n := by
  unfold interiorCount interiorIndices
  exact (card_filter_le _ _).trans_eq (by simp)

lemma interiorMass_nonneg {n : ℕ} (K V b m : ℕ) (p Y : Fin n → ℕ) :
    0 ≤ interiorMass K V b m p Y := by
  unfold interiorMass
  exact sum_nonneg fun c _ => sum_nonneg fun v _ => Real.sqrt_nonneg _

lemma interiorMass_le_sqrt {n : ℕ} (K V b m : ℕ) (p Y : Fin n → ℕ) :
    interiorMass K V b m p Y ≤ (K * V : ℕ) * Real.sqrt n := by
  unfold interiorMass
  calc
    _ ≤ ∑ _c : Fin K, ∑ _v : Fin V, Real.sqrt n := by
      apply sum_le_sum
      intro c _
      apply sum_le_sum
      intro v _
      apply Real.sqrt_le_sqrt
      exact_mod_cast interiorCount_le b m p Y c.val v.val
    _ = _ := by simp; ring

lemma interiorMass_le_linear {n : ℕ} (hn : 1 ≤ n) (K V b m : ℕ) (p Y : Fin n → ℕ) :
    interiorMass K V b m p Y ≤ (K * V : ℕ) * (n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact (interiorMass_le_sqrt K V b m p Y).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr hn')) (by positivity))

lemma endpointValue_abs_le_card {n : ℕ} (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1)
    (p Y : Fin n → ℕ) (c y : ℕ) : |endpointValue χ p Y c y| ≤ n := by
  unfold endpointValue
  calc
    _ ≤ ∑ i, |χ i * (if Y i < y then 1 else 0) * endpointWeight (p i) c| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_nonneg (endpointWeight_nonneg (p i) c)]
      split_ifs
      · norm_num only [abs_one, mul_one]
        exact (mul_le_mul_of_nonneg_right (hχ i) (endpointWeight_nonneg (p i) c)).trans
          (by simpa using endpointWeight_le_one (p i) c)
      · norm_num
    _ = _ := by simp

lemma gridPotential_le_two_card {n K V m : ℕ} (hK : 0 < K) (hV : 0 < V)
    (hm : 0 < m) (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1)
    (p Y : Fin n → ℕ) : gridPotential K V m hm χ p Y ≤ 2 * n := by
  apply gridPotential_le_of_values hK hV hm χ p Y n
  intro c v t
  exact endpointValue_abs_le_card χ hχ p Y c.val _

lemma interiorMass_measurable {n : ℕ} (K V b m : ℕ) :
    Measurable (fun pY : (Fin n → ℕ) × (Fin n → ℕ) =>
      interiorMass K V b m pY.1 pY.2) := measurable_of_countable _

lemma gridPotential_measurable {n : ℕ} (K V m : ℕ) (hm : 0 < m) (χ : Fin n → ℝ) :
    Measurable (fun pY : (Fin n → ℕ) × (Fin n → ℕ) =>
      gridPotential K V m hm χ pY.1 pY.2) := measurable_of_countable _

end
end Oscillation
