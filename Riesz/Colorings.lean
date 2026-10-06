import Riesz.PointSets

/-!
# Taking the finite union over every coloring

This file connects the fixed-coloring probability estimate to the actual bad
event for arbitrary index colorings. It does not assume that the coloring was
chosen independently of the point set.
-/

namespace Riesz.PointSets
noncomputable section
open MeasureTheory Finset
open scoped ENNReal

/-- A two-valued parametrization of colors. -/
def boolSign (b : Bool) : ℤ := if b then 1 else -1

lemma boolSign_pm (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
  cases b <;> simp [boolSign]

/-- Bad event for one fixed coloring, before the final union bound. -/
def fixedColorBad (n : ℕ) (b : ℝ) (χ : Fin n → Bool) : Set (Fin n → ℝ × ℝ) :=
  {X | ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    |∑ t ∈ univ.filter
        (fun t => 0 ≤ (X t).1 ∧ (X t).1 ≤ x ∧ 0 ≤ (X t).2 ∧ (X t).2 ≤ y),
      (boolSign (χ t) : ℝ)| ≤ b}

lemma badSet_eq_iUnion_fixedColorBad (n : ℕ) (b : ℝ) :
    badSet n b = ⋃ χ : Fin n → Bool, fixedColorBad n b χ := by
  classical
  ext X
  constructor
  · rintro ⟨χ, hχ, hsmall⟩
    let c : Fin n → Bool := fun t => decide (χ t = 1)
    have hc : ∀ t, boolSign (c t) = χ t := by
      intro t
      rcases hχ t with h | h <;> simp [c, boolSign, h]
    apply Set.mem_iUnion.mpr
    refine ⟨c, ?_⟩
    intro x hx y hy
    simpa only [hc] using hsmall x hx y hy
  · intro hX
    obtain ⟨χ, hχ⟩ := Set.mem_iUnion.mp hX
    exact ⟨fun t => boolSign (χ t), fun t => boolSign_pm _, hχ⟩

/-- A per-coloring bound holds uniformly over all sample-dependent choices of
coloring after multiplication by exactly `2^n`. Measurability of each bad event
is not required: the inequality uses outer measure. -/
theorem badSet_measure_le_of_fixedColor (n : ℕ) (b : ℝ) (q : ℝ≥0∞)
    (hfixed : ∀ χ : Fin n → Bool, unifPts n (fixedColorBad n b χ) ≤ q) :
    unifPts n (badSet n b) ≤ (2 : ℝ≥0∞) ^ n * q := by
  rw [badSet_eq_iUnion_fixedColorBad]
  calc unifPts n (⋃ χ : Fin n → Bool, fixedColorBad n b χ)
      ≤ ∑ χ : Fin n → Bool, unifPts n (fixedColorBad n b χ) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _χ : Fin n → Bool, q := Finset.sum_le_sum (fun χ _ => hfixed χ)
    _ = (2 : ℝ≥0∞) ^ n * q := by simp

end
end Riesz.PointSets
