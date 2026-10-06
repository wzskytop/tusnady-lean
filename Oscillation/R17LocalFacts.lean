import Oscillation.Rademacher

namespace Oscillation
noncomputable section
open Finset Riesz.Moments
set_option maxHeartbeats 1000000

/-- The algebraic range comparison in r17 Lemma 2.1. No parity condition. -/
theorem midpoint_range_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a z : ι) (haz : a≠z) (lo hi : ι → ℝ) (L U : ℝ)
    (hlo : ∀ i,L≤lo i) (hhi : ∀ i,hi i≤U) :
    (∑ i,(hi i-lo i))+2*|(hi z+lo z)/2-(hi a+lo a)/2| ≤ Fintype.card ι*(U-L) := by
  let gap := fun i => U-L-(hi i-lo i)
  have hg (i) : 0≤gap i := by dsimp [gap]; linarith [hlo i,hhi i]
  have hpair : gap a+gap z ≤ ∑i,gap i := by
    have H := sum_le_sum_of_subset_of_nonneg (show ({a,z}:Finset ι)⊆univ by simp)
      (fun i _ _ => hg i)
    simpa [haz] using H
  have hm : 2*|(hi z+lo z)/2-(hi a+lo a)/2|≤gap a+gap z := by
    rcases le_total 0 ((hi z+lo z)/2-(hi a+lo a)/2) with H|H
    · rw [abs_of_nonneg H]; dsimp [gap]; linarith [hlo a,hhi z]
    · rw [abs_of_nonpos H]; dsimp [gap]; linarith [hlo z,hhi a]
  have he : (∑ i,gap i)=Fintype.card ι*(U-L)-(∑ i,(hi i-lo i)) := by
    simp only [gap,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul]
    ring
  rw [he] at hpair
  linarith

/-- The sharp moment constant used in Fact 2.3, for a finite law. -/
lemma abs_mean_of_fourth_three {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (X : Ω → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hsecond : expectation μ (fun x ↦ X x ^ 2) = v)
    (hfourth : expectation μ (fun x ↦ X x ^ 4) ≤ 3 * v ^ 2) :
    Real.sqrt (v/3) ≤ expectation μ (fun x ↦ |X x|) := by
  let A := expectation μ (fun x ↦ |X x|)
  let B := expectation μ (fun x ↦ |X x| ^ 3)
  have hA : 0 ≤ A := expectation_nonneg μ (fun _ ↦ abs_nonneg _)
  have hB : 0 ≤ B := expectation_nonneg μ (fun _ ↦ by positivity)
  have hcs₁ : v ^ 2 ≤ A * B := by
    rw [← hsecond]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun x _ ↦ mul_nonneg (μ.nonneg x) (abs_nonneg _))
      (fun x _ ↦ mul_nonneg (μ.nonneg x) (by positivity))
    intro x _
    rcases le_total 0 (X x) with hx | hx
    · simp only [abs_of_nonneg hx]; exact le_of_eq (by ring)
    · simp only [abs_of_nonpos hx]; exact le_of_eq (by ring)
  have hcs₂ : B ^ 2 ≤ v * (3 * v ^ 2) := by
    have hc : B ^ 2 ≤ expectation μ (fun x ↦ X x ^ 2) *
        expectation μ (fun x ↦ X x ^ 4) := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (fun x _ ↦ mul_nonneg (μ.nonneg x) (sq_nonneg _))
        (fun x _ ↦ mul_nonneg (μ.nonneg x) (by positivity))
      intro x _
      rcases le_total 0 (X x) with hx | hx
      · simp only [abs_of_nonneg hx]; exact le_of_eq (by ring)
      · simp only [abs_of_nonpos hx]; exact le_of_eq (by ring)
    rw [hsecond] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hfourth hv)
  have hs := Real.sq_sqrt (show 0≤v/3 by positivity)
  have hroot := Real.sqrt_nonneg (v/3)
  by_cases hv0 : v = 0
  · simpa [hv0] using hA
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have hsq : v ^ 4 ≤ A ^ 2 * B ^ 2 := by
    nlinarith [sq_nonneg (A * B - v ^ 2)]
  have hmul := mul_le_mul_of_nonneg_left hcs₂ (sq_nonneg A)
  have hrel : v ≤ 3 * A ^ 2 := by
    have hv3 : 0 < v ^ 3 := by positivity
    apply (mul_le_mul_iff_left₀ hv3).mp
    nlinarith [hsq, hmul]
  change Real.sqrt (v/3) ≤ A
  nlinarith


end
end Oscillation
