import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-!
# The one-dimensional profile used in the direct Riesz proof

`profile` is the primitive `w` from Section 2 of the manuscript.  It is extended by
zero outside the unit interval.  The lemmas in this file establish its actual
pointwise and integral properties; they are not hypotheses of a surrogate model.
-/

namespace Riesz

noncomputable section

/-- The continuous, mean-zero primitive of the four-quarter wavelet. -/
def profile (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x ≤ 1 / 4 then x else
    if x ≤ 3 / 4 then 1 / 2 - x else if x ≤ 1 then x - 1 else 0

lemma profile_zero : profile 0 = 0 := by simp [profile]
lemma profile_one : profile 1 = 0 := by norm_num [profile]

lemma profile_of_nonpos {x : ℝ} (hx : x ≤ 0) : profile x = 0 := by
  simp [profile, hx]

lemma profile_of_one_le {x : ℝ} (hx : 1 ≤ x) : profile x = 0 := by
  unfold profile
  split_ifs <;> linarith

lemma abs_profile_le (x : ℝ) : |profile x| ≤ 1 / 4 := by
  unfold profile
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma profile_reflect (x : ℝ) : profile (1 - x) = -profile x := by
  unfold profile
  split_ifs <;> linarith

lemma abs_profile_sub_le (x y : ℝ) : |profile x - profile y| ≤ |x - y| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    unfold profile
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    unfold profile
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma profile_lipschitz : LipschitzWith 1 profile := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa [Real.dist_eq] using abs_profile_sub_le x y

lemma profile_continuous : Continuous profile := profile_lipschitz.continuous

lemma integral_profile_zero : (∫ x in (0 : ℝ)..1, profile x) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) profile 1
  simp only [sub_self, sub_zero, profile_reflect, intervalIntegral.integral_neg] at h
  linarith

lemma profile_first_quarter {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / 4)) :
    profile x = x := by
  unfold profile
  split_ifs <;> rcases hx with ⟨_, _⟩ <;> linarith

lemma profile_middle_half {x : ℝ} (hx : x ∈ Set.Icc (1 / 4) (3 / 4)) :
    profile x = 1 / 2 - x := by
  unfold profile
  split_ifs <;> rcases hx with ⟨_, _⟩ <;> linarith

lemma profile_last_quarter {x : ℝ} (hx : x ∈ Set.Icc (3 / 4) 1) :
    profile x = x - 1 := by
  unfold profile
  split_ifs <;> rcases hx with ⟨_, _⟩ <;> linarith

lemma integral_profile_left_half : (∫ x in (0 : ℝ)..(1 / 2), profile x) = 1 / 16 := by
  have hfirst : (∫ x in (0 : ℝ)..(1 / 4), profile x) = 1 / 32 := by
    calc (∫ x in (0 : ℝ)..(1 / 4), profile x) = ∫ x in (0 : ℝ)..(1 / 4), x := by
          apply intervalIntegral.integral_congr
          intro x hx
          apply profile_first_quarter
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)] using hx
      _ = 1 / 32 := by norm_num [integral_id]
  have hsecond : (∫ x in (1 / 4 : ℝ)..(1 / 2), profile x) = 1 / 32 := by
    calc (∫ x in (1 / 4 : ℝ)..(1 / 2), profile x) =
          ∫ x in (1 / 4 : ℝ)..(1 / 2), 1 / 2 - x := by
          apply intervalIntegral.integral_congr
          intro x hx
          apply profile_middle_half
          simp only [Set.uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2), Set.mem_Icc] at hx
          exact ⟨hx.1, by linarith [hx.2]⟩
      _ = 1 / 32 := by
          rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 / 2 : ℝ))
            (g := fun x : ℝ => x) (continuous_const.intervalIntegrable _ _)
            (continuous_id.intervalIntegrable _ _)]
          norm_num [integral_id]
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (profile_continuous.intervalIntegrable (0 : ℝ) (1 / 4))
    (profile_continuous.intervalIntegrable (1 / 4 : ℝ) (1 / 2))
  linarith

lemma integral_profile_right_half : (∫ x in (1 / 2 : ℝ)..1, profile x) = -(1 / 16) := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (profile_continuous.intervalIntegrable (0 : ℝ) (1 / 2))
    (profile_continuous.intervalIntegrable (1 / 2 : ℝ) 1)
  rw [integral_profile_zero, integral_profile_left_half] at hsum
  linarith

end
end Riesz

namespace Riesz
noncomputable section
open Finset

/-- Values of the averaged profile in the four quarters, at a fixed local offset. -/
def quarterValue (q : Fin 4) (z : ℝ) : ℝ :=
  if q = 0 then z else if q = 1 then 1 / 4 - z else
    if q = 2 then -z else z - 1 / 4

lemma profile_quarterValue (q : Fin 4) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 4) :
    profile ((q : ℕ) / 4 + z) = quarterValue q z := by
  fin_cases q <;> norm_num [quarterValue] <;> unfold profile <;> split_ifs <;> linarith

lemma abs_quarterValue (q : Fin 4) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 4) :
    |quarterValue q z| ≤ 1 / 4 := by
  rw [← profile_quarterValue q hz0 hz1]
  exact abs_profile_le _

/-- The average over the first two binary digits. -/
def quarterMean (z : ℝ) (f : ℝ → ℝ) : ℝ := (∑ q : Fin 4, f (quarterValue q z)) / 4

lemma quarterMean_id (z : ℝ) : quarterMean z id = 0 := by
  norm_num [quarterMean, Fin.sum_univ_succ, quarterValue]
  ring

lemma quarterMean_sq (z : ℝ) :
    quarterMean z (fun x => x ^ 2) = (z ^ 2 + (1 / 4 - z) ^ 2) / 2 := by
  norm_num [quarterMean, Fin.sum_univ_succ, quarterValue]
  ring

lemma quarterMean_sq_lower (z : ℝ) : 1 / 64 ≤ quarterMean z (fun x => x ^ 2) := by
  rw [quarterMean_sq]
  nlinarith [sq_nonneg (z - 1 / 8)]

lemma quarterMean_fourth_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 4) :
    quarterMean z (fun x => x ^ 4) ≤ (1 / 16) * quarterMean z (fun x => x ^ 2) := by
  unfold quarterMean
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro q _
  have hq := abs_quarterValue q hz0 hz1
  have hs : (quarterValue q z) ^ 2 ≤ 1 / 16 := by
    have hlo := (abs_le.mp hq).1
    have hhi := (abs_le.mp hq).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi)
      (show 0 ≤ quarterValue q z + 1 / 4 by linarith)]
  nlinarith [sq_nonneg (quarterValue q z),
    mul_nonneg (sq_nonneg (quarterValue q z)) (sub_nonneg.mpr hs)]

/-- The midpoint of one of `m` equal cells in a quarter of the unit interval. -/
def quarterMidpoint (m : ℕ) (r : Fin m) : ℝ := ((r : ℕ) + 1 / 2) / (4 * m)

lemma quarterMidpoint_bounds {m : ℕ} (r : Fin m) :
    0 ≤ quarterMidpoint m r ∧ quarterMidpoint m r ≤ 1 / 4 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast r.pos
  have hr : (r : ℝ) < m := by exact_mod_cast r.isLt
  unfold quarterMidpoint
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity)]
    have hr' : (r : ℝ) + 1 ≤ m := by exact_mod_cast r.isLt
    linarith

/-- Uniform expectation of the `4m` possible averaged profile values.  For depth
`L ≥ 2`, the manuscript uses `m = 2^(L-2)`. -/
def blockMean (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∑ r : Fin m, quarterMean (quarterMidpoint m r) f) / m

lemma blockMean_id (m : ℕ) : blockMean m id = 0 := by
  simp [blockMean, quarterMean_id]

lemma blockMean_sq_lower {m : ℕ} (hm : 0 < m) :
    1 / 64 ≤ blockMean m (fun x => x ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold blockMean
  rw [le_div_iff₀ hm']
  calc (1 / 64 : ℝ) * m = ∑ _r : Fin m, (1 / 64 : ℝ) := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun r _ => quarterMean_sq_lower _)

lemma blockMean_fourth_le_second (m : ℕ) :
    blockMean m (fun x => x ^ 4) ≤ (1 / 16) * blockMean m (fun x => x ^ 2) := by
  unfold blockMean
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  apply Finset.sum_le_sum
  intro r _
  exact quarterMean_fourth_le (quarterMidpoint_bounds r).1 (quarterMidpoint_bounds r).2

lemma blockMean_fourth_le {m : ℕ} (hm : 0 < m) :
    blockMean m (fun x => x ^ 4) ≤ 4 * (blockMean m (fun x => x ^ 2)) ^ 2 := by
  have h2 := blockMean_sq_lower hm
  have h4 := blockMean_fourth_le_second m
  nlinarith

end
end Riesz

namespace Riesz
noncomputable section

lemma quarterValue_affine (q : Fin 4) (z : ℝ) :
    quarterValue q z = (quarterValue q 1 - quarterValue q 0) * z + quarterValue q 0 := by
  fin_cases q <;> norm_num [quarterValue] <;> ring

lemma integral_affine (a b s c : ℝ) :
    (∫ x in a..b, s * x + c) = (b - a) * (s * ((a + b) / 2) + c) := by
  rw [intervalIntegral.integral_add (f := fun x : ℝ => s * x) (g := fun _ : ℝ => c)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Every cell lying in one quarter sees an affine profile, so its average is
exactly the midpoint value. This identifies the finite profile distribution
with the cell averages in the manuscript, rather than a different discretization. -/
lemma integral_profile_quarter (q : Fin 4) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 4) :
    (∫ x in (q : ℕ) / 4 + a..(q : ℕ) / 4 + b, profile x) =
      (b - a) * quarterValue q ((a + b) / 2) := by
  have hfun : ∀ x ∈ Set.uIcc ((q : ℕ) / 4 + a : ℝ) ((q : ℕ) / 4 + b),
      profile x = (quarterValue q 1 - quarterValue q 0) *
        (x - (q : ℕ) / 4) + quarterValue q 0 := by
    intro x hx
    simp only [Set.uIcc_of_le (by linarith : ((q : ℕ) / 4 + a : ℝ) ≤ (q : ℕ) / 4 + b),
      Set.mem_Icc] at hx
    have hz0 : 0 ≤ x - (q : ℕ) / 4 := by linarith [hx.1]
    have hz1 : x - (q : ℕ) / 4 ≤ 1 / 4 := by linarith [hx.2]
    have hp := profile_quarterValue q hz0 hz1
    rw [show ((q : ℕ) / 4 : ℝ) + (x - (q : ℕ) / 4) = x by ring] at hp
    exact hp.trans (quarterValue_affine q _)
  calc (∫ x in (q : ℕ) / 4 + a..(q : ℕ) / 4 + b, profile x) =
        ∫ x in (q : ℕ) / 4 + a..(q : ℕ) / 4 + b,
          (quarterValue q 1 - quarterValue q 0) * x +
          (quarterValue q 0 - (quarterValue q 1 - quarterValue q 0) * ((q : ℕ) / 4)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [hfun x hx]
          ring
    _ = (b - a) * quarterValue q ((a + b) / 2) := by
          rw [integral_affine, quarterValue_affine q ((a + b) / 2)]
          ring

lemma profile_cell_average {m : ℕ} (q : Fin 4) (r : Fin m) :
    (4 * m : ℝ) *
      (∫ x in (q : ℕ) / 4 + (r : ℕ) / (4 * m)..
        (q : ℕ) / 4 + ((r : ℕ) + 1) / (4 * m), profile x) =
      quarterValue q (quarterMidpoint m r) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast r.pos
  have ha : (0 : ℝ) ≤ (r : ℕ) / (4 * m) := by positivity
  have hab : ((r : ℕ) : ℝ) / (4 * m) ≤ ((r : ℕ) + 1) / (4 * m) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hb : (((r : ℕ) + 1) : ℝ) / (4 * m) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hr : (r : ℝ) + 1 ≤ m := by exact_mod_cast r.isLt
    linarith
  rw [integral_profile_quarter q ha hab hb]
  have hmid : (((r : ℕ) : ℝ) / (4 * m) + ((r : ℕ) + 1) / (4 * m)) / 2 =
      quarterMidpoint m r := by unfold quarterMidpoint; ring
  rw [hmid]
  have hlen : (4 * m : ℝ) * (((r : ℕ) + 1) / (4 * m) - (r : ℕ) / (4 * m)) = 1 := by
    field_simp
    ring
  rw [← mul_assoc, hlen, one_mul]

end
end Riesz
