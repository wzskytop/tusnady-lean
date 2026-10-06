import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite moment and Laplace bounds

The conditional distribution in the one-rectangle argument is finite: after the
old digits and vertical weights are fixed, the new horizontal digits range over
finitely many possibilities.  The theorems below apply to arbitrary finite
probability weights, not just the uniform distribution.
-/

namespace Riesz.Moments

open scoped BigOperators

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

variable {Ω : Type*} [Fintype Ω]

noncomputable def expectation (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * X ω

noncomputable def probability (μ : FiniteLaw Ω) (A : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if A ω then μ.weight ω else 0

lemma expectation_nonneg (μ : FiniteLaw Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) :
    0 ≤ expectation μ X :=
  Finset.sum_nonneg fun ω _ ↦ mul_nonneg (μ.nonneg ω) (h ω)

lemma expectation_mono (μ : FiniteLaw Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    expectation μ X ≤ expectation μ Y :=
  Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω)

@[simp] lemma expectation_const (μ : FiniteLaw Ω) (a : ℝ) :
    expectation μ (fun _ ↦ a) = a := by
  simp only [expectation, ← Finset.sum_mul, μ.total, one_mul]

lemma probability_nonneg (μ : FiniteLaw Ω) (A : Ω → Prop) :
    0 ≤ probability μ A := by
  classical
  exact Finset.sum_nonneg fun ω _ ↦ by
    split_ifs <;> simp_all [μ.nonneg]

lemma probability_le_one (μ : FiniteLaw Ω) (A : Ω → Prop) :
    probability μ A ≤ 1 := by
  classical
  calc
    probability μ A ≤ ∑ ω, μ.weight ω := by
      apply Finset.sum_le_sum
      intro ω _
      split_ifs <;> simp_all [μ.nonneg]
    _ = 1 := μ.total

/-- The one-sixteenth lower-tail bound requires only the second and fourth
moments. Centering and independence are needed to establish those moments for
a weighted sum, but are not extra assumptions of this implication. -/
theorem small_ball_of_fourth_moment (μ : FiniteLaw Ω) (X : Ω → ℝ) (v : ℝ)
    (hv : 0 < v) (hsecond : expectation μ (fun ω ↦ X ω ^ 2) = v)
    (hfourth : expectation μ (fun ω ↦ X ω ^ 4) ≤ 4 * v ^ 2) :
    (1 / 16 : ℝ) ≤ probability μ (fun ω ↦ v / 2 ≤ X ω ^ 2) := by
  classical
  let A : Ω → Prop := fun ω ↦ v / 2 ≤ X ω ^ 2
  let q := probability μ A
  let T : ℝ := ∑ ω, if A ω then μ.weight ω * X ω ^ 2 else 0
  have hq : 0 ≤ q := probability_nonneg μ A
  have hvT : v ≤ v / 2 + T := by
    calc
      v = ∑ ω, μ.weight ω * X ω ^ 2 := hsecond.symm
      _ ≤ ∑ ω, (μ.weight ω * (v / 2) +
          if A ω then μ.weight ω * X ω ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases ha : A ω
        · simp only [ha, ite_true]
          have := mul_nonneg (μ.nonneg ω) (le_of_lt hv)
          nlinarith
        · simp only [ha, ite_false, add_zero]
          exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge ha)) (μ.nonneg ω)
      _ = v / 2 + T := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, μ.total, one_mul]
  have hcs : T ^ 2 ≤ q * expectation μ (fun ω ↦ X ω ^ 4) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun ω _ ↦ by split_ifs <;> simp_all [μ.nonneg])
      (fun ω _ ↦ mul_nonneg (μ.nonneg ω) (by positivity))
    intro ω _
    by_cases ha : A ω <;> simp only [ha, ite_true, ite_false]
    · nlinarith [sq_nonneg (μ.weight ω * X ω ^ 2)]
    · simp
  have hcs' : T ^ 2 ≤ q * (4 * v ^ 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hfourth hq)
  have hT : 0 ≤ T := by linarith
  have hT2 : (v / 2) ^ 2 ≤ T ^ 2 := by nlinarith
  change (1 / 16 : ℝ) ≤ q
  by_contra hn
  have hq' : q < 1 / 16 := lt_of_not_ge hn
  have hp : 0 < v ^ 2 := sq_pos_of_pos hv
  have := mul_lt_mul_of_pos_right hq' hp
  nlinarith


/-- A finite probability lower bound yields the elementary Laplace bound. -/
theorem laplace_le_of_small_ball (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (a t p : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hprob : p ≤ probability μ (fun ω ↦ a ≤ |X ω|)) :
    expectation μ (fun ω ↦ Real.exp (-t * |X ω|)) ≤
      1 - p * (1 - Real.exp (-t * a)) := by
  classical
  let A : Ω → Prop := fun ω ↦ a ≤ |X ω|
  have he : Real.exp (-t * a) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpoint (ω : Ω) : Real.exp (-t * |X ω|) ≤
      1 - if A ω then (1 - Real.exp (-t * a)) else 0 := by
    by_cases h : A ω
    · simp only [h, ite_true, sub_sub_cancel]
      apply Real.exp_le_exp.mpr
      change a ≤ |X ω| at h
      nlinarith
    · simp only [h, ite_false, sub_zero]
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have := abs_nonneg (X ω)
      nlinarith
  calc
    expectation μ (fun ω ↦ Real.exp (-t * |X ω|)) ≤
        expectation μ (fun ω ↦ 1 - if A ω then (1 - Real.exp (-t * a)) else 0) :=
      expectation_mono μ hpoint
    _ = 1 - probability μ A * (1 - Real.exp (-t * a)) := by
      unfold expectation probability
      simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [μ.total, Finset.sum_mul]
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : A ω <;> simp [h, mul_sub]
    _ ≤ 1 - p * (1 - Real.exp (-t * a)) := by
      have := mul_le_mul_of_nonneg_right hprob (sub_nonneg.mpr he)
      linarith

lemma exp_neg_linear_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    z / 2 ≤ 1 - Real.exp (-z) := by
  have hprod : (1 + z) * Real.exp (-z) ≤ 1 := by
    calc
      (1 + z) * Real.exp (-z) ≤ Real.exp z * Real.exp (-z) := by
        exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp z])
          (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  have hpoly : 1 ≤ (1 + z) * (1 - z / 2) := by nlinarith
  have hle : Real.exp (-z) ≤ 1 - z / 2 := by
    apply le_of_mul_le_mul_left (a := 1 + z)
    · exact hprod.trans hpoly
    · linarith
  linarith

/-- Second and fourth moment hypotheses imply Laplace contraction at any
threshold below the Paley--Zygmund threshold. -/
theorem laplace_le_exp_of_fourth_moment (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (v a t : ℝ) (hv : 0 < v) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (ha2 : a ^ 2 ≤ v / 2) (hat : a * t ≤ 1)
    (hsecond : expectation μ (fun ω ↦ X ω ^ 2) = v)
    (hfourth : expectation μ (fun ω ↦ X ω ^ 4) ≤ 4 * v ^ 2) :
    expectation μ (fun ω ↦ Real.exp (-t * |X ω|)) ≤
      Real.exp (-(a * t) / 32) := by
  classical
  have hprob : (1 / 16 : ℝ) ≤ probability μ (fun ω ↦ a ≤ |X ω|) := by
    apply (small_ball_of_fourth_moment μ X v hv hsecond hfourth).trans
    apply Finset.sum_le_sum
    intro ω _
    by_cases h : v / 2 ≤ X ω ^ 2
    · have haX : a ≤ |X ω| := by
        have hs : |X ω| ^ 2 = X ω ^ 2 := sq_abs _
        have hp := abs_nonneg (X ω)
        nlinarith
      simp [h, haX]
    · simp only [h, ite_false]
      split_ifs <;> simp_all [μ.nonneg]
  have he := laplace_le_of_small_ball μ X a t (1 / 16) ha ht hprob
  have hlinear := exp_neg_linear_bound (mul_nonneg ha ht) hat
  have he' : expectation μ (fun ω ↦ Real.exp (-t * |X ω|)) ≤
      1 - a * t / 32 := by
    rw [neg_mul, mul_comm t a] at he
    nlinarith
  apply he'.trans
  have := Real.add_one_le_exp (-(a * t) / 32)
  linarith


/-- Normalized form convenient for the one-rectangle coefficient estimate. -/
theorem laplace_normalized_of_fourth_moment (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (v lam z : ℝ) (hv : 0 < v) (hlam : 0 < lam) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hzv : z ^ 2 * lam ≤ v / 2)
    (hsecond : expectation μ (fun ω ↦ X ω ^ 2) = v)
    (hfourth : expectation μ (fun ω ↦ X ω ^ 4) ≤ 4 * v ^ 2) :
    expectation μ (fun ω ↦ Real.exp (-|X ω| / Real.sqrt lam)) ≤
      Real.exp (-z / 32) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hprod : (z * Real.sqrt lam) * (1 / Real.sqrt lam) = z := by field_simp
  have hsq : (z * Real.sqrt lam) ^ 2 ≤ v / 2 := by
    simpa [mul_pow, Real.sq_sqrt hlam.le] using hzv
  have hh := laplace_le_exp_of_fourth_moment μ X v (z * Real.sqrt lam)
    (1 / Real.sqrt lam) hv (mul_nonneg hz hs.le) (by positivity) hsq
    (by rw [hprod]; exact hz1) hsecond hfourth
  rw [hprod] at hh
  convert hh using 1
  congr 1
  funext ω
  congr 1
  ring

/-- The constants in the paper's one-rectangle Laplace estimate.
Here `r` is the ratio `g / lam`; the bound on `b` is written as
`1 / (512 * C * sqrt C)`, equal to `1 / (512 * C^(3/2))` for positive `C`.
The proof uses the slightly smaller normalized threshold `sqrt r / (16*C)`;
this still gives the paper's final exponential bound with the same constant. -/
theorem laplace_le_exp_of_weight_ratio (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (v lam C r b : ℝ) (hlam : 0 < lam) (hC : 1 ≤ C) (hr : 0 ≤ r) (hrC : r ≤ C)
    (hb : 0 ≤ b) (hbC : b ≤ 1 / (512 * C * Real.sqrt C))
    (hsecond : expectation μ (fun ω ↦ X ω ^ 2) = v)
    (hfourth : expectation μ (fun ω ↦ X ω ^ 4) ≤ 4 * v ^ 2)
    (hvlow : lam * r / (64 * C ^ 2) ≤ v) :
    expectation μ (fun ω ↦ Real.exp (-|X ω| / Real.sqrt lam)) ≤ Real.exp (-b * r) := by
  have hCp : 0 < C := by linarith
  have hCs : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCp
  by_cases hrz : r = 0
  · simp only [hrz, mul_zero, Real.exp_zero]
    calc
      expectation μ (fun ω ↦ Real.exp (-|X ω| / Real.sqrt lam)) ≤
          expectation μ (fun _ ↦ (1 : ℝ)) := by
        apply expectation_mono
        intro ω
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _))
          (Real.sqrt_nonneg _)
      _ = 1 := expectation_const μ 1
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hrz)
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hvlow
  let z := Real.sqrt r / (16 * C)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hroot : Real.sqrt r ≤ Real.sqrt C := Real.sqrt_le_sqrt hrC
  have hrootC : Real.sqrt C ≤ C := Real.sqrt_le_self_iff.mpr (Or.inr hC)
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ (by positivity : 0 < 16 * C)).mpr
    nlinarith
  have hzsq : z ^ 2 = r / (256 * C ^ 2) := by
    dsimp [z]
    rw [div_pow, Real.sq_sqrt hr]
    ring
  have hzv : z ^ 2 * lam ≤ v / 2 := by
    rw [hzsq]
    calc
      r / (256 * C ^ 2) * lam = (lam * r / (64 * C ^ 2)) / 4 := by ring
      _ ≤ v / 4 := div_le_div_of_nonneg_right hvlow (by norm_num)
      _ ≤ v / 2 := by linarith
  have hbroot : b * Real.sqrt C ≤ 1 / (512 * C) := by
    apply (le_div_iff₀ (by positivity : 0 < 512 * C)).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 512 * C * Real.sqrt C)).mp hbC
    nlinarith
  have hrroot : r ≤ Real.sqrt C * Real.sqrt r := by
    calc
      r = Real.sqrt r * Real.sqrt r := (Real.mul_self_sqrt hr).symm
      _ ≤ Real.sqrt C * Real.sqrt r :=
        mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg r)
  have hbr : b * r ≤ z / 32 := by
    calc
      b * r ≤ b * (Real.sqrt C * Real.sqrt r) := mul_le_mul_of_nonneg_left hrroot hb
      _ = (b * Real.sqrt C) * Real.sqrt r := by ring
      _ ≤ (1 / (512 * C)) * Real.sqrt r :=
        mul_le_mul_of_nonneg_right hbroot (Real.sqrt_nonneg _)
      _ = z / 32 := by dsimp [z]; ring
  apply (laplace_normalized_of_fourth_moment μ X v lam z hv hlam hz hz1 hzv
    hsecond hfourth).trans
  apply Real.exp_le_exp.mpr
  nlinarith


/-- The final one-rectangle estimate with the paper's parameters, including
`g = 0`. The variance and fourth-moment hypotheses are explicit inputs. -/
theorem one_rectangle_laplace (μ : FiniteLaw Ω) (S : Ω → ℝ)
    (v lam C g b : ℝ) (hlam : 1 ≤ lam) (hC : 20 < C)
    (hg : 0 ≤ g) (hgC : g / lam ≤ C)
    (hb : 0 < b) (hbC : b ≤ 1 / (512 * C ^ (3 / 2 : ℝ)))
    (hsecond : expectation μ (fun ω ↦ S ω ^ 2) = v)
    (hfourth : expectation μ (fun ω ↦ S ω ^ 4) ≤ 4 * v ^ 2)
    (hvlow : g / (64 * C ^ 2) ≤ v) :
    expectation μ (fun ω ↦ Real.exp (-|S ω| / Real.sqrt lam)) ≤
      Real.exp (-b * g / lam) := by
  have hlampos : 0 < lam := by linarith
  have hCpos : 0 < C := by linarith
  have hpow : C ^ (3 / 2 : ℝ) = C * Real.sqrt C := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hCpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hbC' : b ≤ 1 / (512 * C * Real.sqrt C) := by
    simpa [hpow, mul_assoc] using hbC
  have hvlow' : lam * (g / lam) / (64 * C ^ 2) ≤ v := by
    have heq : lam * (g / lam) = g := by field_simp
    simpa [heq] using hvlow
  have hh := laplace_le_exp_of_weight_ratio μ S v lam C (g / lam) b
    hlampos (by linarith) (div_nonneg hg hlampos.le) hgC hb.le hbC'
    hsecond hfourth hvlow'
  convert hh using 1
  congr 1
  ring

end Riesz.Moments
