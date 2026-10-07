import R56Audit.Simultaneous
import R56Audit.ArchiveInterface

/-!
# Section 2.5 of the manuscript (Parameters): the proof of Theorem 1.1

Auditor's supplement (not part of the audited archive).

This file proves Theorem 1.1 from Proposition 2.7 (`proposition_2_7` in `Simultaneous.lean`)
as the manuscript does, and then the lower bound of Corollary 1.2.

## The proof of Theorem 1.1, sentence by sentence

Each sentence of the manuscript's proof is followed by the declarations that state it. Every
(in)equality of the proof is stated by one of them. In particular every link of a chain of
(in)equalities is stated, and the theorem that states the two ends of a chain is proved from
its links. The number `M` is always written out as `b ^ (h - 1)`; (14) is the display of
Proposition 2.7.

**The base, the constant and the scale.**

* "Choose an integer `b` so large that" (15) holds. This is `exists_base_of_15`. The two
  conditions of (15), `(1/2) log(b/48) ≥ A + 2` and `b/4096 ≥ A + 2 + log 2`, are the
  hypotheses `hb1` and `hb2` of the statements below.
* "Such a choice depends only on `A`, and it forces `b > 48`, so that `64 ≤ b^4`." The two
  inequalities are `base_ge_49` and `sixty_four_le_pow_four`. That the choice depends only on
  `A` is the order of the quantifiers in `theorem_1_1`: the base, and with it the constant, is
  chosen before `n`.
* "Set `c_A = b^{-8}/(1 + log₂ b)^{3/2}`." This is the definition `cA`; see `cA_pos`.
* "Let `h ≥ 1` be the largest integer with `b^{-5} h b^{h-1} ≤ n`, and set `M = b^{h-1}`."
  These are the definitions `ScaleOK` (the condition) and `IsScale`.
* "Such an `h` exists, since `h = 1` satisfies the condition and the left-hand side tends to
  infinity with `h`." This is `exists_isScale`, proved from `scaleOK_one` and `le_of_scaleOK`.
* "By maximality, `n < b^{-5}(h+1) b^h`." This is `lt_of_isScale`.
* "With `h + 1 ≤ 2h` and `b^h = bM` this gives" (16). These are `scale_succ_le_two_mul`,
  `base_pow_eq_mul_pow` and `display_16`.
* "and with `h + 1 ≤ 2^h` and `b^{-5} ≤ 1` it gives `n < (2b)^h`, that is," (17). These are
  `scale_succ_le_two_pow`, `inv_pow_five_le_one`, `lt_two_mul_pow_of_isScale` and `display_17`.
* "By (17) and the definition of `c_A`," (18). This is `display_18`.

**The case `M > n`.**

* "Proposition 2.7 needs `M ≤ n`." This is not a claim to be proved: `M ≤ n` is the hypothesis
  `hMn` of `proposition_2_7`.
* "If `M > n`, then (16) gives `b^{-5} h < 1`, that is, `h < b^5`, and (18) gives
  `c_A (log₂ n)^{3/2} < b^{-8} b^{15/2} < 1`." These are `scale_div_pow_five_lt_one`,
  `scale_lt_pow_five`, `cA_mul_lt_of_lt` and `inv_pow_eight_mul_rpow_lt_one`; the two ends of
  the last chain are `cA_mul_lt_one`.
* "So it suffices to find an anchored rectangle that has imbalance `1` under every coloring.
  The rectangle `[0,1] × [0, min_i V_i]` is one, because it contains just the lowest point,
  which is unique since all heights are distinct." The rectangle is `one_le_supNorm` in
  `SupNorm.lean`; its hypotheses hold almost surely, which gives `ae_one_le_supNorm`.
* "So in this case the claim of the theorem holds with probability one." This is
  `ae_cA_mul_lt_supNorm`; the reduction to imbalance `1` is its proof.

**The case `M ≤ n`.**

* "So assume that `M ≤ n`. Then Proposition 2.7 applies." `proposition_2_7` is applied in
  `prob_exists_supNorm_le_of_pow_le`.
* "Also `h ≤ 2^{h-1} ≤ M ≤ n`." The first two inequalities are `scale_le_two_pow` and
  `two_pow_le_base_pow`, the third is the assumption of the case, and the two ends are
  `scale_le_of_pow_le`.
* "By the first condition in (15), the first term on the right-hand side of (14) is at most
  `h e^{-(A+2)n} ≤ n e^{-(A+2)n}`." These are `first_term_le` (for the factor `(48/b)^{n/2}`
  alone) and `first_term_le_mul` (the two inequalities).
* "By (16) and the second condition, `hM/(2048 b³) > bn/4096 ≥ (A+2+log 2) n`, so the second
  term is at most `2^n e^{-(A+2+log 2)n}`, which equals `e^{-(A+2)n}`." These are
  `exponent_gt`, `exponent_ge`, `second_term_le_two_pow_mul` and `two_pow_mul_exp_eq`; the two
  ends are `second_term_le`.
* "The sum of the two terms is at most `(n+1) e^{-(A+2)n} ≤ e^{-An}`, since
  `n + 1 ≤ e^{2n}`." These are `sum_terms_le`, `add_one_mul_exp_le` and
  `add_one_le_exp_two_mul` (the last two for a real number `x ≥ 0` in place of `n`); the two
  ends are `failure_le`.
* "The threshold in (14) satisfies
  `(h/(64 b^{3/2})) √(n/M) ≥ (h/(64 b^{3/2})) √(h/b^5) = h^{3/2}/(64 b^4) ≥ b^{-8} h^{3/2} >
  c_A (log₂ n)^{3/2}`. The first inequality uses (16), the second uses `64 ≤ b^4`, and the
  last one is (18)." The four links are `threshold_ge_sqrt`, `threshold_sqrt_eq`,
  `rpow_div_ge` and `display_18`; the two ends are `threshold_gt`.
* "So by (14), with probability at least `1 - e^{-An}`, every coloring `χ` satisfies
  `‖F_χ‖∞ > c_A (log₂ n)^{3/2}`." This is `prob_exists_supNorm_le_of_pow_le`, stated for the
  complementary event.

## Theorem 1.1 and Corollary 1.2

`prob_exists_supNorm_le` puts the two cases together:
`Pr[∃ χ ∈ {±1}ⁿ : ‖F_χ‖∞ ≤ c_A (log₂ n)^{3/2}] ≤ e^{-An}`. The theorem follows:
`theorem_1_1_constant_event` (on a measurable event, with strict inequality, distinct points
in the unit square), `theorem_1_1_constant` (the display of the theorem, with the constant
`c_A` of the proof), `theorem_1_1` (as displayed) and `theorem_1_1_unfolded` (the same with
every definition unfolded). The lower bound of Corollary 1.2 is `exists_points` and
`corollary_1_2_lower`.

| Manuscript | Here |
| --- | --- |
| (15): `(1/2) log(b/48) ≥ A + 2`, `b/4096 ≥ A + 2 + log 2` | `hb1`, `hb2`; `exists_base_of_15` |
| `c_A = b^{-8}/(1 + log₂ b)^{3/2}` | `cA`, `cA_pos` |
| the largest `h ≥ 1` with `b^{-5} h b^{h-1} ≤ n` | `ScaleOK`, `IsScale`, `exists_isScale` |
| (16): `b^{-5} h M ≤ n < 2 b^{-4} h M` | `display_16` |
| (17): `log₂ n < (1 + log₂ b) h` | `display_17` |
| (18): `c_A (log₂ n)^{3/2} < b^{-8} h^{3/2}` | `display_18` |
| the case `M > n` | `cA_mul_lt_one`, `ae_one_le_supNorm`, `ae_cA_mul_lt_supNorm` |
| the case `M ≤ n` | `failure_le`, `threshold_gt`, `prob_exists_supNorm_le_of_pow_le` |
| Theorem 1.1: the probability of failure | `prob_exists_supNorm_le` |
| Theorem 1.1 with the constant `c_A` | `theorem_1_1_constant_event`, `theorem_1_1_constant` |
| Theorem 1.1 as displayed | `theorem_1_1`, `theorem_1_1_unfolded` |
| Corollary 1.2, lower bound | `exists_points`, `corollary_1_2_lower` |

**What is used of the archive.** In this file, nothing of the archive is used except the
measure `unifPts` (the law of `n` independent uniform points of the unit square; it is
Mathlib's product of the Lebesgue measure restricted to `[0,1]²`, see `theorem_1_1_unfolded`),
together with the archive's instance that this is a probability measure, and, for
Corollary 1.2 only, the archive's definition `Δ₂` of the worst-case discrepancy, through
`lt_Δ₂_of_supNorm` of `ArchiveInterface.lean`. The `open` lines below name `unifPts` and `Δ₂`.
In particular the archive's events `badSet` and `GoodEvent`, its `threshold`, its selection of
the scale and its arithmetic lemmas for the parameters do not occur. (The earlier files of the
manuscript route have their own module docstrings; the almost sure events `ae_inUnit` and
`ae_heights_injective` of `GoodTransitions.lean` are used here for the lowest point and for
the distinctness of the points.) The archive's own proof of Theorem 1.1 (base `2^L`) is
restated in `ArchiveRoute.lean` as `theorem_1_1_archive`.
-/

namespace R56Audit

open MeasureTheory
open Riesz.PointSets (unifPts Δ₂)

noncomputable section

/-! ### The base `b`, display (15) -/

/-- "Choose an integer `b` so large that" (15) holds: a base satisfying (15) exists for every
`A`. -/
lemma exists_base_of_15 (A : ℝ) :
    ∃ b : ℕ, A + 2 ≤ Real.log ((b : ℝ) / 48) / 2 ∧ A + 2 + Real.log 2 ≤ (b : ℝ) / 4096 := by
  obtain ⟨b, hb⟩ := exists_nat_ge
    (max (48 * Real.exp (2 * (A + 2))) (4096 * (A + 2 + Real.log 2)))
  refine ⟨b, ?_, ?_⟩
  · have h1 : 48 * Real.exp (2 * (A + 2)) ≤ b := (le_max_left _ _).trans hb
    have h2 : Real.exp (2 * (A + 2)) ≤ (b : ℝ) / 48 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    have h3 := Real.log_le_log (Real.exp_pos _) h2
    rw [Real.log_exp] at h3
    linarith
  · have h1 : 4096 * (A + 2 + Real.log 2) ≤ b := (le_max_right _ _).trans hb
    rw [le_div_iff₀ (by norm_num)]
    linarith

/-- "it forces `b > 48`": the first condition of (15) gives `log(b/48) > 0`. -/
lemma base_ge_49 {A : ℝ} (hA : 0 < A) {b : ℕ} (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) :
    49 ≤ b := by
  have hpos : 0 < Real.log ((b : ℝ) / 48) := by linarith
  have hq : (1 : ℝ) < (b : ℝ) / 48 := by
    by_contra hle
    have := Real.log_nonpos (by positivity : (0 : ℝ) ≤ (b : ℝ) / 48) (not_lt.mp hle)
    linarith
  have h48 : (48 : ℝ) < b := by
    have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 48)).mp hq
    linarith
  have : (48 : ℕ) < b := by exact_mod_cast h48
  omega

/-- "so that `64 ≤ b^4`". Already `b ≥ 3` suffices, because `3^4 = 81`; the threshold chain
(`rpow_div_ge`, `threshold_gt`) is stated for such `b`. -/
lemma sixty_four_le_pow_four {b : ℕ} (hb : 3 ≤ b) : (64 : ℝ) ≤ (b : ℝ) ^ 4 := by
  have hb3 : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have h81 : (3 : ℝ) ^ 4 ≤ (b : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hb3 4
  linarith

/-! ### The constant `c_A` -/

/-- The constant of Theorem 1.1: `c_A = b^{-8} / (1 + log₂ b)^{3/2}`. -/
def cA (b : ℕ) : ℝ := ((b : ℝ) ^ 8)⁻¹ / (1 + Real.logb 2 b) ^ (3 / 2 : ℝ)

/-- `1 + log₂ b > 0`. -/
lemma one_add_logb_pos {b : ℕ} (hb : 2 ≤ b) : 0 < 1 + Real.logb 2 b := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have := Real.logb_nonneg (b := 2) (by norm_num) hbR
  linarith

/-- `c_A > 0`. -/
lemma cA_pos {b : ℕ} (hb : 2 ≤ b) : 0 < cA b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hl := one_add_logb_pos hb
  unfold cA
  positivity

/-! ### The scale `h` -/

/-- `b^{-5} h b^{h-1} ≤ n`. -/
def ScaleOK (b n h : ℕ) : Prop := (h : ℝ) * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 5 ≤ n

/-- "Let `h ≥ 1` be the largest integer with `b^{-5} h b^{h-1} ≤ n`".

The maximality is stated over all natural numbers `h'`; for `h' = 0` the condition holds
trivially (the left-hand side is `0`), so this is the same as maximality over `h' ≥ 1`. -/
def IsScale (b n h : ℕ) : Prop := 1 ≤ h ∧ ScaleOK b n h ∧ ∀ h' : ℕ, ScaleOK b n h' → h' ≤ h

/-- "`h = 1` satisfies the condition": `b^{-5} ≤ 1 ≤ n`. -/
lemma scaleOK_one {b n : ℕ} (hb : 1 ≤ b) (hn : 1 ≤ n) : ScaleOK b n 1 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : (1 : ℝ) ≤ (b : ℝ) ^ 5 := one_le_pow₀ hbR
  unfold ScaleOK
  rw [Nat.sub_self, pow_zero, Nat.cast_one, mul_one]
  exact ((div_le_one (by positivity)).mpr h5).trans hnR

/-- A quantitative form of "the left-hand side tends to infinity with `h`": since
`h ≤ h b^{h-1}`, the condition `b^{-5} h b^{h-1} ≤ n` forces `h ≤ b⁵ n`. -/
lemma le_of_scaleOK {b n h : ℕ} (hb : 1 ≤ b) (hs : ScaleOK b n h) : h ≤ b ^ 5 * n := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hM : (1 : ℝ) ≤ (b : ℝ) ^ (h - 1) := one_le_pow₀ hbR
  have h1 : (h : ℝ) * (b : ℝ) ^ (h - 1) ≤ n * (b : ℝ) ^ 5 :=
    (div_le_iff₀ (by positivity)).mp hs
  have h2 : (h : ℝ) ≤ (h : ℝ) * (b : ℝ) ^ (h - 1) :=
    le_mul_of_one_le_right (Nat.cast_nonneg h) hM
  have h3 : (h : ℝ) ≤ ((b ^ 5 * n : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h3

/-- "Such an `h` exists, since `h = 1` satisfies the condition and the left-hand side tends to
infinity with `h`." -/
theorem exists_isScale {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) : ∃ h, IsScale b n h := by
  classical
  have hb1 : 1 ≤ b := by omega
  have h1 : ScaleOK b n 1 := scaleOK_one hb1 hn
  have h1le : 1 ≤ b ^ 5 * n := le_of_scaleOK hb1 h1
  -- the largest `h ≤ b⁵ n` satisfying the condition is the largest of all
  exact ⟨Nat.findGreatest (ScaleOK b n) (b ^ 5 * n), Nat.le_findGreatest h1le h1,
    Nat.findGreatest_spec h1le h1,
    fun h' hh' => Nat.le_findGreatest (le_of_scaleOK hb1 hh') hh'⟩

/-! ### The displays (16), (17) and (18) -/

/-- "By maximality, `n < b^{-5}(h+1) b^h`." -/
lemma lt_of_isScale {b n h : ℕ} (hs : IsScale b n h) :
    (n : ℝ) < ((h : ℝ) + 1) * (b : ℝ) ^ h / (b : ℝ) ^ 5 := by
  by_contra hcon
  -- otherwise `h + 1` satisfies the condition
  have hok : ScaleOK b n (h + 1) := by
    unfold ScaleOK
    rw [Nat.add_sub_cancel]
    push_cast
    exact not_lt.mp hcon
  have := hs.2.2 (h + 1) hok
  omega

/-- "`h + 1 ≤ 2h`", because `h ≥ 1`. -/
lemma scale_succ_le_two_mul {h : ℕ} (hh : 1 ≤ h) : (h : ℝ) + 1 ≤ 2 * h := by
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  linarith

/-- "`b^h = bM`", where `M = b^{h-1}` and `h ≥ 1`. -/
lemma base_pow_eq_mul_pow (b : ℕ) {h : ℕ} (hh : 1 ≤ h) :
    (b : ℝ) ^ h = b * (b : ℝ) ^ (h - 1) := by
  rw [← pow_succ', Nat.sub_add_cancel hh]

/-- **Display (16)**: `b^{-5} h M ≤ n < 2 b^{-4} h M`, `M = b^{h-1}`. -/
theorem display_16 {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h) :
    (h : ℝ) * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 5 ≤ n ∧
      (n : ℝ) < 2 * h * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 4 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  -- the lower bound is the condition; "By maximality, `n < b^{-5}(h+1) b^h`."
  refine ⟨hs.2.1, (lt_of_isScale hs).trans_le ?_⟩
  -- "`b^h = bM`", so that `b^{-5}(h+1) b^h = b^{-4}(h+1) M`
  have e : ((h : ℝ) + 1) * (b : ℝ) ^ h / (b : ℝ) ^ 5 =
      ((h : ℝ) + 1) * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 4 := by
    rw [base_pow_eq_mul_pow b hs.1]
    field_simp
  rw [e]
  -- "`h + 1 ≤ 2h`"
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (scale_succ_le_two_mul hs.1) (by positivity)) (by positivity)

/-- "`h + 1 ≤ 2^h`". -/
lemma scale_succ_le_two_pow (h : ℕ) : (h : ℝ) + 1 ≤ 2 ^ h := by
  exact_mod_cast Nat.lt_two_pow_self (n := h)

/-- "`b^{-5} ≤ 1`". -/
lemma inv_pow_five_le_one {b : ℕ} (hb : 1 ≤ b) : ((b : ℝ) ^ 5)⁻¹ ≤ 1 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hbR)

/-- "with `h + 1 ≤ 2^h` and `b^{-5} ≤ 1` it gives `n < (2b)^h`". -/
lemma lt_two_mul_pow_of_isScale {b n h : ℕ} (hb : 1 ≤ b) (hs : IsScale b n h) :
    (n : ℝ) < (2 * (b : ℝ)) ^ h := by
  -- "By maximality, `n < b^{-5}(h+1) b^h`."
  calc (n : ℝ) < ((h : ℝ) + 1) * (b : ℝ) ^ h / (b : ℝ) ^ 5 := lt_of_isScale hs
    -- "`b^{-5} ≤ 1`"
    _ ≤ ((h : ℝ) + 1) * (b : ℝ) ^ h := by
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_right (by positivity) (inv_pow_five_le_one hb)
    -- "`h + 1 ≤ 2^h`"
    _ ≤ (2 : ℝ) ^ h * (b : ℝ) ^ h :=
        mul_le_mul_of_nonneg_right (scale_succ_le_two_pow h) (by positivity)
    _ = (2 * (b : ℝ)) ^ h := (mul_pow _ _ _).symm

/-- **Display (17)**: `log₂ n < (1 + log₂ b) h`. -/
theorem display_17 {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h) :
    Real.logb 2 n < (1 + Real.logb 2 b) * h := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  -- `log₂ ((2b)^h) = (1 + log₂ b) h`
  have e : Real.logb 2 ((2 * (b : ℝ)) ^ h) = (1 + Real.logb 2 b) * h := by
    rw [Real.logb_pow, Real.logb_mul (by norm_num) hbR.ne',
      Real.logb_self_eq_one (by norm_num), mul_comm]
  rw [← e]
  -- `n < (2b)^h`
  exact Real.logb_lt_logb (by norm_num) hnR (lt_two_mul_pow_of_isScale (by omega) hs)

/-- **Display (18)**: `c_A (log₂ n)^{3/2} < b^{-8} h^{3/2}`. -/
theorem display_18 {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h) :
    cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < ((b : ℝ) ^ 8)⁻¹ * (h : ℝ) ^ (3 / 2 : ℝ) := by
  have hl : 0 < 1 + Real.logb 2 b := one_add_logb_pos hb
  have hlp : 0 < (1 + Real.logb 2 b) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hl _
  -- `log₂ n ≥ 0` since `n ≥ 1`
  have hlog0 : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
  -- (17), raised to the power `3/2`
  have hpow : Real.logb 2 n ^ (3 / 2 : ℝ) <
      (1 + Real.logb 2 b) ^ (3 / 2 : ℝ) * (h : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow hl.le (Nat.cast_nonneg h)]
    exact Real.rpow_lt_rpow hlog0 (display_17 hb hn hs) (by norm_num)
  -- the definition of `c_A`
  calc cA b * Real.logb 2 n ^ (3 / 2 : ℝ)
      < cA b * ((1 + Real.logb 2 b) ^ (3 / 2 : ℝ) * (h : ℝ) ^ (3 / 2 : ℝ)) :=
        mul_lt_mul_of_pos_left hpow (cA_pos hb)
    _ = ((b : ℝ) ^ 8)⁻¹ * (h : ℝ) ^ (3 / 2 : ℝ) := by
        unfold cA
        rw [← mul_assoc, div_mul_cancel₀ _ hlp.ne']

/-! ### The case `M > n` -/

/-- "If `M > n`, then (16) gives `b^{-5} h < 1`": by (16), `b^{-5} h M ≤ n < M`. -/
lemma scale_div_pow_five_lt_one {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h)
    (hMn : n < b ^ (h - 1)) : (h : ℝ) / (b : ℝ) ^ 5 < 1 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  have hnM : (n : ℝ) < (b : ℝ) ^ (h - 1) := by exact_mod_cast hMn
  -- (16): `b^{-5} h M ≤ n`, and `n < M`
  have h1 : (h : ℝ) / (b : ℝ) ^ 5 * (b : ℝ) ^ (h - 1) < 1 * (b : ℝ) ^ (h - 1) := by
    rw [one_mul, div_mul_eq_mul_div]
    exact (display_16 hb hs).1.trans_lt hnM
  exact lt_of_mul_lt_mul_right h1 hM.le

/-- "that is, `h < b^5`". -/
lemma scale_lt_pow_five {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h)
    (hMn : n < b ^ (h - 1)) : (h : ℝ) < (b : ℝ) ^ 5 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  exact (div_lt_one (by positivity)).mp (scale_div_pow_five_lt_one hb hs hMn)

/-- The first inequality of "(18) gives `c_A (log₂ n)^{3/2} < b^{-8} b^{15/2} < 1`": by (18)
and `h < b^5` (`scale_lt_pow_five`), since `(b^5)^{3/2} = b^{15/2}`. -/
lemma cA_mul_lt_of_lt {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h)
    (hMn : n < b ^ (h - 1)) :
    cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < ((b : ℝ) ^ 8)⁻¹ * (b : ℝ) ^ (15 / 2 : ℝ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb8 : (0 : ℝ) < (b : ℝ) ^ 8 := by positivity
  -- `h < b⁵`, hence `h^{3/2} < (b⁵)^{3/2} = b^{15/2}`
  have h152 : (h : ℝ) ^ (3 / 2 : ℝ) < (b : ℝ) ^ (15 / 2 : ℝ) := by
    have h1 := Real.rpow_lt_rpow (Nat.cast_nonneg h) (scale_lt_pow_five hb hs hMn)
      (by norm_num : (0 : ℝ) < 3 / 2)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hb0.le,
      show ((5 : ℕ) : ℝ) * (3 / 2) = 15 / 2 by norm_num] at h1
  -- (18)
  calc cA b * Real.logb 2 n ^ (3 / 2 : ℝ)
      < ((b : ℝ) ^ 8)⁻¹ * (h : ℝ) ^ (3 / 2 : ℝ) := display_18 hb hn hs
    _ < ((b : ℝ) ^ 8)⁻¹ * (b : ℝ) ^ (15 / 2 : ℝ) :=
        mul_lt_mul_of_pos_left h152 (inv_pos.mpr hb8)

/-- The second inequality of "(18) gives `c_A (log₂ n)^{3/2} < b^{-8} b^{15/2} < 1`":
`b^{15/2} < b^8`, because `b > 1`. -/
lemma inv_pow_eight_mul_rpow_lt_one {b : ℕ} (hb : 2 ≤ b) :
    ((b : ℝ) ^ 8)⁻¹ * (b : ℝ) ^ (15 / 2 : ℝ) < 1 := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb0 : (0 : ℝ) < b := by linarith
  have hb8 : (0 : ℝ) < (b : ℝ) ^ 8 := by positivity
  -- `b^{15/2} < b⁸`
  have h8 : (b : ℝ) ^ (15 / 2 : ℝ) < (b : ℝ) ^ 8 := by
    have h1 := Real.rpow_lt_rpow_of_exponent_lt hb1 (by norm_num : (15 / 2 : ℝ) < (8 : ℕ))
    rwa [Real.rpow_natCast] at h1
  calc ((b : ℝ) ^ 8)⁻¹ * (b : ℝ) ^ (15 / 2 : ℝ)
      < ((b : ℝ) ^ 8)⁻¹ * (b : ℝ) ^ 8 := mul_lt_mul_of_pos_left h8 (inv_pos.mpr hb8)
    _ = 1 := inv_mul_cancel₀ hb8.ne'

/-- "If `M > n`, then (16) gives `b^{-5} h < 1`, that is, `h < b^5`, and (18) gives
`c_A (log₂ n)^{3/2} < b^{-8} b^{15/2} < 1`." This theorem states the two ends of the last
chain; its links are `cA_mul_lt_of_lt` and `inv_pow_eight_mul_rpow_lt_one`. -/
theorem cA_mul_lt_one {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h)
    (hMn : n < b ^ (h - 1)) : cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < 1 :=
  calc cA b * Real.logb 2 n ^ (3 / 2 : ℝ)
      < ((b : ℝ) ^ 8)⁻¹ * (b : ℝ) ^ (15 / 2 : ℝ) := cA_mul_lt_of_lt hb hn hs hMn
    _ < 1 := inv_pow_eight_mul_rpow_lt_one hb

/-- "The rectangle `[0,1] × [0, min_i V_i]` is one, because it contains just the lowest point,
which is unique since all heights are distinct." Almost surely the hypotheses of
`one_le_supNorm` hold (the points lie in the unit square and all heights are distinct), so
almost surely `‖F_χ‖∞ ≥ 1` for every coloring `χ`. -/
theorem ae_one_le_supNorm {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ P ∂unifPts n, ∀ χ : Fin n → ℤˣ, 1 ≤ supNorm χ P := by
  -- almost surely all heights are distinct and all coordinates lie in `(0,1]`
  filter_upwards [ae_heights_injective n, ae_inUnit n] with P hinj hunit χ
  exact one_le_supNorm hn χ P
    (fun i => ⟨⟨(hunit i).1.1.le, (hunit i).1.2⟩, ⟨(hunit i).2.1.le, (hunit i).2.2⟩⟩) hinj

/-- "So in this case the claim of the theorem holds with probability one." If `M > n`, then
almost surely every coloring `χ` satisfies `‖F_χ‖∞ ≥ 1 > c_A (log₂ n)^{3/2}`. -/
theorem ae_cA_mul_lt_supNorm {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h)
    (hMn : n < b ^ (h - 1)) :
    ∀ᵐ P ∂unifPts n, ∀ χ : Fin n → ℤˣ, cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P := by
  -- the threshold is less than `1`: "So it suffices to find an anchored rectangle that has
  -- imbalance `1` under every coloring."
  have hlt : cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < 1 := cA_mul_lt_one hb hn hs hMn
  -- the rectangle `[0,1] × [0, min_i V_i]` is one, almost surely
  filter_upwards [ae_one_le_supNorm hn] with P hP χ
  exact hlt.trans_le (hP χ)

/-! ### The case `M ≤ n` -/

/-- The first inequality of "Also `h ≤ 2^{h-1} ≤ M ≤ n`". -/
lemma scale_le_two_pow (h : ℕ) : h ≤ 2 ^ (h - 1) := by
  have h1 : h - 1 < 2 ^ (h - 1) := Nat.lt_two_pow_self
  omega

/-- The second inequality of "Also `h ≤ 2^{h-1} ≤ M ≤ n`", because `b ≥ 2`. -/
lemma two_pow_le_base_pow {b : ℕ} (hb : 2 ≤ b) (h : ℕ) : 2 ^ (h - 1) ≤ b ^ (h - 1) :=
  Nat.pow_le_pow_left hb _

/-- "Also `h ≤ 2^{h-1} ≤ M ≤ n`." This lemma states the two ends of the chain; its first two
links are `scale_le_two_pow` and `two_pow_le_base_pow`, and the last one is the assumption
`M ≤ n` of the case. -/
lemma scale_le_of_pow_le {b n h : ℕ} (hb : 2 ≤ b) (hMn : b ^ (h - 1) ≤ n) : h ≤ n :=
  calc h ≤ 2 ^ (h - 1) := scale_le_two_pow h
    _ ≤ b ^ (h - 1) := two_pow_le_base_pow hb h
    _ ≤ n := hMn

/-- What "the first condition in (15)" gives for the first term on the right-hand side of
(14): `(48/b)^{n/2} ≤ e^{-(A+2)n}`. The whole first term `h (48/b)^{n/2}` is bounded in
`first_term_le_mul`. -/
lemma first_term_le {A : ℝ} {b : ℕ} (hb : 0 < b) (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2)
    (n : ℕ) : (48 / (b : ℝ)) ^ ((n : ℝ) / 2) ≤ Real.exp (-(A + 2) * n) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- `log(48/b) = -log(b/48) ≤ -2(A+2)`
  have hlog : Real.log (48 / (b : ℝ)) = -Real.log ((b : ℝ) / 48) := by
    rw [← Real.log_inv, inv_div]
  have h1 := mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg (α := ℝ) n)
  -- `(48/b)^{n/2} = exp((n/2) log(48/b))`
  rw [Real.rpow_def_of_pos (by positivity), Real.exp_le_exp, hlog]
  linarith

/-- "By the first condition in (15), the first term on the right-hand side of (14) is at most
`h e^{-(A+2)n} ≤ n e^{-(A+2)n}`." The first inequality is `first_term_le`, multiplied by `h`;
the second is `h ≤ n` (`scale_le_of_pow_le`), multiplied by `e^{-(A+2)n}`. -/
lemma first_term_le_mul {A : ℝ} {b n h : ℕ} (hb : 2 ≤ b)
    (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hMn : b ^ (h - 1) ≤ n) :
    (h : ℝ) * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) ≤ h * Real.exp (-(A + 2) * n) ∧
      (h : ℝ) * Real.exp (-(A + 2) * n) ≤ n * Real.exp (-(A + 2) * n) := by
  refine ⟨mul_le_mul_of_nonneg_left (first_term_le (by omega) hb1 n) (Nat.cast_nonneg h),
    mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le⟩
  -- "Also `h ≤ 2^{h-1} ≤ M ≤ n`."
  exact_mod_cast scale_le_of_pow_le hb hMn

/-- The first inequality of "By (16) and the second condition,
`hM/(2048 b³) > bn/4096 ≥ (A+2+log 2) n`"; it uses the upper bound of (16). -/
lemma exponent_gt {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h) :
    (b : ℝ) * n / 4096 < (h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  -- `hM/(2048 b³) = b (2 b^{-4} h M)/4096`
  have e : (h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3) =
      (b : ℝ) * (2 * h * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 4) / 4096 := by
    field_simp
    ring
  rw [e]
  -- (16): `n < 2 b^{-4} h M`
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (display_16 hb hs).2 hbR)
    (by norm_num)

/-- The second inequality of "By (16) and the second condition,
`hM/(2048 b³) > bn/4096 ≥ (A+2+log 2) n`"; it uses the second condition of (15). -/
lemma exponent_ge {A : ℝ} {b : ℕ} (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) (n : ℕ) :
    (A + 2 + Real.log 2) * n ≤ (b : ℝ) * n / 4096 := by
  have := mul_le_mul_of_nonneg_right hb2 (Nat.cast_nonneg (α := ℝ) n)
  linarith

/-- "so the second term is at most `2^n e^{-(A+2+log 2)n}`", by `exponent_gt` and
`exponent_ge`. -/
lemma second_term_le_two_pow_mul {A : ℝ} {b n h : ℕ} (hb : 2 ≤ b)
    (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) (hs : IsScale b n h) :
    2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) ≤
      2 ^ n * Real.exp (-(A + 2 + Real.log 2) * n) := by
  -- `hM/(2048 b³) > bn/4096 ≥ (A+2+log 2) n`
  have h1 := exponent_gt hb hs
  have h2 := exponent_ge hb2 n
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  linarith

/-- "which equals `e^{-(A+2)n}`": `2^n e^{-(A+2+log 2)n} = e^{-(A+2)n}`, because
`2^n = e^{n log 2}`. -/
lemma two_pow_mul_exp_eq (A : ℝ) (n : ℕ) :
    2 ^ n * Real.exp (-(A + 2 + Real.log 2) * n) = Real.exp (-(A + 2) * n) := by
  -- `2^n = e^{n log 2}`
  have hpow : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hpow, ← Real.exp_add]
  congr 1
  ring

/-- "By (16) and the second condition, `hM/(2048 b³) > bn/4096 ≥ (A+2+log 2) n`, so the second
term is at most `2^n e^{-(A+2+log 2)n}`, which equals `e^{-(A+2)n}`." This lemma states the
two ends; the steps are `exponent_gt`, `exponent_ge`, `second_term_le_two_pow_mul` and
`two_pow_mul_exp_eq`. -/
lemma second_term_le {A : ℝ} {b n h : ℕ} (hb : 2 ≤ b)
    (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) (hs : IsScale b n h) :
    2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) ≤
      Real.exp (-(A + 2) * n) :=
  calc (2 : ℝ) ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3)))
      ≤ (2 : ℝ) ^ n * Real.exp (-(A + 2 + Real.log 2) * n) :=
        second_term_le_two_pow_mul hb hb2 hs
    _ = Real.exp (-(A + 2) * n) := two_pow_mul_exp_eq A n

/-- The first inequality of "The sum of the two terms is at most
`(n+1) e^{-(A+2)n} ≤ e^{-An}`": the first term is at most `n e^{-(A+2)n}`
(`first_term_le_mul`) and the second term is at most `e^{-(A+2)n}` (`second_term_le`). -/
lemma sum_terms_le {A : ℝ} {b n h : ℕ} (hb : 2 ≤ b)
    (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096)
    (hs : IsScale b n h) (hMn : b ^ (h - 1) ≤ n) :
    h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
        2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) ≤
      ((n : ℝ) + 1) * Real.exp (-(A + 2) * n) := by
  -- the first term is at most `h e^{-(A+2)n} ≤ n e^{-(A+2)n}`
  have hfirst := first_term_le_mul hb hb1 hMn
  -- the second term is at most `e^{-(A+2)n}`
  have hsecond := second_term_le hb hb2 hs
  calc (h : ℝ) * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
        2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3)))
      ≤ n * Real.exp (-(A + 2) * n) + Real.exp (-(A + 2) * n) :=
        add_le_add (hfirst.1.trans hfirst.2) hsecond
    _ = ((n : ℝ) + 1) * Real.exp (-(A + 2) * n) := by ring

/-- "since `n + 1 ≤ e^{2n}`". The inequality is stated for a real number `x ≥ 0` in place of
`n`: `x + 1 ≤ e^x ≤ e^{2x}`. -/
lemma add_one_le_exp_two_mul {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ Real.exp (2 * x) :=
  (Real.add_one_le_exp x).trans (Real.exp_le_exp.mpr (le_mul_of_one_le_left hx one_le_two))

/-- The second inequality of "The sum of the two terms is at most
`(n+1) e^{-(A+2)n} ≤ e^{-An}`, since `n + 1 ≤ e^{2n}`." It is stated for a real number
`x ≥ 0` in place of `n`, and follows from `add_one_le_exp_two_mul`. -/
lemma add_one_mul_exp_le (A : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) * Real.exp (-(A + 2) * x) ≤ Real.exp (-A * x) :=
  calc (x + 1) * Real.exp (-(A + 2) * x)
      ≤ Real.exp (2 * x) * Real.exp (-(A + 2) * x) :=
        mul_le_mul_of_nonneg_right (add_one_le_exp_two_mul hx) (Real.exp_pos _).le
    _ = Real.exp (-A * x) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- The two terms of (14) add up to at most `e^{-An}` (the computation after "So assume that
`M ≤ n`").

"The sum of the two terms is at most `(n+1) e^{-(A+2)n} ≤ e^{-An}`, since `n + 1 ≤ e^{2n}`."
This theorem states the two ends of the chain; its links are `sum_terms_le` and
`add_one_mul_exp_le`. (The hypothesis `hn` is implied by `hMn`, since `M ≥ 1`; the proof uses
it only for `n ≥ 0`.) -/
theorem failure_le {A : ℝ} (hA : 0 < A) {b n h : ℕ}
    (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096)
    (hn : 1 ≤ n) (hs : IsScale b n h) (hMn : b ^ (h - 1) ≤ n) :
    h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
        2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) ≤
      Real.exp (-A * n) := by
  -- (15) forces `b > 48`
  have hb49 : 49 ≤ b := base_ge_49 hA hb1
  -- `n ≥ 0`
  have hn0 : (0 : ℝ) ≤ n := zero_le_one.trans (by exact_mod_cast hn)
  calc (h : ℝ) * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
        2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3)))
      ≤ ((n : ℝ) + 1) * Real.exp (-(A + 2) * n) := sum_terms_le (by omega) hb1 hb2 hs hMn
    _ ≤ Real.exp (-A * n) := add_one_mul_exp_le A hn0

/-- The first inequality of the threshold chain (see `threshold_gt`),
`(h/(64 b^{3/2})) √(n/M) ≥ (h/(64 b^{3/2})) √(h/b^5)`. "The first inequality uses (16)": by
the lower bound of (16), `h/b^5 ≤ n/M`. -/
lemma threshold_ge_sqrt {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h) :
    (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (h / (b : ℝ) ^ 5) ≤
      (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  -- (16): `h/b⁵ ≤ n/M`
  have hroot : Real.sqrt (h / (b : ℝ) ^ 5) ≤ Real.sqrt (n / (b : ℝ) ^ (h - 1)) := by
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hM]
    calc (h : ℝ) / (b : ℝ) ^ 5 * (b : ℝ) ^ (h - 1)
        = (h : ℝ) * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 5 := by ring
      _ ≤ (n : ℝ) := (display_16 hb hs).1
  exact mul_le_mul_of_nonneg_left hroot (by positivity)

/-- The equality of the threshold chain (see `threshold_gt`):
`(h/(64 b^{3/2})) √(h/b^5) = h^{3/2}/(64 b^4)`. -/
lemma threshold_sqrt_eq (b h : ℕ) :
    (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (h / (b : ℝ) ^ 5) =
      (h : ℝ) ^ (3 / 2 : ℝ) / (64 * (b : ℝ) ^ 4) := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hsbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb0
  -- `√(b⁵) = b² √b`
  have e5 : Real.sqrt ((b : ℝ) ^ 5) = (b : ℝ) ^ 2 * Real.sqrt b := by
    rw [show (b : ℝ) ^ 5 = ((b : ℝ) ^ 2) ^ 2 * b by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  -- `64 b⁴ = 64 (b √b) (b² √b)`
  have e4 : (64 : ℝ) * (b : ℝ) ^ 4 =
      64 * ((b : ℝ) * Real.sqrt b) * ((b : ℝ) ^ 2 * Real.sqrt b) := by
    calc (64 : ℝ) * (b : ℝ) ^ 4 = 64 * (b : ℝ) ^ 3 * b := by ring
      _ = 64 * (b : ℝ) ^ 3 * (Real.sqrt b * Real.sqrt b) := by rw [hsbb]
      _ = 64 * ((b : ℝ) * Real.sqrt b) * ((b : ℝ) ^ 2 * Real.sqrt b) := by ring
  -- `b^{3/2} = b √b` and `h^{3/2} = h √h`
  rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ (b : ℝ) ^ 5), e5,
    rpow_three_halves_eq_mul_sqrt hb0, rpow_three_halves_eq_mul_sqrt hh0, e4,
    div_mul_div_comm]

/-- The second inequality of the threshold chain (see `threshold_gt`),
`h^{3/2}/(64 b^4) ≥ b^{-8} h^{3/2}`: "the second uses `64 ≤ b^4`". -/
lemma rpow_div_ge {b : ℕ} (hb : 3 ≤ b) (h : ℕ) :
    ((b : ℝ) ^ 8)⁻¹ * (h : ℝ) ^ (3 / 2 : ℝ) ≤ (h : ℝ) ^ (3 / 2 : ℝ) / (64 * (b : ℝ) ^ 4) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  -- "`64 ≤ b^4`", hence `64 b⁴ ≤ b⁸`
  have h64 : (64 : ℝ) ≤ (b : ℝ) ^ 4 := sixty_four_le_pow_four hb
  rw [inv_mul_eq_div]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg h) _) (by positivity)
  nlinarith [pow_pos hb0 4]

/-- The threshold chain of the last display of the proof (uses (16), `64 ≤ b⁴`, (18)).

"The threshold in (14) satisfies
`(h/(64 b^{3/2})) √(n/M) ≥ (h/(64 b^{3/2})) √(h/b^5) = h^{3/2}/(64 b^4) ≥ b^{-8} h^{3/2} >
c_A (log₂ n)^{3/2}`. The first inequality uses (16), the second uses `64 ≤ b^4`, and the
last one is (18)." This theorem states the two ends of the chain; its links are
`threshold_ge_sqrt`, `threshold_sqrt_eq`, `rpow_div_ge` and `display_18`. -/
theorem threshold_gt {b n h : ℕ} (hb : 3 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h) :
    cA b * Real.logb 2 n ^ (3 / 2 : ℝ) <
      (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1)) :=
  -- the chain, read from right to left
  calc cA b * Real.logb 2 n ^ (3 / 2 : ℝ)
      < ((b : ℝ) ^ 8)⁻¹ * (h : ℝ) ^ (3 / 2 : ℝ) := display_18 (by omega) hn hs
    _ ≤ (h : ℝ) ^ (3 / 2 : ℝ) / (64 * (b : ℝ) ^ 4) := rpow_div_ge hb h
    _ = (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (h / (b : ℝ) ^ 5) :=
        (threshold_sqrt_eq b h).symm
    _ ≤ (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1)) :=
        threshold_ge_sqrt (by omega) hs

/-- The case `M ≤ n` of the proof of Theorem 1.1. "So by (14), with probability at least
`1 - e^{-An}`, every coloring `χ` satisfies `‖F_χ‖∞ > c_A (log₂ n)^{3/2}`." Stated for the
complementary event:

`Pr[∃ χ ∈ {±1}ⁿ : ‖F_χ‖∞ ≤ c_A (log₂ n)^{3/2}] ≤ e^{-An}`. -/
theorem prob_exists_supNorm_le_of_pow_le {A : ℝ} (hA : 0 < A) {b n h : ℕ}
    (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096)
    (hn : 1 ≤ n) (hs : IsScale b n h) (hMn : b ^ (h - 1) ≤ n) :
    (unifPts n).real {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ cA b * Real.logb 2 n ^ (3 / 2 : ℝ)} ≤
      Real.exp (-A * n) := by
  -- (15) forces `b > 48`
  have hb49 : 49 ≤ b := base_ge_49 hA hb1
  -- the event is contained in the event of (14), by the threshold chain
  have hsub : {P : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤˣ,
        supNorm χ P ≤ cA b * Real.logb 2 n ^ (3 / 2 : ℝ)} ⊆
      {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤
        (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))} :=
    fun P ⟨χ, hχ⟩ => ⟨χ, hχ.trans (threshold_gt (by omega) hn hs).le⟩
  calc (unifPts n).real {P | ∃ χ : Fin n → ℤˣ,
        supNorm χ P ≤ cA b * Real.logb 2 n ^ (3 / 2 : ℝ)}
      ≤ (unifPts n).real {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤
          (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))} :=
        measureReal_mono hsub
    -- "Then Proposition 2.7 applies."
    _ ≤ h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
          2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) :=
        proposition_2_7 (by omega) hs.1 hMn
    -- the right-hand side of (14) is at most `e^{-An}`
    _ ≤ Real.exp (-A * n) := failure_le hA hb1 hb2 hn hs hMn

/-! ### Theorem 1.1 -/

/-- The core of the proof of Theorem 1.1. For an integer `b` satisfying (15) and every `n ≥ 1`,

`Pr[∃ χ ∈ {±1}ⁿ : ‖F_χ‖∞ ≤ c_A (log₂ n)^{3/2}] ≤ e^{-An}`.

The two cases of the proof are `ae_cA_mul_lt_supNorm` (`M > n`) and
`prob_exists_supNorm_le_of_pow_le` (`M ≤ n`). The event is measurable
(`measurableSet_exists_supNorm_le`). -/
theorem prob_exists_supNorm_le {A : ℝ} (hA : 0 < A) {b : ℕ}
    (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096)
    {n : ℕ} (hn : 1 ≤ n) :
    (unifPts n).real {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ cA b * Real.logb 2 n ^ (3 / 2 : ℝ)} ≤
      Real.exp (-A * n) := by
  -- (15) forces `b > 48`
  have hb49 : 49 ≤ b := base_ge_49 hA hb1
  -- the scale `h`, with `M = b^{h-1}`
  obtain ⟨h, hs⟩ := exists_isScale (by omega : 2 ≤ b) hn
  rcases lt_or_ge n (b ^ (h - 1)) with hMn | hMn
  · -- "If `M > n`": almost surely every coloring has `‖F_χ‖∞ > c_A (log₂ n)^{3/2}`
    -- (`ae_cA_mul_lt_supNorm`), so the event is null
    have hnull : unifPts n {P | ∃ χ : Fin n → ℤˣ,
        supNorm χ P ≤ cA b * Real.logb 2 n ^ (3 / 2 : ℝ)} = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp (ae_cA_mul_lt_supNorm (by omega) hn hs hMn))
      rintro P ⟨χ, hχ⟩ hall
      exact absurd (hall χ) (not_lt.mpr hχ)
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  · -- "So assume that `M ≤ n`." This case is `prob_exists_supNorm_le_of_pow_le`.
    exact prob_exists_supNorm_le_of_pow_le hA hb1 hb2 hn hs hMn

/-- The event that the points are distinct and lie in the unit square and that every coloring
`χ` has `‖F_χ‖∞ > t` is measurable. -/
lemma measurableSet_distinct_Icc_forall_lt_supNorm {n : ℕ} (t : ℝ) :
    MeasurableSet {P : Fin n → ℝ × ℝ | (∀ i j, i ≠ j → P i ≠ P j) ∧
      (∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1) ∧ ∀ χ : Fin n → ℤˣ, t < supNorm χ P} := by
  have h1 : MeasurableSet {P : Fin n → ℝ × ℝ | ∀ i j, i ≠ j → P i ≠ P j} := by
    have e : {P : Fin n → ℝ × ℝ | ∀ i j, i ≠ j → P i ≠ P j} =
        ⋂ i, ⋂ j, ⋂ _ : i ≠ j, {P | P i = P j}ᶜ := by
      ext P
      simp
    rw [e]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ =>
        (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl
  have h2 : MeasurableSet {P : Fin n → ℝ × ℝ | ∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1} := by
    have e : {P : Fin n → ℝ × ℝ | ∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1} =
        ⋂ i, (fun P : Fin n → ℝ × ℝ => P i) ⁻¹' Set.Icc 0 1 := by
      ext P
      simp
    rw [e]
    exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Icc
  have h3 : MeasurableSet {P : Fin n → ℝ × ℝ | ∀ χ : Fin n → ℤˣ, t < supNorm χ P} := by
    have e : {P : Fin n → ℝ × ℝ | ∀ χ : Fin n → ℤˣ, t < supNorm χ P} =
        ⋂ χ : Fin n → ℤˣ, {P | t < supNorm χ P} := by
      ext P
      simp
    rw [e]
    exact MeasurableSet.iInter fun χ => measurableSet_lt measurable_const (measurable_supNorm χ)
  exact h1.inter (h2.inter h3)

/-- Theorem 1.1 with the manuscript's constant, on a measurable event: "with probability at least
`1 - e^{-An}`, every coloring `χ` satisfies `‖F_χ‖∞ > c_A (log₂ n)^{3/2}`"; on the event the
points are distinct and lie in the unit square. -/
theorem theorem_1_1_constant_event {A : ℝ} (hA : 0 < A) {b : ℕ}
    (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ G : Set (Fin n → ℝ × ℝ), MeasurableSet G ∧
      ENNReal.ofReal (1 - Real.exp (-A * n)) ≤ unifPts n G ∧
      ∀ P ∈ G, Function.Injective P ∧ (∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1) ∧
        ∀ χ : Fin n → ℤˣ, cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P := by
  -- the event `G`: distinct points of the unit square, and `‖F_χ‖∞ > c_A (log₂ n)^{3/2}`
  -- for every coloring
  have hG := measurableSet_distinct_Icc_forall_lt_supNorm (n := n)
    (cA b * Real.logb 2 n ^ (3 / 2 : ℝ))
  refine ⟨_, hG, ?_, fun P hP => ⟨fun i j hij => ?_, hP.2.1, hP.2.2⟩⟩
  · -- almost surely the heights are distinct and the points lie in the unit square, so the
    -- complement of `G` is, up to a null set, inside the event of `prob_exists_supNorm_le`
    have hae : ({P : Fin n → ℝ × ℝ | (∀ i j, i ≠ j → P i ≠ P j) ∧
          (∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1) ∧
          ∀ χ : Fin n → ℤˣ, cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P}ᶜ : Set _)
        ≤ᵐ[unifPts n] {P | ∃ χ : Fin n → ℤˣ,
          supNorm χ P ≤ cA b * Real.logb 2 n ^ (3 / 2 : ℝ)} := by
      filter_upwards [ae_heights_injective n, ae_inUnit n] with P hinj hunit hP
      by_contra hcon
      refine hP ⟨fun i j hij hPij => hij (hinj (congrArg Prod.snd hPij)), fun i => ?_,
        fun χ => not_le.mp fun hχ => hcon ⟨χ, hχ⟩⟩
      exact ⟨⟨(hunit i).1.1.le, (hunit i).2.1.le⟩, ⟨(hunit i).1.2, (hunit i).2.2⟩⟩
    have hbad : unifPts n {P | ∃ χ : Fin n → ℤˣ,
        supNorm χ P ≤ cA b * Real.logb 2 n ^ (3 / 2 : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-A * n)) := by
      have H := prob_exists_supNorm_le hA hb1 hb2 hn
      simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        ENNReal.ofReal_le_ofReal H
    -- `Pr(G^c) ≤ e^{-An}`, hence `Pr(G) = 1 - Pr(G^c) ≥ 1 - e^{-An}`
    have hcompl := (measure_mono_ae hae).trans hbad
    rw [prob_compl_eq_one_sub hG] at hcompl
    rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
    exact tsub_le_iff_left.mpr (tsub_le_iff_right.mp hcompl)
  · -- distinct points: `P` is injective
    by_contra hne
    exact hP.1 i j hne hij

/-- **Theorem 1.1 with the constant of the manuscript.** Let `A > 0`, let the integer `b`
satisfy (15), `(1/2) log(b/48) ≥ A + 2` and `b/4096 ≥ A + 2 + log 2`, and let
`c_A = b^{-8}/(1 + log₂ b)^{3/2}`. Then for every integer `n ≥ 1`,

`Pr[for every χ ∈ {±1}ⁿ, ‖F_χ‖∞ ≥ c_A (log₂ n)^{3/2}] ≥ 1 - e^{-An}`.

The event is measurable (`measurableSet_forall_le_supNorm`). -/
theorem theorem_1_1_constant {A : ℝ} (hA : 0 < A) {b : ℕ}
    (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096)
    {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (1 - Real.exp (-A * n)) ≤
      unifPts n {P | ∀ χ : Fin n → ℤˣ, cA b * Real.logb 2 n ^ (3 / 2 : ℝ) ≤ supNorm χ P} := by
  obtain ⟨G, -, hmeas, hgood⟩ := theorem_1_1_constant_event hA hb1 hb2 hn
  exact hmeas.trans (measure_mono fun P hP χ => ((hgood P hP).2.2 χ).le)

/-- **Theorem 1.1**, as displayed. "For every `A > 0`, there is a constant `c_A > 0` such that
the following holds for every integer `n ≥ 1`. If `P_1, …, P_n` are independent uniform points
in `[0,1]²`, then

`Pr[for every χ ∈ {±1}ⁿ, ‖F_χ‖∞ ≥ c_A (log₂ n)^{3/2}] ≥ 1 - e^{-An}`."

The proof is the one of the manuscript: a base `b` with (15), the potential of display (1),
Lemma 2.1, Fact 2.2, Lemmas 2.3–2.6, Proposition 2.7 and the computations of this file. The
event is measurable (`measurableSet_forall_le_supNorm`). The archive's own proof of the same
statement is restated as `theorem_1_1_archive` in `ArchiveRoute.lean`. -/
theorem theorem_1_1 :
    ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (1 - Real.exp (-A * n)) ≤
        unifPts n {P | ∀ χ : Fin n → ℤˣ, c * Real.logb 2 n ^ (3 / 2 : ℝ) ≤ supNorm χ P} := by
  intro A hA
  -- "Choose an integer `b` so large that" (15) holds; it forces `b > 48`
  obtain ⟨b, hb1, hb2⟩ := exists_base_of_15 A
  have hb49 := base_ge_49 hA hb1
  exact ⟨cA b, cA_pos (by omega), fun n hn => theorem_1_1_constant hA hb1 hb2 hn⟩

/-- **Theorem 1.1 with every definition unfolded**: no definition of the supplement or of the
archive occurs in the statement. The law of the points is the product of `n` copies of the
Lebesgue measure restricted to `[0,1]²`, the supremum norm is attained (`exists_eq_supNorm`),
and `F_χ(x,y)` is written as the sum of `χ_i` over the points with `0 ≤ U_i ≤ x` and
`0 ≤ V_i ≤ y`. -/
theorem theorem_1_1_unfolded :
    ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (1 - Real.exp (-A * n)) ≤
        (MeasureTheory.Measure.pi fun _ : Fin n =>
            (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))
          {P : Fin n → ℝ × ℝ | ∀ χ : Fin n → ℤˣ,
            ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1,
              c * Real.logb 2 (n : ℝ) ^ (3 / 2 : ℝ) ≤
                |∑ i : Fin n, if 0 ≤ (P i).1 ∧ (P i).1 ≤ x ∧ 0 ≤ (P i).2 ∧ (P i).2 ≤ y
                  then (((χ i : ℤˣ) : ℤ) : ℝ) else 0|} := by
  intro A hA
  obtain ⟨c, hc, h⟩ := theorem_1_1 A hA
  refine ⟨c, hc, fun n hn => (h n hn).trans (measure_mono ?_)⟩
  intro P hP χ
  -- the supremum is attained at some `(x, y) ∈ [0,1]²`
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_eq_supNorm χ P
  refine ⟨x, hx, y, hy, ?_⟩
  have h1 : c * Real.logb 2 (n : ℝ) ^ (3 / 2 : ℝ) ≤ supNorm χ P := hP χ
  rw [← hxy, F_eq_filter, Finset.sum_filter] at h1
  exact h1

/-! ### Corollary 1.2, lower bound -/

/-- "Since `1 - e^{-An} > 0` and the points are almost surely distinct, there is an `n`-point set
for which every coloring leaves an anchored rectangle with imbalance at least
`c_A (log₂ n)^{3/2}`." -/
theorem exists_points {A : ℝ} (hA : 0 < A) {b : ℕ}
    (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ P : Fin n → ℝ × ℝ, Function.Injective P ∧ (∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1) ∧
      ∀ χ : Fin n → ℤˣ, cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P := by
  obtain ⟨G, -, hmeas, hgood⟩ := theorem_1_1_constant_event hA hb1 hb2 hn
  -- "`1 - e^{-An} > 0`", so the event has positive probability and is not empty
  have hpos : 0 < unifPts n G := by
    refine lt_of_lt_of_le ?_ hmeas
    rw [ENNReal.ofReal_pos, sub_pos, Real.exp_lt_one_iff]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have := mul_pos hA hn'
    linarith
  obtain ⟨P, hP⟩ := nonempty_of_measure_ne_zero hpos.ne'
  exact ⟨P, hgood P hP⟩

/-- **Corollary 1.2, lower bound**: `Δ₂(n) = Ω(log^{3/2} n)`.

"Anchored rectangles are a subfamily of all rectangles" (`lt_Δ₂_of_supNorm`). Here `Δ₂` is the
archive's definition of the worst-case discrepancy of `n` points with respect to axis-parallel
rectangles. The upper bound of the corollary is Nikolov's theorem, which the manuscript cites;
it is not formalized. -/
theorem corollary_1_2_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * Real.logb 2 n ^ (3 / 2 : ℝ) < Δ₂ n := by
  -- the base for `A = 1`
  obtain ⟨b, hb1, hb2⟩ := exists_base_of_15 1
  have hb49 := base_ge_49 one_pos hb1
  refine ⟨cA b, cA_pos (by omega), fun n hn => ?_⟩
  obtain ⟨P, hinj, -, hP⟩ := exists_points one_pos hb1 hb2 hn
  exact lt_Δ₂_of_supNorm P hinj hP

end

end R56Audit
