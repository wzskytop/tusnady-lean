import R56Audit.ConditionalGain
import R56Audit.Influence
import R56Audit.BoundedDifferencesGeneral
import R56Audit.SuccessiveConditioning

/-!
# Lemma 2.6 of the manuscript (fluctuations)

Auditor's supplement (not part of the audited archive).

**Lemma 2.6.** Fix a coloring, and let `T = Σ_{j<h} (Z_{j+1} - E[Z_{j+1} | 𝓕_j])` be the
fluctuation term of (10). Then, for every `λ > 0`,

`Pr(T ≤ -λ) ≤ exp(-λ² M² / (2hn))`.

Here `Z_j` is the potential `Zpot` of display (1), `𝓕_j` is `stageSigma n b j`, and `T` is
`fluct χ b h` of `ConditionalGain.lean`. (The statement for the manuscript's `𝓕_j`, the σ-field
`digitSigma n b j` of the heights and the first `j` digits, is `lemma_2_6_digits` in
`Digits.lean`; it follows from `lemma_2_6`.) The proof has the three steps of the manuscript:

* Step 1, one digit: `Zstep_update_le` (`Influence.lean`);
* Step 2, one transition: `condExp_exp_step`, by **Fact A.1** (`fact_A_1`) with `Γ` the
  heights and the stage-`j` indices, `ξ_1, …, ξ_n` the next digits and `c = 1/M`; the next
  digits are independent of each other and of `𝓕_j` (`iIndepFun_fresh`,
  `indepFun_coarse_fresh`);
* Step 3, all transitions: the earlier terms are `𝓕_j`-measurable
  (`fluctTerm_measurable_of_lt`); `integral_exp_neg_sum_le`, conditioning successively
  (`integral_prod_le_of_condExp_le`, for the factors `e^{-t T_j}` and the bounds
  `exp(n t² / (2M²))` of Step 2); and Markov's inequality
  (`measureReal_le_exp_mul_integral_exp_neg`) with `t = λM²/(hn)`. The two general facts,
  successive conditioning and Markov's inequality, are proved from Mathlib in
  `SuccessiveConditioning.lean`.

`condExp_exp_step` and `integral_exp_neg_sum_le` read `Z_{j+1}` from the heights and the
indices (`Zproc`) and write `E[Z_{j+1} | 𝓕_j]` as the average over the next digits (`Zmean`);
almost surely this changes nothing (`fluctTerm_ae_eq`, `fluct_ae_eq`). The displays of the two
steps are then stated in the manuscript's terms, with the potential `Zpot`, Mathlib's
conditional expectation given `𝓕_j` and the fluctuation term `fluct`:

* `lemma_2_6_step2`: with `T_j = Z_{j+1} - E[Z_{j+1} | 𝓕_j]`, almost surely
  `E[e^{-t T_j} | 𝓕_j] ≤ exp(n t² / (2M²))`;
* `lemma_2_6_step3`: `E e^{-tT} ≤ exp(h n t² / (2M²))`;
* `integrable_exp_neg_fluctTerm`, `integrable_exp_neg_fluct`: `e^{-t T_j}` and `e^{-tT}` are
  integrable, so the conditional expectation and the expectation of these two displays are
  those of integrable functions;
* `lemma_2_6_markov`: `Pr(T ≤ -λ) ≤ exp(-tλ + h n t² / (2M²))` for every `t > 0`, by Step 3
  and Markov's inequality;
* `lemma_2_6`: Lemma 2.6, by the choice `t = λM²/(hn)`.
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory Finset Riesz Riesz.PointSets Oscillation

noncomputable section

variable {n : ℕ}

/-! ### Step 2: one transition -/

/-- `Z_{j+1}` as a function `φ(Γ, ξ)` of the `𝓕_j`-measurable data `Γ` (the heights and the
stage-`j` indices) and of the next digits `ξ`. -/
def nextPot (ε : Fin n → ℝ) (b h j : ℕ)
    (p : ((Fin n → ℝ) × (Fin n → ℤ)) × (Fin n → Fin b)) : ℝ :=
  Zstep ε b h (j + 1) p.1.1 (refineIdx p.1.2 p.2)

lemma measurable_nextPot {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) :
    Measurable (nextPot ε b h j) :=
  measurable_from_prod_countable_left fun r => measurable_Zstep_refine hb ε h (j + 1) r

/-- **Step 2 of the proof of Lemma 2.6**: for every real `t`, almost surely
`E[exp(t (Z_{j+1} - E[Z_{j+1} | 𝓕_j])) | 𝓕_j] ≤ exp(n t² / (2M²))`. This is Fact A.1 with
`c = 1/M`. Here `E[Z_{j+1} | 𝓕_j]` is written as the average over the next digits. -/
theorem condExp_exp_step {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) (t : ℝ) :
    ∀ᵐ P ∂pointSampleLaw n,
      ((pointSampleLaw n)[fun P => Real.exp (t * (Zproc ε b h (j + 1) P - Zmean ε b h j P)) |
          stageSigma n b j]) P ≤
        Real.exp (n * t ^ 2 * (1 / (b : ℝ) ^ (h - 1)) ^ 2 / 2) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- `Z_{j+1} = φ(Γ, ξ)`
  have hf : ∀ P : Fin n → ℝ × ℝ, nextPot ε b h j (coarseInfo n (b ^ j) P,
      fun i => freshGridIndex (b ^ j) b hb (P i).1) = Zproc ε b h (j + 1) P :=
    fun P => (Zproc_succ hb hj ε P).symm
  have hA := fact_A_1 (μ := pointSampleLaw n) (coarseInfo n (b ^ j))
    (fun (i : Fin n) (P : Fin n → ℝ × ℝ) => freshGridIndex (b ^ j) b hb (P i).1)
    (measurable_coarseInfo n (b ^ j))
    (fun i => (measurable_freshGridIndex (b ^ j) b hb).comp
      (measurable_fst.comp (measurable_pi_apply i)))
    (iIndepFun_fresh n (b ^ j) b hb)
    (indepFun_coarse_fresh n (b ^ j) b (pow_pos hb j) hb)
    (nextPot ε b h j) (measurable_nextPot hb ε h j)
    (c := 1 / (b : ℝ) ^ (h - 1)) (by positivity)
    (fun γ x i a => Zstep_update_le hb hj ε hε γ.1 γ.2 x i a)
    (by simp only [hf]; exact integrable_Zproc hb ε hε h (j + 1)) t
  simp only [hf] at hA
  -- replace `E[Z_{j+1} | 𝓕_j]` by the average over the next digits
  have hcongr : (fun P => Real.exp (t * (Zproc ε b h (j + 1) P -
      ((pointSampleLaw n)[Zproc ε b h (j + 1) | stageSigma n b j]) P))) =ᵐ[pointSampleLaw n]
      fun P => Real.exp (t * (Zproc ε b h (j + 1) P - Zmean ε b h j P)) := by
    filter_upwards [condExp_Zproc_succ hb hj ε hε] with P hP
    rw [hP]
  filter_upwards [hA, condExp_congr_ae (m := stageSigma n b j) hcongr] with P hP hP'
  rw [← hP']
  exact hP

/-! ### Step 3: all transitions -/

/-- The sum of the centered increments, with the conditional expectations written as averages
over the next digits. Almost surely this is the fluctuation term `T` (`fluct_ae_eq`). -/
def fluctStep (ε : Fin n → ℝ) (b h : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  ∑ j ∈ Finset.range h, (Zproc ε b h (j + 1) P - Zmean ε b h j P)

lemma measurable_fluctStep {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h : ℕ) :
    Measurable (fluctStep ε b h) :=
  Finset.measurable_sum _ fun j _ => (measurable_Zproc hb ε h (j + 1)).sub
    (measurable_Zmean hb ε h j)

lemma abs_fluctStep_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1) (h : ℕ)
    (P : Fin n → ℝ × ℝ) : |fluctStep ε b h P| ≤ h * n := by
  unfold fluctStep
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Finset.range h, |Zproc ε b h (j + 1) P - Zmean ε b h j P|
      ≤ ∑ _j ∈ Finset.range h, (n : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have h1 := Zproc_nonneg hb ε h (j + 1) P
        have h2 := Zproc_le hb ε hε h (j + 1) P
        have h3 := Zmean_nonneg hb ε h j P
        have h4 := Zmean_le hb (Finset.mem_range.mp hj) ε hε P
        rw [abs_le]
        constructor <;> linarith
    _ = h * n := by simp

/-- "For every `j`, the earlier terms `T_0, …, T_{j-1}` are `𝓕_j`-measurable." Here `𝓕_j` is
the σ-field `stageSigma n b j`, and the term `T_k = Z_{k+1} - E[Z_{k+1} | 𝓕_k]` is written
with `Z_{k+1}` read from the heights and the interval indices (`Zproc`) and with the average
over the next digits (`Zmean`) in place of the conditional expectation (`fluctTerm_ae_eq`). -/
lemma fluctTerm_measurable_of_lt {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h : ℕ) {k j : ℕ}
    (hkj : k < j) :
    Measurable[stageSigma n b j] (fun P => Zproc ε b h (k + 1) P - Zmean ε b h k P) := by
  -- `Z_{k+1}` is `𝓕_{k+1}`-measurable, and its average over the next digits is `𝓕_k`-measurable
  have h1 : Measurable[stageSigma n b j] (Zproc ε b h (k + 1)) :=
    ((Zproc_stronglyMeasurable hb ε h (k + 1)).mono (stageSigma_mono hb n hkj)).measurable
  have h2 : Measurable[stageSigma n b j] (Zmean ε b h k) :=
    ((Zmean_stronglyMeasurable hb ε h k).mono (stageSigma_mono hb n hkj.le)).measurable
  exact h1.sub h2

/-- **Step 3 of the proof of Lemma 2.6**: `E exp(-tT) ≤ exp(h n t² / (2M²))`, for every real
`t`. Here the conditional expectations in `T` are written as averages over the next digits
(`fluctStep`). "So we can condition successively on `𝓕_{h-1}, 𝓕_{h-2}, …, 𝓕_0` and apply
Step 2 each time. Multiplying the `h` bounds gives `E e^{-tT} ≤ exp(hnt²/(2M²))`." The
successive conditioning is `integral_prod_le_of_condExp_le`, for the factors `e^{-t T_j}`. -/
theorem integral_exp_neg_sum_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (h : ℕ) (t : ℝ) :
    ∫ P, Real.exp (-t * fluctStep ε b h P) ∂pointSampleLaw n ≤
      Real.exp (h * (n * t ^ 2 * (1 / (b : ℝ) ^ (h - 1)) ^ 2 / 2)) := by
  set c0 : ℝ := n * t ^ 2 * (1 / (b : ℝ) ^ (h - 1)) ^ 2 / 2 with hc0
  -- the factors: `W_j = e^{-t T_j}`, with `T_j = Z_{j+1} - E[Z_{j+1} | 𝓕_j]`
  let W : ℕ → (Fin n → ℝ × ℝ) → ℝ := fun j P =>
    Real.exp (-t * (Zproc ε b h (j + 1) P - Zmean ε b h j P))
  -- `W_j` is `𝓕_{j+1}`-measurable
  have hW : ∀ j < h, StronglyMeasurable[stageFiltration n b hb (j + 1)] (W j) := fun j _ =>
    (((fluctTerm_measurable_of_lt hb ε h (Nat.lt_succ_self j)).const_mul
      (-t)).exp).stronglyMeasurable
  -- `0 ≤ W_j ≤ e^{|t| n}`, since `|T_j| ≤ n`
  have hbound : ∀ j < h, ∀ P, 0 ≤ W j P ∧ W j P ≤ Real.exp (|t| * n) := by
    intro j hj P
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩
    have h1 := Zproc_nonneg hb ε h (j + 1) P
    have h2 := Zproc_le hb ε hε h (j + 1) P
    have h3 := Zmean_nonneg hb ε h j P
    have h4 := Zmean_le hb hj ε hε P
    have h5 : |Zproc ε b h (j + 1) P - Zmean ε b h j P| ≤ n := by
      rw [abs_le]
      constructor <;> linarith
    calc -t * (Zproc ε b h (j + 1) P - Zmean ε b h j P)
        ≤ |-t * (Zproc ε b h (j + 1) P - Zmean ε b h j P)| := le_abs_self _
      _ = |t| * |Zproc ε b h (j + 1) P - Zmean ε b h j P| := by rw [abs_mul, abs_neg]
      _ ≤ |t| * n := mul_le_mul_of_nonneg_left h5 (abs_nonneg t)
  -- Step 2 for each factor, with `-t` in place of `t`: `E[W_j | 𝓕_j] ≤ exp(n t² / (2M²))`
  have hcond : ∀ j < h, ∀ᵐ P ∂pointSampleLaw n,
      ((pointSampleLaw n)[W j | stageFiltration n b hb j]) P ≤ Real.exp c0 := by
    intro j hj
    have hstep := condExp_exp_step hb hj ε hε (-t)
    rw [neg_sq, ← hc0] at hstep
    exact hstep
  -- the product of the factors is `e^{-tT}`
  have he : ∀ P, Real.exp (-t * fluctStep ε b h P) = ∏ j ∈ Finset.range h, W j P := by
    intro P
    unfold fluctStep
    rw [Finset.mul_sum, Real.exp_sum]
  calc ∫ P, Real.exp (-t * fluctStep ε b h P) ∂pointSampleLaw n
      = ∫ P, ∏ j ∈ Finset.range h, W j P ∂pointSampleLaw n :=
        integral_congr_ae (Filter.Eventually.of_forall he)
    _ ≤ ∏ _j ∈ Finset.range h, Real.exp c0 :=
        -- conditioning successively on `𝓕_{h-1}, 𝓕_{h-2}, …, 𝓕_0`, with Step 2 each time
        integral_prod_le_of_condExp_le (stageFiltration n b hb) W (fun _ => Real.exp c0)
          (Real.exp (|t| * n)) h hW hbound (fun _ _ => (Real.exp_pos c0).le) hcond
    _ = Real.exp (h * c0) := by
        -- multiplying the `h` bounds
        rw [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]

/-! ### The displays of Steps 2 and 3 in the manuscript's terms -/

/-- Almost surely, the fluctuation term `T` of display (10) is the sum of the centered
increments with the conditional expectations written as averages over the next digits. -/
lemma fluct_ae_eq {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) :
    fluct χ b h =ᵐ[pointSampleLaw n] fluctStep (sgn χ) b h := by
  have hall : ∀ᵐ P ∂pointSampleLaw n, ∀ j ∈ Finset.range h,
      Zpot χ b h (j + 1) P - ((pointSampleLaw n)[Zpot χ b h (j + 1) | stageSigma n b j]) P =
        Zproc (sgn χ) b h (j + 1) P - Zmean (sgn χ) b h j P := by
    refine (ae_ball_iff (Finset.range h).countable_toSet).mpr fun j hj => ?_
    have hj' : j < h := Finset.mem_range.mp hj
    filter_upwards [Zpot_ae_eq_Zproc hb (by omega : j + 1 ≤ h) χ,
      condExp_Zpot_succ hb hj' χ] with P h1 h2
    rw [h1, h2]
  unfold fluct fluctStep
  rw [← pointSampleLaw_eq_unifPts]
  filter_upwards [hall] with P hP
  exact Finset.sum_congr rfl hP

/-- Almost surely, `T_j = Z_{j+1} - E[Z_{j+1} | 𝓕_j]` is the centered increment of
`condExp_exp_step`: `Z_{j+1}` read from the heights and the indices, minus its average over the
next digits. -/
lemma fluctTerm_ae_eq {b h j : ℕ} (hb : 0 < b) (hj : j < h) (χ : Fin n → ℤˣ) :
    (fun P => Zpot χ b h (j + 1) P - ((unifPts n)[Zpot χ b h (j + 1) | stageSigma n b j]) P)
      =ᵐ[unifPts n] fun P => Zproc (sgn χ) b h (j + 1) P - Zmean (sgn χ) b h j P := by
  rw [← pointSampleLaw_eq_unifPts]
  filter_upwards [Zpot_ae_eq_Zproc hb (by omega : j + 1 ≤ h) χ,
    condExp_Zpot_succ hb hj χ] with P h1 h2
  rw [h1, h2]

/-- For a finite measure, `e^{-tX}` is integrable if `X` is almost everywhere equal to a
measurable function `Y` with `|Y| ≤ B`. -/
lemma integrable_exp_neg_of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hXY : X =ᵐ[μ] Y) (hY : Measurable Y) {B : ℝ}
    (hB : ∀ ω, |Y ω| ≤ B) (t : ℝ) :
    Integrable (fun ω => Real.exp (-t * X ω)) μ := by
  -- `Y` is measurable with values in `[-B, B]`, so `e^{-tY}` is measurable and bounded
  have hint : Integrable (fun ω => Real.exp (-t * Y ω)) μ :=
    integrable_exp_mul_of_mem_Icc hY.aemeasurable
      (Filter.Eventually.of_forall fun ω => abs_le.mp (hB ω))
  refine hint.congr ?_
  filter_upwards [hXY] with ω hω
  rw [hω]

/-- `e^{-t T_j}` is integrable: almost surely, `T_j` is a measurable function with `|T_j| ≤ n`.
So the conditional expectation in `lemma_2_6_step2` is that of an integrable function. -/
lemma integrable_exp_neg_fluctTerm {b h j : ℕ} (hb : 0 < b) (hj : j < h) (χ : Fin n → ℤˣ)
    (t : ℝ) :
    Integrable (fun P => Real.exp (-t * (Zpot χ b h (j + 1) P -
      ((unifPts n)[Zpot χ b h (j + 1) | stageSigma n b j]) P))) (unifPts n) := by
  have hε : ∀ i, |sgn χ i| ≤ 1 := fun i => (abs_sgn χ i).le
  refine integrable_exp_neg_of_ae_eq (fluctTerm_ae_eq hb hj χ)
    ((measurable_Zproc hb (sgn χ) h (j + 1)).sub (measurable_Zmean hb (sgn χ) h j))
    (B := n) (fun P => ?_) t
  -- both `Z_{j+1}` and its average over the next digits lie in `[0, n]`
  have h1 := Zproc_nonneg hb (sgn χ) h (j + 1) P
  have h2 := Zproc_le hb (sgn χ) hε h (j + 1) P
  have h3 := Zmean_nonneg hb (sgn χ) h j P
  have h4 := Zmean_le hb hj (sgn χ) hε P
  rw [abs_le]
  constructor <;> linarith

/-- **Step 2 of the proof of Lemma 2.6**, as displayed: with `T_j = Z_{j+1} - E[Z_{j+1} | 𝓕_j]`,
almost surely `E[e^{-t T_j} | 𝓕_j] ≤ exp(n t² / (2M²))`. (The manuscript states it for `t > 0`;
it holds for every real `t`.) -/
theorem lemma_2_6_step2 {b h j : ℕ} (hb : 0 < b) (hj : j < h) (χ : Fin n → ℤˣ) (t : ℝ) :
    ∀ᵐ P ∂unifPts n,
      ((unifPts n)[fun P => Real.exp (-t * (Zpot χ b h (j + 1) P -
          ((unifPts n)[Zpot χ b h (j + 1) | stageSigma n b j]) P)) | stageSigma n b j]) P ≤
        Real.exp (n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2)) := by
  have hε : ∀ i, |sgn χ i| ≤ 1 := fun i => (abs_sgn χ i).le
  -- almost surely, `e^{-t T_j}` is the function of `condExp_exp_step`, with `-t` in place of `t`
  have hcongr : (fun P => Real.exp (-t * (Zpot χ b h (j + 1) P -
      ((unifPts n)[Zpot χ b h (j + 1) | stageSigma n b j]) P))) =ᵐ[unifPts n]
      fun P => Real.exp (-t * (Zproc (sgn χ) b h (j + 1) P - Zmean (sgn χ) b h j P)) := by
    filter_upwards [fluctTerm_ae_eq hb hj χ] with P hP
    rw [hP]
  -- Step 1 and Fact A.1, with `c = 1/M`
  have hstep := condExp_exp_step hb hj (sgn χ) hε (-t)
  rw [pointSampleLaw_eq_unifPts] at hstep
  filter_upwards [hstep, condExp_congr_ae (m := stageSigma n b j) hcongr] with P hP hP'
  rw [hP']
  refine hP.trans_eq ?_
  congr 1
  ring

/-- `e^{-tT}` is integrable: almost surely, `T` is a measurable function with `|T| ≤ hn`. So
the expectation in `lemma_2_6_step3` is that of an integrable function. -/
lemma integrable_exp_neg_fluct {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (t : ℝ) :
    Integrable (fun P => Real.exp (-t * fluct χ b h P)) (unifPts n) := by
  have hT := fluct_ae_eq hb h χ
  rw [pointSampleLaw_eq_unifPts] at hT
  exact integrable_exp_neg_of_ae_eq hT (measurable_fluctStep hb (sgn χ) h)
    (abs_fluctStep_le hb (sgn χ) (fun i => (abs_sgn χ i).le) h) t

/-- **Step 3 of the proof of Lemma 2.6**, as displayed: `E e^{-tT} ≤ exp(h n t² / (2M²))`. -/
theorem lemma_2_6_step3 {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (t : ℝ) :
    ∫ P, Real.exp (-t * fluct χ b h P) ∂unifPts n ≤
      Real.exp (h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2)) := by
  have hε : ∀ i, |sgn χ i| ≤ 1 := fun i => (abs_sgn χ i).le
  rw [← pointSampleLaw_eq_unifPts]
  -- almost surely, `T` is the sum of the centered increments of `integral_exp_neg_sum_le`
  have hcongr : (fun P => Real.exp (-t * fluct χ b h P)) =ᵐ[pointSampleLaw n]
      fun P => Real.exp (-t * fluctStep (sgn χ) b h P) := by
    filter_upwards [fluct_ae_eq hb h χ] with P hP
    rw [hP]
  rw [integral_congr_ae hcongr]
  -- conditioning successively on `𝓕_{h-1}, 𝓕_{h-2}, …, 𝓕_0` and applying Step 2 each time
  refine (integral_exp_neg_sum_le hb (sgn χ) hε h t).trans_eq ?_
  congr 1
  ring

/-! ### Lemma 2.6 -/

/-- **Markov's inequality in Step 3 of the proof of Lemma 2.6**: for every `t > 0`,
`Pr(T ≤ -λ) ≤ exp(-tλ + h n t² / (2M²))`. "By Markov's inequality,
`Pr(T ≤ -λ) = Pr(e^{-tT} ≥ e^{tλ}) ≤ exp(-tλ + hnt²/(2M²))`". -/
theorem lemma_2_6_markov {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (lam : ℝ) {t : ℝ}
    (ht : 0 < t) :
    (unifPts n).real {P | fluct χ b h P ≤ -lam} ≤
      Real.exp (-t * lam + h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2)) := by
  calc (unifPts n).real {P | fluct χ b h P ≤ -lam}
      ≤ Real.exp (t * -lam) * ∫ P, Real.exp (-t * fluct χ b h P) ∂unifPts n :=
        -- Markov's inequality: `Pr(T ≤ -λ) = Pr(e^{-tT} ≥ e^{tλ}) ≤ e^{-tλ} E e^{-tT}`
        measureReal_le_exp_mul_integral_exp_neg (fluct χ b h) ht
          (integrable_exp_neg_fluct hb h χ t) (-lam)
    _ ≤ Real.exp (t * -lam) * Real.exp (h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2)) :=
        -- Step 3: `E e^{-tT} ≤ exp(h n t² / (2M²))`
        mul_le_mul_of_nonneg_left (lemma_2_6_step3 hb h χ t) (Real.exp_pos _).le
    _ = Real.exp (-t * lam + h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2)) := by
        rw [← Real.exp_add, mul_neg, ← neg_mul]

/-- **Lemma 2.6 (fluctuations).** Fix a coloring, and let
`T = Σ_{j<h} (Z_{j+1} - E[Z_{j+1} | 𝓕_j])` be the fluctuation term of (10). Then, for every
`λ > 0`,

`Pr(T ≤ -λ) ≤ exp(-λ² M² / (2hn))`,   `M = b^{h-1}`. -/
theorem lemma_2_6 {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) {lam : ℝ} (hlam : 0 < lam) :
    (unifPts n).real {P | fluct χ b h P ≤ -lam} ≤
      Real.exp (-(lam ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (2 * h * n))) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- if there are no transitions or no points, the bound is `1`
  by_cases hdeg : h = 0 ∨ n = 0
  · have : (2 : ℝ) * h * n = 0 := by
      rcases hdeg with rfl | rfl <;> simp
    rw [this, div_zero, neg_zero, Real.exp_zero]
    exact measureReal_le_one
  have hh : 0 < h := Nat.pos_of_ne_zero fun h0 => hdeg (Or.inl h0)
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hdeg (Or.inr h0)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  -- Step 3 and Markov's inequality (`lemma_2_6_markov`), for `t = λM²/(hn)`:
  -- `Pr(T ≤ -λ) ≤ exp(-tλ + hnt²/(2M²))`
  set t : ℝ := lam * ((b : ℝ) ^ (h - 1)) ^ 2 / (h * n) with ht
  have htpos : 0 < t := by positivity
  refine (lemma_2_6_markov hb h χ lam htpos).trans_eq ?_
  -- "the choice `t = λM²/(hn)` gives the claim": the exponent is `-λ²M²/(2hn)`
  congr 1
  rw [ht]
  field_simp
  ring

end

end R56Audit
