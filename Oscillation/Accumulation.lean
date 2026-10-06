import Oscillation.Exponential

/-! One-directional accumulation of the actual finite conditional drift. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma sum_increments (Z : ℕ → Ω → ℝ) (h : ℕ) (ω : Ω) :
    ∑ j ∈ range h, (Z (j + 1) ω - Z j ω) = Z h ω - Z 0 ω := by
  induction h with
  | zero => simp
  | succ h ih => rw [Finset.sum_range_succ, ih]; ring

/-- The finite-coordinate conditional laws are used at every layer, so the
accumulation theorem assumes no one-step exponential bound. -/
theorem integral_exp_accumulated_le {α : Type*} [Fintype α] [Nonempty α]
    (ℱ : Filtration ℕ mΩ) (n h : ℕ) (Z S : ℕ → Ω → ℝ)
    (Y : ℕ → Ω → (Fin n → α) → ℝ)
    (hZ : StronglyAdapted ℱ Z) (hS : StronglyAdapted ℱ S)
    (K : ℝ) (hbound : ∀ j ω, |Z j ω| ≤ K ∧ |S j ω| ≤ K)
    (hstart : ∀ ω, Z 0 ω = 0) {d : ℝ} (hd : 0 ≤ d) (u : ℝ) (hu : 0 ≤ u)
    (hlaw : ∀ j < h, HasFiniteConditionalLaw (μ := μ) (ℱ j) (Z (j + 1)) (Y j))
    (hosc : ∀ j < h, ∀ᵐ ω ∂μ, CoordinateOscillation (Y j ω) d)
    (hmean : ∀ j < h, ∀ᵐ ω ∂μ, S j ω ≤ finAvg (Y j ω) - Z j ω) :
    (∫ ω, Real.exp (-u * Z h ω + u * ∑ j ∈ range h, S j ω) ∂μ) ≤
      Real.exp ((h : ℝ) * n * u ^ 2 * d ^ 2 / 2) := by
  let c := (n : ℝ) * u ^ 2 * d ^ 2 / 2
  let W : ℕ → Ω → ℝ := fun j ω ↦ Real.exp (-u * (Z (j + 1) ω - Z j ω) + u * S j ω - c)
  have hW : ∀ j, StronglyMeasurable[ℱ (j + 1)] (W j) := by
    intro j
    have hz1 := (hZ (j + 1)).measurable
    have hz0 := ((hZ j).mono (ℱ.mono (Nat.le_succ j))).measurable
    have hs := ((hS j).mono (ℱ.mono (Nat.le_succ j))).measurable
    apply Measurable.stronglyMeasurable
    dsimp [W]
    fun_prop
  have hWbound : ∀ j ω, 0 ≤ W j ω ∧ W j ω ≤ Real.exp (3 * u * K + |c|) := by
    intro j ω
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩
    have hx := (abs_le.mp (hbound (j + 1) ω).1).1
    have hz := (abs_le.mp (hbound j ω).1).2
    have hs := (abs_le.mp (hbound j ω).2).2
    have hc := neg_le_abs c
    nlinarith
  have hWcond : ∀ j < h, ∀ᵐ ω ∂μ, (μ[W j | ℱ j]) ω ≤ 1 := by
    intro j hj
    exact condExp_exp_drift_le_of_finite_law (ℱ.le j) n (Z (j + 1)) (Z j) (S j) (Y j)
      ((hZ (j + 1)).mono (ℱ.le (j + 1))).measurable (hZ j) (hS j) K
      (fun ω ↦ ⟨(hbound (j + 1) ω).1, hbound j ω⟩) hd u hu
      (hlaw j hj) (hosc j hj) (hmean j hj)
  have hprod := integral_prefixProduct_le_of_cond ℱ W (Real.exp (3 * u * K + |c|)) hW hWbound h hWcond
  have heq (ω : Ω) : Riesz.prefixProduct W h ω =
      Real.exp (-u * Z h ω + u * ∑ j ∈ range h, S j ω - h * c) := by
    simp only [Riesz.prefixProduct, W, ← Real.exp_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_increments, hstart]
    simp only [sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hacc : (∫ ω, Real.exp (-u * Z h ω + u * ∑ j ∈ range h, S j ω - h * c) ∂μ) ≤ 1 := by
    simpa only [heq] using hprod
  calc
    _ = Real.exp (h * c) *
        ∫ ω, Real.exp (-u * Z h ω + u * ∑ j ∈ range h, S j ω - h * c) ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω ↦ by
        dsimp only
        rw [← Real.exp_add]
        congr 1
        ring)
    _ ≤ Real.exp (h * c) * 1 := mul_le_mul_of_nonneg_left hacc (Real.exp_pos _).le
    _ = _ := by dsimp [c]; rw [mul_one]; congr 1; ring

omit [IsProbabilityMeasure μ] in
lemma integral_finAvg {ι : Type*} [Fintype ι] (F : ι → Ω → ℝ)
    (hF : ∀ i, Integrable (F i) μ) :
    (∫ ω, finAvg (fun i ↦ F i ω) ∂μ) = finAvg (fun i ↦ ∫ ω, F i ω ∂μ) := by
  simp only [finAvg, integral_div, integral_finsetSum Finset.univ (fun i _ ↦ hF i)]

/-- Equal marginal distributions suffice for the convexity reduction; no
independence between the layers is used. -/
theorem integral_exp_sum_le_single (h : ℕ) (hh : 0 < h) (S : ℕ → Ω → ℝ)
    (hS : ∀ j < h, Measurable (S j)) (K : ℝ)
    (hbound : ∀ j < h, ∀ ω, |S j ω| ≤ K) (u : ℝ) (hu : 0 ≤ u)
    (hsame : ∀ j < h, (∫ ω, Real.exp (-u * h * S j ω) ∂μ) =
      ∫ ω, Real.exp (-u * h * S 0 ω) ∂μ) :
    (∫ ω, Real.exp (-u * ∑ j ∈ range h, S j ω) ∂μ) ≤
      ∫ ω, Real.exp (-u * h * S 0 ω) ∂μ := by
  let : NeZero h := ⟨by omega⟩
  have hi (j : Fin h) : Integrable (fun ω ↦ Real.exp (-u * h * S j ω)) μ :=
    integrable_exp_of_bounded ((hS j j.isLt).const_mul (-u * h)) (u * h * K) (fun ω ↦ by
      have hs := (abs_le.mp (hbound j j.isLt ω)).1
      have hp : 0 ≤ u * (h : ℝ) := by positivity
      nlinarith)
  have hfin : Integrable (fun ω ↦ finAvg (fun j : Fin h ↦ Real.exp (-u * h * S j ω))) μ := by
    unfold finAvg
    exact (integrable_finsetSum Finset.univ (fun j _ ↦ hi j)).div_const _
  have hsum (ω : Ω) : finAvg (fun j : Fin h ↦ -u * h * S j ω) =
      -u * ∑ j ∈ range h, S j ω := by
    rw [finAvg_const_mul]
    simp only [finAvg, Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ S j ω) h]
    have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp
  have hm : Measurable (fun ω ↦ -u * ∑ j ∈ range h, S j ω) := by
    apply Measurable.const_mul
    exact Finset.measurable_sum _ (fun j hj ↦ hS j (Finset.mem_range.mp hj))
  have hInt := integrable_exp_of_bounded (μ := μ) hm (u * h * K) (fun ω ↦ by
    have hs : -(h : ℝ) * K ≤ ∑ j ∈ range h, S j ω := by
      calc
        _ = ∑ _j ∈ range h, -K := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j hj ↦ (abs_le.mp (hbound j (Finset.mem_range.mp hj) ω)).1)
    nlinarith)
  calc
    _ ≤ ∫ ω, finAvg (fun j : Fin h ↦ Real.exp (-u * h * S j ω)) ∂μ := by
      apply integral_mono hInt hfin
      intro ω
      dsimp only
      rw [← hsum]
      exact exp_finAvg_le_finAvg_exp _
    _ = finAvg (fun j : Fin h ↦ ∫ ω, Real.exp (-u * h * S j ω) ∂μ) := integral_finAvg _ hi
    _ = _ := by simp_rw [hsame _ (Fin.isLt _)]; exact finAvg_const _

/-- Subtracting the deterministic cost gives the compensated expectation at
most one. This form can be integrated over a second, initially fixed coordinate. -/
theorem integral_exp_compensated_le {α : Type*} [Fintype α] [Nonempty α]
    (ℱ : Filtration ℕ mΩ) (n h : ℕ) (Z S : ℕ → Ω → ℝ)
    (Y : ℕ → Ω → (Fin n → α) → ℝ)
    (hZ : StronglyAdapted ℱ Z) (hS : StronglyAdapted ℱ S)
    (K : ℝ) (hbound : ∀ j ω, |Z j ω| ≤ K ∧ |S j ω| ≤ K)
    (hstart : ∀ ω, Z 0 ω = 0) {d : ℝ} (hd : 0 ≤ d) (u : ℝ) (hu : 0 ≤ u)
    (hlaw : ∀ j < h, HasFiniteConditionalLaw (μ := μ) (ℱ j) (Z (j + 1)) (Y j))
    (hosc : ∀ j < h, ∀ᵐ ω ∂μ, CoordinateOscillation (Y j ω) d)
    (hmean : ∀ j < h, ∀ᵐ ω ∂μ, S j ω ≤ finAvg (Y j ω) - Z j ω) :
    (∫ ω, Real.exp (-u * Z h ω + u * ∑ j ∈ range h, S j ω -
      (h : ℝ) * n * u ^ 2 * d ^ 2 / 2) ∂μ) ≤ 1 := by
  let c := (h : ℝ) * n * u ^ 2 * d ^ 2 / 2
  have hh := integral_exp_accumulated_le ℱ n h Z S Y hZ hS K hbound hstart hd u hu hlaw hosc hmean
  calc
    _ = Real.exp (-c) * (∫ ω, Real.exp (-u * Z h ω + u * ∑ j ∈ range h, S j ω) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω ↦ by
        dsimp only
        rw [← Real.exp_add]
        congr 1
        dsimp [c]
        ring)
    _ ≤ Real.exp (-c) * Real.exp c := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- After the compensated estimate is proved, Cauchy--Schwarz and convexity
use only the marginal law at each layer. This theorem can therefore be applied
after integrating out any initially conditioned coordinates. -/
theorem integral_exp_terminal_le_of_compensated (h : ℕ) (hh : 0 < h)
    (X : Ω → ℝ) (S : ℕ → Ω → ℝ) (hX : Measurable X)
    (hS : ∀ j < h, Measurable (S j)) (K : ℝ)
    (hXb : ∀ ω, |X ω| ≤ K) (hSb : ∀ j < h, ∀ ω, |S j ω| ≤ K)
    (t a c : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hcomp : (∫ ω, Real.exp (-2 * t * X ω + a * ∑ j ∈ range h, S j ω - c) ∂μ) ≤ 1)
    (hsame : ∀ j < h, (∫ ω, Real.exp (-a * h * S j ω) ∂μ) =
      ∫ ω, Real.exp (-a * h * S 0 ω) ∂μ) :
    (∫ ω, Real.exp (-t * X ω) ∂μ) ≤
      Real.exp (c / 2) * Real.sqrt (∫ ω, Real.exp (-a * h * S 0 ω) ∂μ) := by
  let T : Ω → ℝ := fun ω ↦ ∑ j ∈ range h, S j ω
  have hT : Measurable T := Finset.measurable_sum _
    (fun j hj ↦ hS j (Finset.mem_range.mp hj))
  have hTb (ω : Ω) : -(h : ℝ) * K ≤ T ω ∧ T ω ≤ h * K := by
    constructor
    · calc
        _ = ∑ _j ∈ range h, -K := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j hj ↦ (abs_le.mp (hSb j (Finset.mem_range.mp hj) ω)).1)
    · calc
        _ ≤ ∑ _j ∈ range h, K := Finset.sum_le_sum
          (fun j hj ↦ (abs_le.mp (hSb j (Finset.mem_range.mp hj) ω)).2)
        _ = _ := by simp
  let A : Ω → ℝ := fun ω ↦ -2 * t * X ω + a * T ω - c
  let B : Ω → ℝ := fun ω ↦ -a * T ω
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hAb (ω : Ω) : A ω ≤ 2 * t * K + a * h * K + |c| := by
    have hx := (abs_le.mp (hXb ω)).1
    have hs := (hTb ω).2
    have hc := neg_le_abs c
    dsimp [A]
    nlinarith
  have hBb (ω : Ω) : B ω ≤ a * h * K := by
    have hs := (hTb ω).1
    dsimp [B]
    nlinarith
  have hcs := integral_exp_split_le (μ := μ) A B hA hB
    (2 * t * K + a * h * K + |c|) (a * h * K) hAb hBb
  have hAsqrt : Real.sqrt (∫ ω, Real.exp (A ω) ∂μ) ≤ 1 :=
    (Real.sqrt_le_sqrt hcomp).trans_eq (by norm_num)
  have hj := integral_exp_sum_le_single h hh S hS K hSb a ha hsame
  calc
    _ = Real.exp (c / 2) * (∫ ω, Real.exp ((A ω + B ω) / 2) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω ↦ by
        dsimp only
        rw [← Real.exp_add]
        congr 1
        dsimp [A, B]
        ring)
    _ ≤ Real.exp (c / 2) * (Real.sqrt (∫ ω, Real.exp (A ω) ∂μ) *
        Real.sqrt (∫ ω, Real.exp (B ω) ∂μ)) :=
      mul_le_mul_of_nonneg_left hcs (Real.exp_pos _).le
    _ ≤ Real.exp (c / 2) * Real.sqrt (∫ ω, Real.exp (B ω) ∂μ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hAsqrt (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hj) (Real.exp_pos _).le

/-- The manuscript's exact Cauchy--Schwarz and equal-marginal conclusion,
with constants left unchanged. The compensated premise is supplied by
`integral_exp_compensated_le`, possibly after a further integration. -/
theorem integral_exp_oscillation_laplace (n h : ℕ) (hh : 0 < h) (b M : ℝ)
    (hb : 0 < b) (hM : 0 < M) (X : Ω → ℝ) (S : ℕ → Ω → ℝ)
    (hX : Measurable X) (hS : ∀ j < h, Measurable (S j)) (K : ℝ)
    (hXb : ∀ ω, |X ω| ≤ K) (hSb : ∀ j < h, ∀ ω, |S j ω| ≤ K)
    (hcomp : (∫ ω, Real.exp (-2 * M * X ω / Real.sqrt h +
      (∑ j ∈ range h, S j ω) / (2 * b * Real.sqrt h) - 2 * n) ∂μ) ≤ 1)
    (hsame : ∀ j < h, (∫ ω, Real.exp (-Real.sqrt h * S j ω / (2 * b)) ∂μ) =
      ∫ ω, Real.exp (-Real.sqrt h * S 0 ω / (2 * b)) ∂μ) :
    (∫ ω, Real.exp (-M * X ω / Real.sqrt h) ∂μ) ≤
      Real.exp n * Real.sqrt (∫ ω, Real.exp (-Real.sqrt h * S 0 ω / (2 * b)) ∂μ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hroot : 0 < Real.sqrt (h : ℝ) := Real.sqrt_pos.2 hhR
  have hsq := Real.sq_sqrt hhR.le
  have hid : 1 / (2 * b * Real.sqrt h) * h = Real.sqrt h / (2 * b) := by
    field_simp
    nlinarith
  have hex (z : ℝ) : -(1 / (2 * b * Real.sqrt h)) * h * z =
      -Real.sqrt h * z / (2 * b) := by
    calc
      _ = -(1 / (2 * b * Real.sqrt h) * h) * z := by ring
      _ = _ := by rw [hid]; ring
  have hc : (∫ ω, Real.exp (-2 * (M / Real.sqrt h) * X ω +
      1 / (2 * b * Real.sqrt h) * ∑ j ∈ range h, S j ω - 2 * n) ∂μ) ≤ 1 := by
    convert hcomp using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω ↦ by dsimp only; congr 1; ring)
  have hs : ∀ j < h, (∫ ω, Real.exp (-(1 / (2 * b * Real.sqrt h)) * h * S j ω) ∂μ) =
      ∫ ω, Real.exp (-(1 / (2 * b * Real.sqrt h)) * h * S 0 ω) ∂μ := by
    simpa only [hex] using hsame
  have hout := integral_exp_terminal_le_of_compensated h hh X S hX hS K hXb hSb
    (M / Real.sqrt h) (1 / (2 * b * Real.sqrt h)) (2 * n) (by positivity) (by positivity) hc hs
  simp only [hex, show (2 * (n : ℝ)) / 2 = n by ring] at hout
  convert hout using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω ↦ by dsimp only; congr 1; ring)

/-- Uniform marginal bounds suffice in place of equality of laws. -/
theorem integral_exp_sum_le_marginal_bound (h : ℕ) (hh : 0 < h) (S : ℕ → Ω → ℝ)
    (hS : ∀ j < h, Measurable (S j)) (K : ℝ)
    (hbound : ∀ j < h, ∀ ω, |S j ω| ≤ K) (u B0 : ℝ) (hu : 0 ≤ u)
    (hLap : ∀ j < h, (∫ ω, Real.exp (-u * h * S j ω) ∂μ) ≤ B0) :
    (∫ ω, Real.exp (-u * ∑ j ∈ range h, S j ω) ∂μ) ≤
      B0 := by
  let : NeZero h := ⟨by omega⟩
  have hi (j : Fin h) : Integrable (fun ω ↦ Real.exp (-u * h * S j ω)) μ :=
    integrable_exp_of_bounded ((hS j j.isLt).const_mul (-u * h)) (u * h * K) (fun ω ↦ by
      have hs := (abs_le.mp (hbound j j.isLt ω)).1
      have hp : 0 ≤ u * (h : ℝ) := by positivity
      nlinarith)
  have hfin : Integrable (fun ω ↦ finAvg (fun j : Fin h ↦ Real.exp (-u * h * S j ω))) μ := by
    unfold finAvg
    exact (integrable_finsetSum Finset.univ (fun j _ ↦ hi j)).div_const _
  have hsum (ω : Ω) : finAvg (fun j : Fin h ↦ -u * h * S j ω) =
      -u * ∑ j ∈ range h, S j ω := by
    rw [finAvg_const_mul]
    simp only [finAvg, Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ S j ω) h]
    have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp
  have hm : Measurable (fun ω ↦ -u * ∑ j ∈ range h, S j ω) := by
    apply Measurable.const_mul
    exact Finset.measurable_sum _ (fun j hj ↦ hS j (Finset.mem_range.mp hj))
  have hInt := integrable_exp_of_bounded (μ := μ) hm (u * h * K) (fun ω ↦ by
    have hs : -(h : ℝ) * K ≤ ∑ j ∈ range h, S j ω := by
      calc
        _ = ∑ _j ∈ range h, -K := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j hj ↦ (abs_le.mp (hbound j (Finset.mem_range.mp hj) ω)).1)
    nlinarith)
  calc
    _ ≤ ∫ ω, finAvg (fun j : Fin h ↦ Real.exp (-u * h * S j ω)) ∂μ := by
      apply integral_mono hInt hfin
      intro ω
      dsimp only
      rw [← hsum]
      exact exp_finAvg_le_finAvg_exp _
    _ = finAvg (fun j : Fin h ↦ ∫ ω, Real.exp (-u * h * S j ω) ∂μ) := integral_finAvg _ hi
    _ ≤ B0 := (finAvg_mono (fun j : Fin h ↦ hLap j j.isLt)).trans_eq (finAvg_const B0)

theorem integral_exp_terminal_le_of_compensated_marginal_bound (h : ℕ) (hh : 0 < h)
    (X : Ω → ℝ) (S : ℕ → Ω → ℝ) (hX : Measurable X)
    (hS : ∀ j < h, Measurable (S j)) (K : ℝ)
    (hXb : ∀ ω, |X ω| ≤ K) (hSb : ∀ j < h, ∀ ω, |S j ω| ≤ K)
    (t a c B0 : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hcomp : (∫ ω, Real.exp (-2 * t * X ω + a * ∑ j ∈ range h, S j ω - c) ∂μ) ≤ 1)
    (hLap : ∀ j < h, (∫ ω, Real.exp (-a * h * S j ω) ∂μ) ≤ B0) :
    (∫ ω, Real.exp (-t * X ω) ∂μ) ≤
      Real.exp (c / 2) * Real.sqrt B0 := by
  let T : Ω → ℝ := fun ω ↦ ∑ j ∈ range h, S j ω
  have hT : Measurable T := Finset.measurable_sum _
    (fun j hj ↦ hS j (Finset.mem_range.mp hj))
  have hTb (ω : Ω) : -(h : ℝ) * K ≤ T ω ∧ T ω ≤ h * K := by
    constructor
    · calc
        _ = ∑ _j ∈ range h, -K := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j hj ↦ (abs_le.mp (hSb j (Finset.mem_range.mp hj) ω)).1)
    · calc
        _ ≤ ∑ _j ∈ range h, K := Finset.sum_le_sum
          (fun j hj ↦ (abs_le.mp (hSb j (Finset.mem_range.mp hj) ω)).2)
        _ = _ := by simp
  let A : Ω → ℝ := fun ω ↦ -2 * t * X ω + a * T ω - c
  let B : Ω → ℝ := fun ω ↦ -a * T ω
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hAb (ω : Ω) : A ω ≤ 2 * t * K + a * h * K + |c| := by
    have hx := (abs_le.mp (hXb ω)).1
    have hs := (hTb ω).2
    have hc := neg_le_abs c
    dsimp [A]
    nlinarith
  have hBb (ω : Ω) : B ω ≤ a * h * K := by
    have hs := (hTb ω).1
    dsimp [B]
    nlinarith
  have hcs := integral_exp_split_le (μ := μ) A B hA hB
    (2 * t * K + a * h * K + |c|) (a * h * K) hAb hBb
  have hAsqrt : Real.sqrt (∫ ω, Real.exp (A ω) ∂μ) ≤ 1 :=
    (Real.sqrt_le_sqrt hcomp).trans_eq (by norm_num)
  have hj := integral_exp_sum_le_marginal_bound h hh S hS K hSb a B0 ha hLap
  calc
    _ = Real.exp (c / 2) * (∫ ω, Real.exp ((A ω + B ω) / 2) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω ↦ by
        dsimp only
        rw [← Real.exp_add]
        congr 1
        dsimp [A, B]
        ring)
    _ ≤ Real.exp (c / 2) * (Real.sqrt (∫ ω, Real.exp (A ω) ∂μ) *
        Real.sqrt (∫ ω, Real.exp (B ω) ∂μ)) :=
      mul_le_mul_of_nonneg_left hcs (Real.exp_pos _).le
    _ ≤ Real.exp (c / 2) * Real.sqrt (∫ ω, Real.exp (B ω) ∂μ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hAsqrt (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hj) (Real.exp_pos _).le

theorem integral_exp_oscillation_laplace_of_marginal_bound (n h : ℕ) (hh : 0 < h) (b M : ℝ)
    (hb : 0 < b) (hM : 0 < M) (X : Ω → ℝ) (S : ℕ → Ω → ℝ)
    (hX : Measurable X) (hS : ∀ j < h, Measurable (S j)) (K B0 : ℝ)
    (hXb : ∀ ω, |X ω| ≤ K) (hSb : ∀ j < h, ∀ ω, |S j ω| ≤ K)
    (hcomp : (∫ ω, Real.exp (-2 * M * X ω / Real.sqrt h +
      (∑ j ∈ range h, S j ω) / (2 * b * Real.sqrt h) - 2 * n) ∂μ) ≤ 1)
    (hLap : ∀ j < h, (∫ ω, Real.exp (-Real.sqrt h * S j ω / (2 * b)) ∂μ) ≤ B0) :
    (∫ ω, Real.exp (-M * X ω / Real.sqrt h) ∂μ) ≤
      Real.exp n * Real.sqrt B0 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hroot : 0 < Real.sqrt (h : ℝ) := Real.sqrt_pos.2 hhR
  have hsq := Real.sq_sqrt hhR.le
  have hid : 1 / (2 * b * Real.sqrt h) * h = Real.sqrt h / (2 * b) := by
    field_simp
    nlinarith
  have hex (z : ℝ) : -(1 / (2 * b * Real.sqrt h)) * h * z =
      -Real.sqrt h * z / (2 * b) := by
    calc
      _ = -(1 / (2 * b * Real.sqrt h) * h) * z := by ring
      _ = _ := by rw [hid]; ring
  have hc : (∫ ω, Real.exp (-2 * (M / Real.sqrt h) * X ω +
      1 / (2 * b * Real.sqrt h) * ∑ j ∈ range h, S j ω - 2 * n) ∂μ) ≤ 1 := by
    convert hcomp using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω ↦ by dsimp only; congr 1; ring)
  have hs : ∀ j < h, (∫ ω, Real.exp (-(1 / (2 * b * Real.sqrt h)) * h * S j ω) ∂μ) ≤ B0 := by
    simpa only [hex] using hLap
  have hout := integral_exp_terminal_le_of_compensated_marginal_bound h hh X S hX hS K hXb hSb
    (M / Real.sqrt h) (1 / (2 * b * Real.sqrt h)) (2 * n) B0 (by positivity) (by positivity) hc hs
  simp only [show (2 * (n : ℝ)) / 2 = n by ring] at hout
  convert hout using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω ↦ by dsimp only; congr 1; ring)

end
end Oscillation
