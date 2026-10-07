import Oscillation
import R56Audit.GridDrift
import R56Audit.ArchiveRoute

/-!
# The archive's finite-probe route to Proposition 2.7, for every integer base `b ≥ 3`

Auditor's supplement (not part of the audited archive).

This file belongs to the archive's route, not to the manuscript's. It is the archive's
finite-probe proof of Proposition 2.7 with the parity restriction removed: a second proof of
display (14). The proof that follows the manuscript (the potential of display (1) and
Lemmas 2.4, 2.5 and 2.6) is `proposition_2_7` in `Simultaneous.lean`; Theorem 1.1 is derived
from that one in `Parameters.lean`, and nothing of the present file is used there.

In the archive the parity hypothesis `Even b` enters the proof of the main theorem at one
place, the conditional gain `Oscillation.gridPotential_drift_even`, and is carried from there
through `stage_finite_drift`, `stage_exp_gain`, `point_exp_loss`, `loss_tail`,
`good_fixed_bad_bound` and `union_simultaneous_bound` to Proposition 2.7.

`GridDrift.lean` proves the conditional gain for every base from Lemma 2.3 of the manuscript.
This file repeats the six steps above with that lemma in place of the even-base one. The
proofs are the archive's, with `Even b` replaced by `2 ≤ b` and the hypothesis `0 < h`, which
they do not need, dropped. All other ingredients of the archive (good transitions, bounded
differences, the union over colorings) are used unchanged.

* `union_simultaneous_bound_all`: the archive's `Direct.union_simultaneous_bound` for every
  integer `b ≥ 4` (the hypothesis `0 < h` of the archive's version is not needed either);
* `proposition_2_7_probe`: **Proposition 2.7, display (14), for every integer `b ≥ 3`**, by
  the finite-probe route, with `‖F_χ‖∞` of `Notation.lean`. No parity hypothesis. (The
  archive's own statement, for even `b` or `b ≤ 48`, is `proposition_2_7_archive` in
  `ArchiveRoute.lean`.)
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory Finset Riesz Riesz.PointSets Oscillation Oscillation.Direct

open scoped ENNReal Classical

noncomputable section

/-- The conditional gain (11) of the archive's stage process, for every base `b ≥ 2`.
(`Oscillation.stage_finite_drift` without `Even b`.) -/
lemma stage_finite_drift_all {n b h j : ℕ} (hb0 : 0 < b) (hb : 2 ≤ b) (hj : j < h)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (Y : Fin n → ℕ) (U : Fin n → ℝ) :
    stageMass b h hb0 Y j U / (4 * (b : ℝ) * (b ^ (h-1) : ℕ)) ≤
      finAvg (stageContinuation b h hb0 χ Y j U) - stagePotential b h hb0 χ Y j U := by
  have hg := gridPotential_drift_all (K := b^j) (V := b^(h-j-1))
    (pow_pos hb0 _) (pow_pos hb0 _) hb (pow_pos hb0 j) χ hχ
    (sampleCells n (b^j) (pow_pos hb0 _) U) Y
  rw [stage_rectangles b h j hj] at hg
  rw [stageMass, ite_eq_left hj, stagePotential_before hb0 hj]
  change _ ≤ finAvg (fun r : Fin n → Fin b ↦
    gridPotential (b*b^j) (b^(h-j-1)) (b*b^j) (Nat.mul_pos hb0 (pow_pos hb0 j)) χ
      (refinedPositions (sampleCells n (b^j) (pow_pos hb0 j) U) r) Y) - _
  simpa only [Nat.mul_comm (b^j) b] using hg

/-- `Oscillation.Direct.stage_exp_gain` without `Even b`. -/
theorem stage_exp_gain_all (n b h : ℕ) (hb0 : 0 < b) (hb : 2 ≤ b)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (Y : Fin n → ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (∫ U, Real.exp (-u * stagePotential b h hb0 χ Y h U +
      u * (∑ j ∈ range h, stageMass b h hb0 Y j U) / (4 * b * (b^(h-1):ℕ)))
      ∂Measure.pi (fun _ : Fin n => μI)) ≤
      Real.exp ((h:ℝ)*n*u^2/(2*(b^(h-1):ℕ)^2)) := by
  let : Nonempty (Fin b) := ⟨⟨0, hb0⟩⟩
  let M : ℝ := (b ^ (h-1) : ℕ)
  let D : ℝ := 4 * b * M
  let Z := stagePotential b h hb0 χ Y
  let S : ℕ → (Fin n → ℝ) → ℝ := fun j U ↦ stageMass b h hb0 Y j U / D
  let F := stageFiltration n b h hb0
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hχle : ∀ i, |χ i| ≤ 1 := fun i ↦ (hχ i).le
  have hZ : StronglyAdapted F Z := stagePotential_adapted b h hb0 χ Y
  have hS : StronglyAdapted F S :=
    fun j ↦ ((stageMass_adapted b h hb0 Y j).measurable.div_const D).stronglyMeasurable
  have hbound : ∀ j U, |Z j U| ≤ max (2 * (n : ℝ)) (M * Real.sqrt n / D) ∧
      |S j U| ≤ max (2 * (n : ℝ)) (M * Real.sqrt n / D) := by
    intro j U
    constructor
    · exact (stagePotential_abs_le b h hb0 χ hχle Y j U).trans (le_max_left _ _)
    · calc
        |S j U| = |stageMass b h hb0 Y j U| / D := by dsimp [S]; rw [abs_div, abs_of_pos hD]
        _ ≤ M * Real.sqrt n / D := div_le_div_of_nonneg_right
          (stageMass_abs_le b h hb0 Y j U) hD.le
        _ ≤ _ := le_max_right _ _
  have hc := integral_exp_accumulated_le (μ := Measure.pi (fun _ : Fin n ↦ μI))
    F n h Z S (stageContinuation b h hb0 χ Y) hZ hS
    (max (2 * (n : ℝ)) (M * Real.sqrt n / D)) hbound
    (stagePotential_zero b h hb0 χ Y) (by positivity : 0 ≤ 1 / M) u hu
    (fun j hj ↦ stage_finiteConditionalLaw hb0 hj χ hχle Y)
    (fun j hj ↦ Filter.Eventually.of_forall (stage_coordinateOscillation hb0 hj χ hχle Y))
    (fun j hj ↦ Filter.Eventually.of_forall (stage_finite_drift_all hb0 hb hj χ hχ Y))
  have he (U : Fin n → ℝ) : u * (∑ j ∈ range h, S j U) =
      u * (∑ j ∈ range h, stageMass b h hb0 Y j U) / D := by
    simp only [S, ← sum_div]; ring
  simp_rw [he] at hc
  convert hc using 1
  dsimp [Z, D, M]
  congr 1
  ring

/-- `Oscillation.Direct.point_exp_loss` without `Even b`. -/
theorem point_exp_loss_all {n : ℕ} (b h : ℕ) (hb0 : 0 < b) (hb : 2 ≤ b)
    (χ : Fin n → Bool) (u : ℝ) (hu : 0 ≤ u) :
    (∫ P, Real.exp (-u * loss b h hb0 χ P) ∂pointSampleLaw n) ≤
      Real.exp ((h:ℝ)*n*u^2/(2*(b^(h-1):ℕ)^2)) := by
  have hi := integrable_exp_loss b h hb0 χ u hu
  rw [integral_point_eq_vertical_horizontal _ hi]
  have ho := ((integrable_pairCoordinates_iff _).mpr hi).integral_prod_right
  calc
    _ ≤ ∫ _W : Fin n → ℝ, Real.exp ((h:ℝ)*n*u^2/(2*(b^(h-1):ℕ)^2))
        ∂coordinateSampleLaw n := by
      apply integral_mono ho (integrable_const _)
      intro W
      let Y := sampleCells n (b^h) (pow_pos hb0 h) W
      have hχ : ∀ i, |(PointSets.boolSign (χ i):ℝ)| = 1 := by
        intro i; cases χ i <;> simp [PointSets.boolSign]
      have H := stage_exp_gain_all n b h hb0 hb _ hχ Y u hu
      have hsum (U : Fin n → ℝ) : (∑ j ∈ range h, stageMass b h hb0 Y j U) =
          ∑ j ∈ range h, pointLayerMass b h hb0 j (fun i => (U i,W i)) := by
        apply sum_congr rfl
        intro j hj
        simp only [stageMass, ite_eq_left (mem_range.mp hj)]
        rfl
      simp_rw [stagePotential_terminal] at H
      simp_rw [hsum] at H
      convert H using 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun U => by dsimp [loss,pointTerminalPotential]; congr 1; ring)
    _ = _ := by simp

/-- `Oscillation.Direct.loss_tail` without `Even b`. -/
lemma loss_tail_all {n b h : ℕ} (hn : 0 < n) (hb0 : 0 < b) (hb : 2 ≤ b)
    (χ : Fin n → Bool) :
    (pointSampleLaw n).real {P | loss b h hb0 χ P ≤ -(h:ℝ)*drift n b (b^(h-1):ℕ)/4} ≤
      Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  let M : ℝ := (b^(h-1):ℕ)
  let d := drift n b M
  let u := d*M^2/(4*n)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hbR : (0:ℝ) < b := by exact_mod_cast hb0
  have hM : 0 < M := by dsimp [M]; positivity
  have hd : 0 < d := drift_pos hn hbR hM
  have hu : 0 < u := by dsimp [u]; positivity
  have H := small_event_of_laplace (pointSampleLaw n) (loss b h hb0 χ) u (-(h:ℝ)*d/4)
    (Real.exp ((h:ℝ)*n*u^2/(2*M^2))) hu
    (integrable_exp_loss b h hb0 χ u hu.le) (point_exp_loss_all b h hb0 hb χ u hu.le)
  have he : Real.exp (u*(-(h:ℝ)*d/4))*Real.exp ((h:ℝ)*n*u^2/(2*M^2)) =
      Real.exp (-(h:ℝ)*M/(2048*(b:ℝ)^3)) := by
    rw [← Real.exp_add]
    congr 1
    have halg : u*(-(h:ℝ)*d/4)+(h:ℝ)*n*u^2/(2*M^2) = -(h:ℝ)*(d^2*M^2/(32*n)) := by
      dsimp [u]; field_simp; ring
    rw [halg, drift_exponent hn hbR hM]
    ring
  rw [he] at H
  simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top H

/-- `Oscillation.Direct.good_fixed_bad_bound` without `Even b`. -/
lemma good_fixed_bad_bound_all {n b h : ℕ} (hn : 0 < n) (hb0 : 0 < b) (hb : 2 ≤ b)
    (χ : Fin n → Bool) :
    (pointSampleLaw n).real
        (good (n := n) b h hb0 ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) ≤
      Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  apply le_trans _ (loss_tail_all hn hb0 hb χ)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_pointSampleLaw_mem_Ioc n] with P hP
  rintro ⟨hg,hbad⟩
  have hx := actualPotential_le_of_fixedColorBad (pow_pos hb0 h) (by omega : 0 < 1)
    (pow_pos hb0 h) χ (fun i => (P i).1) (fun i => (P i).2)
    (fun i => (hP i).1) (fun i => (hP i).2) hbad
  rw [sampleCells_eq_of_grid_eq (Nat.one_mul (b^h)) _ (pow_pos hb0 h)] at hx
  change pointTerminalPotential b h hb0 χ P ≤ 2*threshold n h b (b^(h-1):ℕ) at hx
  have hs : (h:ℝ)*massFloor n b (b^(h-1):ℕ)/2 ≤ ∑ j ∈ range h, pointLayerMass b h hb0 j P := hg
  have hdiv := div_le_div_of_nonneg_right hs (show (0:ℝ) ≤ 4*b*(b^(h-1):ℕ) by positivity)
  change loss b h hb0 χ P ≤ _
  dsimp only [loss,threshold,drift] at *
  have hneg := neg_le_neg hdiv
  linear_combination hx + hneg

/-- `Oscillation.Direct.union_simultaneous_bound` without `Even b`: for every integer base
`b ≥ 4`, with all `h` transitions required to be good and the union bound over the colorings
taken only for the fluctuation event. -/
theorem union_simultaneous_bound_all {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n (threshold n h b (b^(h-1):ℕ))) ≤
      h*(4*Real.sqrt (3/b))^n + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  rw [← pointSampleLaw_eq_unifPts]
  have hs : badSet n (threshold n h b (b^(h-1):ℕ)) ⊆
      (allGood (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ := by
    intro P hP
    by_cases hg : P ∈ allGood b h (by omega)
    · right
      rw [badSet_eq_iUnion_fixedColorBad] at hP
      obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp hP
      exact Set.mem_iUnion.mpr ⟨χ,hg,hχ⟩
    · exact Or.inl hg
  have hf (χ : Fin n → Bool) :
      (pointSampleLaw n).real
          (allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) ≤
        Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
    apply le_trans _ (good_fixed_bad_bound_all hn (by omega) (by omega) χ)
    exact measureReal_mono (Set.inter_subset_inter_left _ (allGood_subset_good hn (by omega)))
  calc
    _ ≤ (pointSampleLaw n).real ((allGood (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) :=
      measureReal_mono hs
    _ ≤ (pointSampleLaw n).real (allGood (n := n) b h (by omega))ᶜ +
        (pointSampleLaw n).real (⋃ χ : Fin n → Bool,
          allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) :=
      measureReal_union_le _ _
    _ ≤ h*(4*Real.sqrt (3/b))^n +
        ∑ χ : Fin n → Bool, (pointSampleLaw n).real
          (allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) :=
      add_le_add (allGood_compl_bound hn hb hMn) (measureReal_iUnion_fintype_le _)
    _ ≤ h*(4*Real.sqrt (3/b))^n +
        ∑ _χ : Fin n → Bool, Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) :=
      add_le_add_right (sum_le_sum (fun χ _ => hf χ)) _
    _ = _ := by simp

/-- The archive's form of Proposition 2.7 (with `badSet`), for every integer `b ≥ 4`. -/
theorem simultaneous_bound_all {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (hMn : b^(h-1) ≤ n) :
    (unifPts n).real
        (badSet n ((h:ℝ)*Real.sqrt ((n:ℝ)/(b^(h-1):ℕ))/(64*(b:ℝ)^(3/2:ℝ)))) ≤
      h*(48/(b:ℝ))^((n:ℝ)/2) + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  have hbR : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have H := union_simultaneous_bound_all hn hb hMn
  rw [threshold_eq hn h hbR (by positivity), geometry_factor_eq hbR] at H
  exact H

/-- **Proposition 2.7, display (14), for every integer base `b ≥ 3`, by the archive's
finite-probe route**, with `M = b^{h-1}`: if `M ≤ n`, then

`Pr[∃ χ ∈ {±1}ⁿ : ‖F_χ‖∞ ≤ (h / (64 b^{3/2})) √(n/M)] ≤ h (48/b)^{n/2} + 2ⁿ e^{-hM/(2048 b³)}`.

For `b = 3` the right-hand side is at least `1`. For `b ≥ 4` the local gain comes from
Lemma 2.3 of the manuscript (`gridPotential_drift_all`); the potential is the archive's
finite-probe potential. This is a second proof of the statement of `proposition_2_7` in
`Simultaneous.lean`, which is proved there as in the manuscript. -/
theorem proposition_2_7_probe {n b h : ℕ} (hb : 3 ≤ b) (hh : 1 ≤ h) (hMn : b ^ (h - 1) ≤ n) :
    (unifPts n).real {P | ∃ χ : Fin n → ℤˣ,
        supNorm χ P ≤ (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))} ≤
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
        2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) := by
  by_cases hb4 : 4 ≤ b
  · have hn : 0 < n := lt_of_lt_of_le (pow_pos (by omega) _) hMn
    have H := simultaneous_bound_all hn hb4 hMn
    rw [exists_supNorm_le_eq_badSet]
    have e1 : (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1)) =
        (h : ℝ) * Real.sqrt ((n : ℝ) / (b ^ (h - 1) : ℕ)) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) := by
      push_cast
      ring
    have e2 : -((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3)) =
        -(h : ℝ) * (b ^ (h - 1) : ℕ) / (2048 * (b : ℝ) ^ 3) := by
      push_cast
      ring
    rw [e1, e2]
    exact H
  · exact proposition_2_7_of_le_48 hb (by omega) hh

end

end R56Audit
