import R56Audit.ArchiveInterface

/-!
# The archive's theorems, restated with `F_χ` and `‖F_χ‖∞`

Auditor's supplement (not part of the audited archive).

Every theorem of this file is one of the ARCHIVE's theorems, proved by the archive's own route
(base `b = 2^L`, the even-base local gain, the finite-probe potential) and restated here with
the manuscript's objects `F_χ` and `‖F_χ‖∞` of `R56Audit.Notation`, through the bridges of
`ArchiveInterface.lean`. Nothing is proved here about the lower bound itself.

The theorems proved along the manuscript's own route carry the plain names and are elsewhere:
`proposition_2_7` in `Simultaneous.lean`; `theorem_1_1`, `theorem_1_1_constant`,
`theorem_1_1_constant_event`, `exists_points` and `corollary_1_2_lower` in `Parameters.lean`.

* `theorem_1_1_archive`: Theorem 1.1 exactly as displayed, from `Oscillation.paper_lower_bound`.
* `theorem_1_1_event_archive`: the same on a measurable event on which the points are distinct
  and the inequality is strict.
* `corollary_1_2_lower_archive`, `exists_points_anchored_archive`: the lower-bound half of
  Corollary 1.2.
* `proposition_2_7_archive`: the display (14) of Proposition 2.7, for every integer base
  `b ≥ 3` that is even or at most `48`, from `Oscillation.R65.simultaneous_bound`. For `b ≤ 48`
  the right-hand side is at least `1` and the statement is empty
  (`proposition_2_7_of_le_48`); the archive has no proof for odd `b ≥ 49`.
-/

namespace R56Audit

open MeasureTheory Riesz.PointSets

noncomputable section

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1 on a measurable event, from the archive.** For every `A > 0` there is `c > 0`
such that for every `n ≥ 1` there is a measurable event of probability at least `1 - e^{-An}`,
for `n` independent uniform points of `[0,1]²`, on which the points are distinct and every
coloring `χ ∈ {±1}ⁿ` has `‖F_χ‖∞ > c (log₂ n)^{3/2}`. -/
theorem theorem_1_1_event_archive :
    ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ G : Set (Fin n → ℝ × ℝ), MeasurableSet G ∧
        ENNReal.ofReal (1 - Real.exp (-A * n)) ≤ unifPts n G ∧
        ∀ P ∈ G, Function.Injective P ∧
          ∀ χ : Fin n → ℤˣ, c * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P := by
  intro A hA
  obtain ⟨c, hc, h⟩ := Oscillation.paper_lower_bound A hA
  exact ⟨c, hc, fun n hn => goodEvent_supNorm (h n hn)⟩

/-- **Theorem 1.1, from the archive**, as displayed in the manuscript: for every `A > 0` there
is a constant `c_A > 0` such that for every integer `n ≥ 1`, if `P_1, …, P_n` are independent
uniform points in `[0,1]²`, then
`Pr[for every χ ∈ {±1}ⁿ, ‖F_χ‖∞ ≥ c_A (log₂ n)^{3/2}] ≥ 1 - e^{-An}`.
The event is measurable: `measurableSet_forall_le_supNorm`. -/
theorem theorem_1_1_archive :
    ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (1 - Real.exp (-A * n)) ≤
        unifPts n {P | ∀ χ : Fin n → ℤˣ, c * Real.logb 2 n ^ (3 / 2 : ℝ) ≤ supNorm χ P} := by
  intro A hA
  obtain ⟨c, hc, h⟩ := theorem_1_1_event_archive A hA
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨G, -, hmeas, hgood⟩ := h n hn
  exact hmeas.trans (measure_mono fun P hP χ => ((hgood P hP).2 χ).le)

/-! ### Corollary 1.2, lower bound -/

/-- **The lower bound for anchored rectangles, from the archive**: there is `c > 0` such that
for every `n ≥ 1` some `n` distinct points of the plane have, for every coloring
`χ ∈ {±1}ⁿ`, an anchored rectangle `[0,x] × [0,y]` with `x, y ∈ [0,1]` and imbalance greater
than `c (log₂ n)^{3/2}`. -/
theorem exists_points_anchored_archive :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Fin n → ℝ × ℝ, Function.Injective P ∧
        ∀ χ : Fin n → ℤˣ, c * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P := by
  obtain ⟨c, hc, h⟩ := theorem_1_1_event_archive 1 one_pos
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨G, -, hmeas, hgood⟩ := h n hn
  have hpos : 0 < unifPts n G := by
    refine lt_of_lt_of_le ?_ hmeas
    rw [ENNReal.ofReal_pos, sub_pos, Real.exp_lt_one_iff]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨P, hP⟩ := nonempty_of_measure_ne_zero hpos.ne'
  exact ⟨P, hgood P hP⟩

/-- **Corollary 1.2, lower bound, from the archive**: `Δ₂(n) = Ω(log^{3/2} n)` for the
worst-case discrepancy of `n` points with respect to axis-parallel rectangles. (The upper
bound is Nikolov's theorem, which the manuscript cites and neither the archive nor the
supplement formalizes.) -/
theorem corollary_1_2_lower_archive :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * Real.logb 2 n ^ (3 / 2 : ℝ) < Δ₂ n := by
  obtain ⟨c, hc, h⟩ := exists_points_anchored_archive
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨P, hinj, hP⟩ := h n hn
  exact lt_Δ₂_of_supNorm P hinj hP

/-! ### Proposition 2.7 -/

/-- For `b ≤ 48` the right-hand side of (14) is at least `1`, so Proposition 2.7 has no
content there. -/
theorem proposition_2_7_of_le_48 {n b h : ℕ} (hb : 3 ≤ b) (h48 : b ≤ 48) (hh : 1 ≤ h) :
    (unifPts n).real {P | ∃ χ : Fin n → ℤˣ,
        supNorm χ P ≤ (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))} ≤
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
        2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb48 : (b : ℝ) ≤ 48 := by exact_mod_cast h48
  have hbase : (1 : ℝ) ≤ 48 / b := (le_div_iff₀ hbR).mpr (by simpa using hb48)
  have hr := Real.one_le_rpow hbase (show (0 : ℝ) ≤ n / 2 by positivity)
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hexp : 0 ≤ (2 : ℝ) ^ n *
      Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) := by positivity
  calc (unifPts n).real _ ≤ 1 := measureReal_le_one
    _ ≤ h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) := by nlinarith
    _ ≤ _ := le_add_of_nonneg_right hexp

/-- **Proposition 2.7, display (14), from the archive**, with `M = b^{h-1}`: if `M ≤ n`, then
`Pr[∃ χ ∈ {±1}ⁿ : ‖F_χ‖∞ ≤ (h / (64 b^{3/2})) √(n/M)] ≤ h (48/b)^{n/2} + 2ⁿ e^{-hM/(2048 b³)}`.

The manuscript states this for every integer `b ≥ 3`. The archive proves it for even
`b ≥ 4` (`Oscillation.R65.simultaneous_bound`); for `b ≤ 48` the right-hand side is at least
`1`, so nothing has to be proved. **Odd `b ≥ 49` is not covered by the archive.** The
statement without the parity hypothesis is `proposition_2_7` in `Simultaneous.lean` (the
manuscript's proof) and `proposition_2_7_probe` in `AllBases.lean` (the archive's finite-probe
route with the parity restriction removed). -/
theorem proposition_2_7_archive {n b h : ℕ} (hb : 3 ≤ b) (hpar : Even b ∨ b ≤ 48) (hh : 1 ≤ h)
    (hMn : b ^ (h - 1) ≤ n) :
    (unifPts n).real {P | ∃ χ : Fin n → ℤˣ,
        supNorm χ P ≤ (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))} ≤
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
        2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) := by
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by omega) _) hMn
  by_cases h48 : b ≤ 48
  · exact proposition_2_7_of_le_48 hb h48 hh
  · have heven : Even b := hpar.resolve_right h48
    have H := Oscillation.R65.simultaneous_bound hn (by omega : 4 ≤ b) heven hh hMn
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

end

end R56Audit
