import R56Audit.Notation

/-!
# `‖F_χ‖∞` is a maximum over finitely many rectangles

An anchored rectangle `[0,x] × [0,y]` with `x, y ∈ [0,1]` contains the same sample points as
one whose sides are `0` or coordinates of sample points. Hence the supremum defining
`‖F_χ‖∞` is attained (`exists_eq_supNorm`): it is the largest imbalance of an anchored
rectangle `[0,x] × [0,y]` with `x, y ∈ [0,1]`. It is also a measurable function of the sample
(`measurable_supNorm`), so the events of Theorem 1.1 and of Proposition 2.7 are measurable
(`measurableSet_forall_le_supNorm`, `measurableSet_supNorm_le`, `measurableSet_exists_supNorm_le`)
and their probabilities are not merely outer measures.

`one_le_supNorm` is the lowest-point argument of the proof of Theorem 1.1: "The rectangle
`[0,1] × [0, min_i V_i]` \[…\] contains just the lowest point, which is unique since all
heights are distinct."

Auditor's supplement (not part of the audited archive).
-/

namespace R56Audit

open MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The nearest point of `[0,1]`. -/
def clampUnit (u : ℝ) : ℝ := min (max u 0) 1

lemma clampUnit_mem (u : ℝ) : clampUnit u ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

lemma clampUnit_of_mem {u : ℝ} (h : u ∈ Set.Icc (0 : ℝ) 1) : clampUnit u = u := by
  unfold clampUnit
  rw [max_eq_left h.1, min_eq_left h.2]

lemma measurable_clampUnit : Measurable clampUnit :=
  (measurable_id.max measurable_const).min measurable_const

/-- The candidate right sides: `0` and the horizontal coordinates of the sample, clamped. -/
def candidateX (o : Option (Fin n)) (P : Fin n → ℝ × ℝ) : ℝ :=
  o.elim 0 (fun k => clampUnit (P k).1)

/-- The candidate upper sides: `0` and the vertical coordinates of the sample, clamped. -/
def candidateY (o : Option (Fin n)) (P : Fin n → ℝ × ℝ) : ℝ :=
  o.elim 0 (fun k => clampUnit (P k).2)

lemma candidateX_mem (o : Option (Fin n)) (P : Fin n → ℝ × ℝ) :
    candidateX o P ∈ Set.Icc (0 : ℝ) 1 := by
  cases o with
  | none => simp [candidateX]
  | some k => exact clampUnit_mem _

lemma candidateY_mem (o : Option (Fin n)) (P : Fin n → ℝ × ℝ) :
    candidateY o P ∈ Set.Icc (0 : ℝ) 1 := by
  cases o with
  | none => simp [candidateY]
  | some k => exact clampUnit_mem _

lemma measurable_candidateX (o : Option (Fin n)) : Measurable (candidateX (n := n) o) := by
  cases o with
  | none => exact measurable_const
  | some k => exact measurable_clampUnit.comp (measurable_pi_apply k).fst

lemma measurable_candidateY (o : Option (Fin n)) : Measurable (candidateY (n := n) o) := by
  cases o with
  | none => exact measurable_const
  | some k => exact measurable_clampUnit.comp (measurable_pi_apply k).snd

/-- For `x ∈ [0,1]` there is a candidate `x'`, either `0` or a clamped coordinate, such that
`[0,x']` and `[0,x]` contain the same coordinates. -/
lemma exists_candidate (w : Fin n → ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ o : Option (Fin n), ∀ i,
      (0 ≤ w i ∧ w i ≤ o.elim 0 (fun k => clampUnit (w k))) ↔ (0 ≤ w i ∧ w i ≤ x) := by
  classical
  by_cases hA : ∃ i, 0 ≤ w i ∧ w i ≤ x
  · have hne : (Finset.univ.filter (fun i => 0 ≤ w i ∧ w i ≤ x)).Nonempty := by
      obtain ⟨i, hi⟩ := hA
      exact ⟨i, by simp [hi]⟩
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image _ w hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hmax
    refine ⟨some k, fun i => ?_⟩
    have hck : clampUnit (w k) = w k := clampUnit_of_mem ⟨hk.1, hk.2.trans hx.2⟩
    simp only [Option.elim_some, hck]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0, h1.trans hk.2⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0, hmax i ⟨h0, h1⟩⟩
  · refine ⟨none, fun i => ?_⟩
    simp only [Option.elim_none]
    constructor
    · rintro ⟨h0, h1⟩
      exact absurd ⟨i, h0, h1.trans hx.1⟩ hA
    · intro h
      exact absurd ⟨i, h⟩ hA

/-- `F_χ` depends on `(x, y)` only through the set of sample points in `[0,x] × [0,y]`. -/
lemma F_congr (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) {x x' y y' : ℝ}
    (hx : ∀ i, (0 ≤ (P i).1 ∧ (P i).1 ≤ x') ↔ (0 ≤ (P i).1 ∧ (P i).1 ≤ x))
    (hy : ∀ i, (0 ≤ (P i).2 ∧ (P i).2 ≤ y') ↔ (0 ≤ (P i).2 ∧ (P i).2 ≤ y)) :
    F χ P x' y' = F χ P x y := by
  classical
  rw [F_eq_filter, F_eq_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a1, a2, a3, a4⟩
    exact ⟨((hx i).mp ⟨a1, a2⟩).1, ((hx i).mp ⟨a1, a2⟩).2,
      ((hy i).mp ⟨a3, a4⟩).1, ((hy i).mp ⟨a3, a4⟩).2⟩
  · rintro ⟨a1, a2, a3, a4⟩
    exact ⟨((hx i).mpr ⟨a1, a2⟩).1, ((hx i).mpr ⟨a1, a2⟩).2,
      ((hy i).mpr ⟨a3, a4⟩).1, ((hy i).mpr ⟨a3, a4⟩).2⟩

/-- `‖F_χ‖∞` is the maximum of `|F_χ|` over the `(n+1)²` candidate rectangles. -/
theorem supNorm_eq_max (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) :
    supNorm χ P = ⨆ o : Option (Fin n) × Option (Fin n),
      |F χ P (candidateX o.1 P) (candidateY o.2 P)| := by
  apply le_antisymm
  · rw [supNorm_le_iff]
    intro x hx y hy
    obtain ⟨o1, h1⟩ := exists_candidate (fun i => (P i).1) hx
    obtain ⟨o2, h2⟩ := exists_candidate (fun i => (P i).2) hy
    have h := F_congr χ P (x' := candidateX o1 P) (y' := candidateY o2 P) (x := x) (y := y)
      h1 h2
    rw [← h]
    exact le_ciSup (f := fun o : Option (Fin n) × Option (Fin n) =>
      |F χ P (candidateX o.1 P) (candidateY o.2 P)|) (Set.finite_range _).bddAbove (o1, o2)
  · exact ciSup_le fun o => le_supNorm χ P (candidateX_mem _ _) (candidateY_mem _ _)

/-- **`‖F_χ‖∞` is the largest imbalance of an anchored rectangle**: the supremum over `[0,1]²`
is attained. -/
theorem exists_eq_supNorm (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, |F χ P x y| = supNorm χ P := by
  obtain ⟨o, ho⟩ := exists_eq_ciSup_of_finite
    (f := fun o : Option (Fin n) × Option (Fin n) =>
      |F χ P (candidateX o.1 P) (candidateY o.2 P)|)
  exact ⟨_, candidateX_mem o.1 P, _, candidateY_mem o.2 P, by rw [supNorm_eq_max]; exact ho⟩

lemma measurable_F_candidate (χ : Fin n → ℤˣ) (o1 o2 : Option (Fin n)) :
    Measurable (fun P : Fin n → ℝ × ℝ => F χ P (candidateX o1 P) (candidateY o2 P)) := by
  classical
  simp_rw [F_eq_filter, Finset.sum_filter]
  refine Finset.measurable_sum _ fun i _ => ?_
  have hU : Measurable (fun P : Fin n → ℝ × ℝ => (P i).1) := (measurable_pi_apply i).fst
  have hV : Measurable (fun P : Fin n → ℝ × ℝ => (P i).2) := (measurable_pi_apply i).snd
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_le measurable_const hU).inter
    ((measurableSet_le hU (measurable_candidateX o1)).inter
      ((measurableSet_le measurable_const hV).inter
        (measurableSet_le hV (measurable_candidateY o2))))

/-- `‖F_χ‖∞` is a measurable function of the sample. -/
theorem measurable_supNorm (χ : Fin n → ℤˣ) : Measurable (supNorm χ) := by
  have h : supNorm χ = fun P => ⨆ o : Option (Fin n) × Option (Fin n),
      |F χ P (candidateX o.1 P) (candidateY o.2 P)| :=
    funext (supNorm_eq_max χ)
  rw [h]
  exact Measurable.iSup fun o =>
    continuous_abs.measurable.comp (measurable_F_candidate χ o.1 o.2)

/-- The event of Theorem 1.1, that every coloring `χ` has `‖F_χ‖∞ ≥ t`, is measurable. -/
theorem measurableSet_forall_le_supNorm (t : ℝ) :
    MeasurableSet {P : Fin n → ℝ × ℝ | ∀ χ : Fin n → ℤˣ, t ≤ supNorm χ P} := by
  have h : {P : Fin n → ℝ × ℝ | ∀ χ : Fin n → ℤˣ, t ≤ supNorm χ P} =
      ⋂ χ : Fin n → ℤˣ, {P | t ≤ supNorm χ P} := by
    ext P
    simp
  rw [h]
  exact MeasurableSet.iInter fun χ => measurableSet_le measurable_const (measurable_supNorm χ)

/-- The event `‖F_χ‖∞ ≤ B` of a fixed coloring is measurable. -/
theorem measurableSet_supNorm_le (χ : Fin n → ℤˣ) (B : ℝ) :
    MeasurableSet {P : Fin n → ℝ × ℝ | supNorm χ P ≤ B} :=
  measurableSet_le (measurable_supNorm χ) measurable_const

/-- The event of Proposition 2.7, that some coloring `χ` has `‖F_χ‖∞ ≤ B`, is measurable. -/
theorem measurableSet_exists_supNorm_le (B : ℝ) :
    MeasurableSet {P : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ B} := by
  have h : {P : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ B} =
      ⋃ χ : Fin n → ℤˣ, {P | supNorm χ P ≤ B} := by
    ext P
    simp
  rw [h]
  exact MeasurableSet.iUnion fun χ => measurableSet_supNorm_le χ B

/-- **The lowest point.** If `n ≥ 1`, the points lie in the unit square and all heights are
distinct, then the anchored rectangle `[0,1] × [0, min_i V_i]` contains just the lowest
point, so it has imbalance `1` under every coloring: `‖F_χ‖∞ ≥ 1`. -/
theorem one_le_supNorm (hn : 1 ≤ n) (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ)
    (hP : ∀ i, (P i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Icc (0 : ℝ) 1)
    (hinj : Function.Injective fun i => (P i).2) : 1 ≤ supNorm χ P := by
  classical
  -- the lowest point `t₀`
  obtain ⟨t₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun i => (P i).2) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  -- it is the only point of `[0,1] × [0, V_{t₀}]`
  have hfilter : Finset.univ.filter (fun t => 0 ≤ (P t).1 ∧ (P t).1 ≤ 1 ∧
      0 ≤ (P t).2 ∧ (P t).2 ≤ (P t₀).2) = {t₀} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, -, -, h4⟩
      exact hinj (le_antisymm h4 (hmin t (Finset.mem_univ t)))
    · rintro rfl
      exact ⟨(hP t).1.1, (hP t).1.2, (hP t).2.1, le_rfl⟩
  have h := le_supNorm χ P (x := 1) (y := (P t₀).2) (by simp) (hP t₀).2
  rw [F_eq_filter, hfilter, Finset.sum_singleton] at h
  have h1 : |(((χ t₀ : ℤˣ) : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (χ t₀) with h' | h' <;> simp [h']
  rw [h1] at h
  exact h

end

end R56Audit
