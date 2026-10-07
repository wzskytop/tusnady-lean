import R56Audit.LocalGain

/-!
# Oscillations of step functions on vertical intervals

Auditor's supplement (not part of the audited archive).

Section 2.1 of the manuscript: "All functions of the height that we consider are finite linear
combinations of the functions `y ↦ 1{V_i ≤ y}`, up to an additive constant. They take finitely
many values, so these extrema exist". This file collects what the later sections use about
such functions (`stepFn V c`) on a vertical interval `B = [s, t)`:

* `osc_le_osc_add_add`: "Applying it to `f = (f+g) + (-g)` and using `osc_B (-g) = osc_B g`
  gives `osc_B f ≤ osc_B (f+g) + osc_B g`", where "it" is the triangle inequality
  (`osc_add_le` and `osc_neg` in `Osc.lean`);
* `abs_osc_add_sub_le`: "Together with the triangle inequality itself, this is the reverse
  triangle inequality `|osc_B (f+g) - osc_B f| ≤ osc_B g`";
* `osc_stepFn_le`: `osc_B (Σ_i c_i 1{V_i ≤ ·}) ≤ Σ_i |c_i|`;
* `stepFn_single_eq_of_notMem`, `osc_stepFn_single_le`: a single jump at a height outside `B`
  is constant on `B`, and a single jump at a height in `B` has oscillation at most its size
  (Step 1 of the proof of Lemma 2.6);
* `maxOn_Ico_stepFn`, `minOn_Ico_stepFn`: the extrema over `B` are the extrema over the
  `n + 1` heights `s` and `V_i ∈ B`;
* `measurable_osc_Ico_stepFn`: `osc_B (stepFn V c)` is a measurable function of the heights.
-/

namespace R56Audit

open Finset

noncomputable section

variable {n : ℕ}

/-! ### The oscillation -/

lemma image_add_finite {α : Type*} {B : Set α} {f g : α → ℝ} (hf : (f '' B).Finite)
    (hg : (g '' B).Finite) : ((fun y => f y + g y) '' B).Finite := by
  refine (hf.image2 (fun a b => a + b) hg).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  exact Set.mem_image2.mpr ⟨f y, ⟨y, hy, rfl⟩, g y, ⟨y, hy, rfl⟩, rfl⟩

/-- If `g` takes finitely many values on `B`, then so does `-g`. -/
lemma image_neg_finite {α : Type*} {B : Set α} {g : α → ℝ} (hg : (g '' B).Finite) :
    ((fun y => -g y) '' B).Finite := by
  have h : (fun y => -g y) '' B = (fun t => -t) '' (g '' B) := by
    rw [Set.image_image]
  rw [h]
  exact hg.image _

/-- "Applying it to `f = (f+g) + (-g)` and using `osc_B (-g) = osc_B g` gives
`osc_B f ≤ osc_B (f+g) + osc_B g`." Here "it" is the triangle inequality `osc_add_le`. -/
lemma osc_le_osc_add_add {α : Type*} {B : Set α} {f g : α → ℝ} (hB : B.Nonempty)
    (hf : (f '' B).Finite) (hg : (g '' B).Finite) :
    osc B f ≤ osc B (fun y => f y + g y) + osc B g :=
  -- write `f = (f + g) + (-g)`, apply the triangle inequality to `f + g` and `-g`, and use
  -- `osc_B (-g) = osc_B g`
  calc osc B f = osc B (fun y => (f y + g y) + -g y) := osc_congr fun y _ => by ring
    _ ≤ osc B (fun y => f y + g y) + osc B (fun y => -g y) :=
        osc_add_le hB (image_add_finite hf hg) (image_neg_finite hg)
    _ = osc B (fun y => f y + g y) + osc B g := by rw [osc_neg]

/-- "Together with the triangle inequality itself, this is the reverse triangle inequality
`|osc_B (f+g) - osc_B f| ≤ osc_B g`", where "this" is `osc_B f ≤ osc_B (f+g) + osc_B g`
(`osc_le_osc_add_add`). -/
lemma abs_osc_add_sub_le {α : Type*} {B : Set α} {f g : α → ℝ} (hB : B.Nonempty)
    (hf : (f '' B).Finite) (hg : (g '' B).Finite) :
    |osc B (fun y => f y + g y) - osc B f| ≤ osc B g := by
  -- the triangle inequality itself
  have h1 : osc B (fun y => f y + g y) ≤ osc B f + osc B g := osc_add_le hB hf hg
  -- the triangle inequality applied to `f = (f + g) + (-g)`
  have h2 : osc B f ≤ osc B (fun y => f y + g y) + osc B g := osc_le_osc_add_add hB hf hg
  rw [abs_le]
  constructor <;> linarith

/-- A step function with coefficients `c` has oscillation at most `Σ_i |c_i|` on every
nonempty set of heights. -/
lemma osc_stepFn_le (V c : Fin n → ℝ) {B : Set ℝ} (hB : B.Nonempty) :
    osc B (stepFn V c) ≤ ∑ i, |c i| := by
  apply osc_le hB
  intro y _ y' _
  unfold stepFn
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := le_abs_self (c i)
  have h2 := neg_abs_le (c i)
  have h3 := abs_nonneg (c i)
  split_ifs <;> linarith

lemma osc_stepFn_nonneg (V c : Fin n → ℝ) {B : Set ℝ} (hB : B.Nonempty) :
    0 ≤ osc B (stepFn V c) :=
  osc_nonneg hB (stepFn_image_finite V c B)

/-- A step function depends on the height `y` only through the set of points of height at
most `y`. -/
lemma stepFn_congr_height (V c : Fin n → ℝ) {y y' : ℝ} (h : ∀ i, V i ≤ y ↔ V i ≤ y') :
    stepFn V c y = stepFn V c y' := by
  unfold stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : V i ≤ y
  · rw [ite_eq_left hi, ite_eq_left ((h i).mp hi)]
  · rw [ite_eq_right hi, ite_eq_right (fun h' => hi ((h i).mpr h'))]

/-- A step function with one jump, at the height of the point `i`. -/
lemma stepFn_single (V d : Fin n → ℝ) (i : Fin n) (hd : ∀ k, k ≠ i → d k = 0) (y : ℝ) :
    stepFn V d y = if V i ≤ y then d i else 0 := by
  unfold stepFn
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rw [hd k hk]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **One jump outside `B`** (Step 1 of the proof of Lemma 2.6). "If `V_i ∉ B`, the added
function is constant on `B`": a step function with its only jump at the height `V_i`, of size
`d_i`, is constant on a vertical interval `B = [s, t)` that does not contain `V_i`. Its value
on `B` is `d_i` if `V_i` lies below `B`, and `0` if `V_i` lies above `B`. -/
lemma stepFn_single_eq_of_notMem (V d : Fin n → ℝ) (i : Fin n) (hd : ∀ k, k ≠ i → d k = 0)
    {s t : ℝ} (hi : V i ∉ Set.Ico s t) {y : ℝ} (hy : y ∈ Set.Ico s t) :
    stepFn V d y = if V i < s then d i else 0 := by
  rw [stepFn_single V d i hd]
  by_cases hlo : V i < s
  · -- `V_i` lies below `B`, so the jump is counted at every height of `B`
    rw [ite_eq_left hlo, ite_eq_left (hlo.le.trans hy.1)]
  · -- `V_i` lies above `B`, so the jump is counted at no height of `B`
    have hhi : t ≤ V i := by
      by_contra hlt
      exact hi ⟨not_lt.mp hlo, not_le.mp hlt⟩
    rw [ite_eq_right hlo, ite_eq_right (not_le.mpr (hy.2.trans_le hhi))]

/-- **One jump** (Step 1 of the proof of Lemma 2.6). Let the step function have its only jump
at the height `V_i`, of size `d_i`. "If `V_i ∉ B`, the added function is constant on `B`
\[…\]. If `V_i ∈ B`, the added function has oscillation at most `1` on `B`" (here: at most
`|d_i|`). -/
lemma osc_stepFn_single_le (V d : Fin n → ℝ) (i : Fin n) (hd : ∀ k, k ≠ i → d k = 0) {s t : ℝ}
    (hst : s < t) :
    osc (Set.Ico s t) (stepFn V d) ≤ if V i ∈ Set.Ico s t then |d i| else 0 := by
  have hB : (Set.Ico s t).Nonempty := ⟨s, le_rfl, hst⟩
  apply osc_le hB
  intro y hy y' hy'
  by_cases hi : V i ∈ Set.Ico s t
  · -- `V_i ∈ B`: two values of a function that takes only the values `d_i` and `0`
    rw [stepFn_single V d i hd, stepFn_single V d i hd, ite_eq_left hi]
    have h1 := le_abs_self (d i)
    have h2 := neg_abs_le (d i)
    have h3 := abs_nonneg (d i)
    split_ifs <;> linarith
  · -- `V_i ∉ B`: the function is constant on `B`
    rw [stepFn_single_eq_of_notMem V d i hd hi hy, stepFn_single_eq_of_notMem V d i hd hi hy',
      sub_self, ite_eq_right hi]

/-! ### The extrema over an interval are extrema over finitely many heights -/

/-- The candidate heights in `B = [s, t)`: the bottom `s`, and the heights of the points in
`B`. -/
def candY (s t : ℝ) (o : Option (Fin n)) (V : Fin n → ℝ) : ℝ :=
  o.elim s (fun i => if s ≤ V i ∧ V i < t then V i else s)

lemma candY_mem {s t : ℝ} (hst : s < t) (o : Option (Fin n)) (V : Fin n → ℝ) :
    candY s t o V ∈ Set.Ico s t := by
  cases o with
  | none => exact ⟨le_rfl, hst⟩
  | some i =>
    simp only [candY, Option.elim_some]
    split_ifs with h
    · exact h
    · exact ⟨le_rfl, hst⟩

lemma measurable_candY (s t : ℝ) (o : Option (Fin n)) : Measurable (candY (n := n) s t o) := by
  cases o with
  | none => exact measurable_const
  | some i =>
    change Measurable (fun V : Fin n → ℝ => if s ≤ V i ∧ V i < t then V i else s)
    refine Measurable.ite ?_ (measurable_pi_apply i) measurable_const
    exact (measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

/-- Every value of a step function on `[s, t)` is its value at a candidate height. -/
lemma exists_candY (V c : Fin n → ℝ) {s t y : ℝ} (hy : y ∈ Set.Ico s t) :
    ∃ o : Option (Fin n), stepFn V c (candY s t o V) = stepFn V c y := by
  classical
  by_cases hT : ∃ i, s ≤ V i ∧ V i ≤ y
  · have hne : (Finset.univ.filter (fun i => s ≤ V i ∧ V i ≤ y)).Nonempty := by
      obtain ⟨i, hi⟩ := hT
      exact ⟨i, by simp [hi]⟩
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ V hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hmax
    refine ⟨some i, stepFn_congr_height V c fun k => ?_⟩
    have hc : candY s t (some i) V = V i := by
      simp only [candY, Option.elim_some]
      rw [ite_eq_left ⟨hi.1, hi.2.trans_lt hy.2⟩]
    rw [hc]
    constructor
    · intro hk
      exact hk.trans hi.2
    · intro hk
      by_cases hs : s ≤ V k
      · exact hmax k ⟨hs, hk⟩
      · exact (not_le.mp hs).le.trans hi.1
  · refine ⟨none, stepFn_congr_height V c fun k => ?_⟩
    simp only [candY, Option.elim_none]
    constructor
    · intro hk
      exact hk.trans hy.1
    · intro hk
      by_contra hs
      exact hT ⟨k, (not_le.mp hs).le, hk⟩

/-- `max_B` of a step function over `B = [s, t)` is the maximum over the candidate heights. -/
theorem maxOn_Ico_stepFn (V c : Fin n → ℝ) {s t : ℝ} (hst : s < t) :
    maxOn (Set.Ico s t) (stepFn V c) = ⨆ o : Option (Fin n), stepFn V c (candY s t o V) := by
  have hB : (Set.Ico s t).Nonempty := ⟨s, le_rfl, hst⟩
  apply le_antisymm
  · apply maxOn_le hB
    intro y hy
    obtain ⟨o, ho⟩ := exists_candY V c hy
    rw [← ho]
    exact le_ciSup (f := fun o : Option (Fin n) => stepFn V c (candY s t o V))
      (Set.finite_range _).bddAbove o
  · exact ciSup_le fun o => le_maxOn (stepFn_image_finite V c _) (candY_mem hst o V)

/-- `min_B` of a step function over `B = [s, t)` is the minimum over the candidate heights. -/
theorem minOn_Ico_stepFn (V c : Fin n → ℝ) {s t : ℝ} (hst : s < t) :
    minOn (Set.Ico s t) (stepFn V c) = ⨅ o : Option (Fin n), stepFn V c (candY s t o V) := by
  have hB : (Set.Ico s t).Nonempty := ⟨s, le_rfl, hst⟩
  apply le_antisymm
  · exact le_ciInf fun o => minOn_le (stepFn_image_finite V c _) (candY_mem hst o V)
  · apply le_minOn hB
    intro y hy
    obtain ⟨o, ho⟩ := exists_candY V c hy
    rw [← ho]
    exact ciInf_le (f := fun o : Option (Fin n) => stepFn V c (candY s t o V))
      (Set.finite_range _).bddBelow o

lemma measurable_stepFn_candY (c : Fin n → ℝ) (s t : ℝ) (o : Option (Fin n)) :
    Measurable (fun V : Fin n → ℝ => stepFn V c (candY s t o V)) := by
  unfold stepFn
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i) (measurable_candY s t o))
    measurable_const measurable_const

/-- The oscillation of a step function on a vertical interval is a measurable function of the
heights. -/
theorem measurable_osc_Ico_stepFn (c : Fin n → ℝ) {s t : ℝ} (hst : s < t) :
    Measurable (fun V : Fin n → ℝ => osc (Set.Ico s t) (stepFn V c)) := by
  have h : (fun V : Fin n → ℝ => osc (Set.Ico s t) (stepFn V c)) =
      fun V => (⨆ o : Option (Fin n), stepFn V c (candY s t o V)) -
        ⨅ o : Option (Fin n), stepFn V c (candY s t o V) := by
    funext V
    unfold osc
    rw [maxOn_Ico_stepFn V c hst, minOn_Ico_stepFn V c hst]
  rw [h]
  exact (Measurable.iSup fun o => measurable_stepFn_candY c s t o).sub
    (Measurable.iInf fun o => measurable_stepFn_candY c s t o)

end

end R56Audit
