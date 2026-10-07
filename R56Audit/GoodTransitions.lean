import Oscillation

/-!
# Good transitions: the regions, `δ_j`, `δ_*`, Lemma 2.5(i), and the event of Section 2.1

Auditor's supplement (not part of the audited archive).

In the transition `j → j+1`, the comparison rectangle with indices `(c, v)` is `R = I × J`,
where `I = [c b^{-j}, (c+1) b^{-j}]` is the `c`-th horizontal interval of stage `j` and
`J = [v b^{j+1-h}, (v+1) b^{j+1-h})` the `v`-th vertical interval of stage `j+1`; it consists
of `b` old cells of height `b^{j-h}`. Horizontal intervals are closed and vertical intervals
are closed at the bottom and open at the top, as in the manuscript.

| Manuscript | Here |
| --- | --- |
| inner region `R^in`: `R` without its bottom and top old cells | `innerRegion b h j c v` |
| `m_R` | `innerCount b h j P c v` |
| `R^in` is heavy: `m_R > bn/M`, `M = b^{h-1}` | `Heavy b h j P c v` |
| the transition is good: at least `n/2` points lie in inner regions that are not heavy | `GoodTransition b h j P` |
| `δ_j` of (11), `δ_*` of (12) | `delta b h j P`, `deltaStar n b h` |
| "all heights are distinct" | `Function.Injective fun i => (P i).2` |
| "no coordinate of a point has the form `k/b^r`" | `NoGrid b P` |
| the probability-one event of Section 2.1 | `SetupEvent b P` |

* `lemma_2_5_i`: **Lemma 2.5(i)**, on `G_j` we have `δ_j ≥ δ_*`. This is a statement about
  the numbers of points in the regions, for every position of the points; the proof is the
  one of the manuscript.
* `measurableSet_goodTransition`: the events `G_j` are measurable.

Lemma 2.5(ii) is proved in `Crowding.lean`. (`StageGeometry.lean` identifies `innerRegion`
with the comparison rectangle without its bottom and top old cells.)

**The probability-one event of Section 2.1**: "all heights are distinct and \[…\] no
coordinate of a point has the form `k/b^r` with integers `k` and `r ≥ 0`" is `SetupEvent b P`;
it has probability one (`ae_setupEvent`). The points of the manuscript lie in `[0,1]²`; on
this event their coordinates then lie in `(0,1)`, since `0 = 0/b^0` and `1 = 1/b^0`
(`inUnit_of_noGrid`). The supplement uses the two halves of the event separately, and only
where they are needed; `InUnit` (all coordinates in `(0,1]`) holds almost surely for the
law `unifPts n` (`ae_inUnit`).
-/

namespace R56Audit

open MeasureTheory Finset Riesz Riesz.PointSets Oscillation

open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ### Regions, counts, good transitions -/

/-- The inner region `R^in` of the comparison rectangle `R = I × J` of the transition
`j → j+1`, with `I = [c b^{-j}, (c+1) b^{-j}]` and `J = [v b^{j+1-h}, (v+1) b^{j+1-h})`: the
points of `R` whose height lies in `J` without its bottom and top blocks of length `b^{j-h}`,
that is, in `[v b^{j+1-h} + b^{j-h}, (v+1) b^{j+1-h} - b^{j-h})`. -/
def innerRegion (b h j c v : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
    Set.Ico (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h)
      ((((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h)

/-- `m_R`: the number of points in the inner region of `R`. -/
def innerCount (b h j : ℕ) (P : Fin n → ℝ × ℝ) (c v : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => P i ∈ innerRegion b h j c v)).card

/-- The inner region is heavy: `m_R > b n / M`, with `M = b^{h-1}`. -/
def Heavy (b h j : ℕ) (P : Fin n → ℝ × ℝ) (c v : ℕ) : Prop :=
  (b : ℝ) * n / (b : ℝ) ^ (h - 1) < innerCount b h j P c v

/-- The transition `j → j+1` is good: at least `n/2` points lie in inner regions that are
not heavy. -/
def GoodTransition (b h j : ℕ) (P : Fin n → ℝ × ℝ) : Prop :=
  (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
    P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)).card

/-- `δ_j = (1 / (4bM)) Σ_R √(m_R)`, display (11). -/
def delta (b h j : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), Real.sqrt (innerCount b h j P c v)) /
    (4 * (b : ℝ) * (b : ℝ) ^ (h - 1))

/-- `δ_* = (1 / (8 b^{3/2})) √(n/M)`, display (12). -/
def deltaStar (n b h : ℕ) : ℝ :=
  1 / (8 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))

/-! ### Lemma 2.5(i) -/

/-- `x^{3/2} = x √x` for `x ≥ 0`. -/
lemma rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rcases hx.eq_or_lt with rfl | h
  · rw [Real.zero_rpow (by norm_num), zero_mul]
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one,
      ← Real.sqrt_eq_rpow]

/-- **Lemma 2.5(i).** On `G_j` we have `δ_j ≥ δ_*`.

"An inner region that is not heavy has `m_R ≤ bn/M`, and hence `√(m_R) ≥ m_R / √(bn/M)`. On
`G_j` these regions hold at least `n/2` points in total, so `Σ_R √(m_R) ≥ (n/2) √(M/(bn))`."

No condition on the position of the points. -/
theorem lemma_2_5_i {b h j : ℕ} (hn : 0 < n) (hb : 0 < b) (P : Fin n → ℝ × ℝ)
    (hG : GoodTransition b h j P) : deltaStar n b h ≤ delta b h j P := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  -- the threshold `T = bn/M` for heavy regions
  have hT : (0 : ℝ) < (b : ℝ) * n / (b : ℝ) ^ (h - 1) := by positivity
  have hsT : 0 < Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) := Real.sqrt_pos.mpr hT
  -- a region that is not heavy has `√m ≥ m / √T`
  have hsqrt : ∀ (c : Fin (b ^ j)) (v : Fin (b ^ (h - j - 1))), ¬ Heavy b h j P c v →
      (innerCount b h j P c v : ℝ) / Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) ≤
        Real.sqrt (innerCount b h j P c v) := by
    intro c v hnh
    have hle : (innerCount b h j P c v : ℝ) ≤ (b : ℝ) * n / (b : ℝ) ^ (h - 1) := not_lt.mp hnh
    have hm0 : (0 : ℝ) ≤ innerCount b h j P c v := Nat.cast_nonneg _
    rw [div_le_iff₀ hsT]
    calc (innerCount b h j P c v : ℝ)
        = Real.sqrt (innerCount b h j P c v) * Real.sqrt (innerCount b h j P c v) :=
          (Real.mul_self_sqrt hm0).symm
      _ ≤ Real.sqrt (innerCount b h j P c v) * Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _)
  -- the regions that are not heavy hold at least `n/2` points in total
  let S : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1))) :=
    Finset.univ.filter (fun p => ¬ Heavy b h j P p.1 p.2)
  have hcount : (n : ℝ) / 2 ≤ ∑ p ∈ S, (innerCount b h j P p.1 p.2 : ℝ) := by
    refine hG.trans ?_
    have hsub : (Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
        P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)) ⊆
        S.biUnion (fun p => Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1 p.2)) := by
      intro i hi
      obtain ⟨c, v, hin, hnh⟩ := (Finset.mem_filter.mp hi).2
      exact Finset.mem_biUnion.mpr ⟨(c, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnh⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩⟩
    have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have : ((Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
        P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)).card : ℝ) ≤
        ((∑ p ∈ S, (Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1 p.2)).card : ℕ) : ℝ) :=
      by exact_mod_cast hcard
    refine this.trans (le_of_eq ?_)
    push_cast
    rfl
  -- hence `Σ_R √(m_R) ≥ (n/2) / √T`
  have hsum : (n : ℝ) / 2 / Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) ≤
      ∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), Real.sqrt (innerCount b h j P c v) := by
    calc (n : ℝ) / 2 / Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1))
        ≤ (∑ p ∈ S, (innerCount b h j P p.1 p.2 : ℝ)) /
            Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) :=
          div_le_div_of_nonneg_right hcount hsT.le
      _ = ∑ p ∈ S, (innerCount b h j P p.1 p.2 : ℝ) /
            Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) := Finset.sum_div _ _ _
      _ ≤ ∑ p ∈ S, Real.sqrt (innerCount b h j P p.1 p.2) :=
          Finset.sum_le_sum fun p hp => hsqrt p.1 p.2 (Finset.mem_filter.mp hp).2
      _ ≤ ∑ p : Fin (b ^ j) × Fin (b ^ (h - j - 1)), Real.sqrt (innerCount b h j P p.1 p.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun p _ _ => Real.sqrt_nonneg _
      _ = ∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)),
            Real.sqrt (innerCount b h j P c v) := Fintype.sum_prod_type _
  -- `δ_* = (n/2) / √T / (4bM)`
  have hstar : deltaStar n b h =
      (n : ℝ) / 2 / Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) /
        (4 * (b : ℝ) * (b : ℝ) ^ (h - 1)) := by
    have hq : (0 : ℝ) < n / (b : ℝ) ^ (h - 1) := by positivity
    have hsq : 0 < Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) := Real.sqrt_pos.mpr hq
    have hsb : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr hbR
    have e1 : Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) =
        Real.sqrt b * Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) := by
      rw [mul_div_assoc, Real.sqrt_mul hbR.le]
    have e2 : (n : ℝ) = Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) *
        Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) * (b : ℝ) ^ (h - 1) := by
      rw [Real.mul_self_sqrt hq.le]
      field_simp
    unfold deltaStar
    rw [e1, rpow_three_halves_eq_mul_sqrt hbR.le]
    have hbs : Real.sqrt (b : ℝ) ≠ 0 := hsb.ne'
    have hqs : Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) ≠ 0 := hsq.ne'
    rw [div_div, div_div, eq_div_iff (by positivity)]
    nth_rewrite 3 [e2]
    field_simp
    norm_num
  rw [hstar]
  unfold delta
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-! ### Measurability -/

lemma measurableSet_innerRegion (b h j c v : ℕ) : MeasurableSet (innerRegion b h j c v) :=
  measurableSet_Icc.prod measurableSet_Ico

/-- The event `G_j` is measurable. -/
theorem measurableSet_goodTransition (b h j : ℕ) :
    MeasurableSet {P : Fin n → ℝ × ℝ | GoodTransition b h j P} := by
  -- the event depends on `P` only through finitely many membership bits
  let Φ : (Fin n → ℝ × ℝ) → (Fin n → Fin (b ^ j) → Fin (b ^ (h - j - 1)) → Bool) :=
    fun P i c v => decide (P i ∈ innerRegion b h j c v)
  have hΦ : Measurable Φ := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun c =>
      measurable_pi_iff.mpr fun v => ?_
    refine measurable_to_bool ?_
    have : (fun P : Fin n → ℝ × ℝ => decide (P i ∈ innerRegion b h j c v)) ⁻¹' {true} =
        (fun P : Fin n → ℝ × ℝ => P i) ⁻¹' innerRegion b h j c v := by
      ext P
      simp
    rw [this]
    exact (measurable_pi_apply i) (measurableSet_innerRegion b h j c v)
  let G : (Fin n → Fin (b ^ j) → Fin (b ^ (h - j - 1)) → Bool) → Prop := fun φ =>
    (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
      φ i c v = true ∧ ¬ ((b : ℝ) * n / (b : ℝ) ^ (h - 1) <
        ((Finset.univ.filter (fun i' => φ i' c v = true)).card : ℝ)))).card
  have hG : {P : Fin n → ℝ × ℝ | GoodTransition b h j P} = Φ ⁻¹' {φ | G φ} := by
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, GoodTransition, Heavy, innerCount, G, Φ,
      decide_eq_true_eq]
    exact Iff.of_eq (by congr!)
  rw [hG]
  exact hΦ (Set.toFinite _).measurableSet

/-! ### The probability-one event of Section 2.1 -/

/-- All coordinates of all points lie in `(0, 1]`; this holds almost surely. -/
def InUnit (P : Fin n → ℝ × ℝ) : Prop :=
  ∀ i, (P i).1 ∈ Set.Ioc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ioc (0 : ℝ) 1

/-- "no coordinate of a point has the form `k/b^r` with integers `k` and `r ≥ 0`": no point
lies on a grid line. -/
def NoGrid (b : ℕ) (P : Fin n → ℝ × ℝ) : Prop :=
  ∀ i, ∀ (k : ℤ) (r : ℕ), (P i).1 ≠ (k : ℝ) / (b : ℝ) ^ r ∧ (P i).2 ≠ (k : ℝ) / (b : ℝ) ^ r

/-- Almost surely all coordinates of `n` independent uniform points lie in `(0,1]`. -/
theorem ae_inUnit (n : ℕ) : ∀ᵐ P ∂unifPts n, InUnit P := by
  rw [← pointSampleLaw_eq_unifPts]
  exact ae_pointSampleLaw_mem_Ioc n

/-- Almost surely no coordinate of `n` independent uniform points has the form `k/b^r`. -/
theorem ae_noGrid (n b : ℕ) : ∀ᵐ P ∂unifPts n, NoGrid b P := by
  rw [← pointSampleLaw_eq_unifPts]
  refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => ae_all_iff.mpr fun r => ?_
  have hI : ∀ᵐ x ∂μI, x ≠ (k : ℝ) / (b : ℝ) ^ r := by
    rw [ae_iff]
    simp
  have hprod : ∀ᵐ z ∂μI.prod μI,
      z.1 ≠ (k : ℝ) / (b : ℝ) ^ r ∧ z.2 ≠ (k : ℝ) / (b : ℝ) ^ r := by
    have hms : MeasurableSet {z : ℝ × ℝ |
        z.1 ≠ (k : ℝ) / (b : ℝ) ^ r ∧ z.2 ≠ (k : ℝ) / (b : ℝ) ^ r} :=
      (measurableSet_eq_fun measurable_fst measurable_const).compl.inter
        (measurableSet_eq_fun measurable_snd measurable_const).compl
    apply (Measure.ae_prod_iff_ae_ae hms).mpr
    filter_upwards [hI] with u hu
    filter_upwards [hI] with v hv
    exact ⟨hu, hv⟩
  exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μI.prod μI) (i := i) hprod

/-- "all heights are distinct", almost surely. -/
theorem ae_heights_injective (n : ℕ) :
    ∀ᵐ P ∂unifPts n, Function.Injective fun i => (P i).2 := by
  rw [← pointSampleLaw_eq_unifPts]
  -- two given points have different heights, almost surely
  have hpair : ∀ i j : Fin n, i ≠ j → ∀ᵐ P ∂pointSampleLaw n, (P i).2 ≠ (P j).2 := by
    intro i j hij
    have hset : {P : Fin n → ℝ × ℝ | ¬ (P i).2 ≠ (P j).2} =
        splitCoordinates n ⁻¹' (Set.univ ×ˢ {y : Fin n → ℝ | y i = y j}) := by
      ext P
      simp [splitCoordinates_apply]
    rw [ae_iff, hset, (splitCoordinates_measurePreserving n).measure_preimage_equiv,
      Measure.prod_prod, diag_null i j hij, mul_zero]
  have hall : ∀ᵐ P ∂pointSampleLaw n, ∀ i j : Fin n, i ≠ j → (P i).2 ≠ (P j).2 := by
    refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · filter_upwards [hpair i j hij] with P hP _
      exact hP
  filter_upwards [hall] with P hP i j hV
  by_contra hij
  exact hP i j hij hV

/-- **The probability-one event of Section 2.1**: "all heights are distinct and \[…\] no
coordinate of a point has the form `k/b^r` with integers `k` and `r ≥ 0`". -/
def SetupEvent (b : ℕ) (P : Fin n → ℝ × ℝ) : Prop :=
  (Function.Injective fun i => (P i).2) ∧ NoGrid b P

/-- The event of Section 2.1 has probability one. -/
theorem ae_setupEvent (n b : ℕ) : ∀ᵐ P ∂unifPts n, SetupEvent b P := by
  filter_upwards [ae_heights_injective n, ae_noGrid n b] with P h1 h2
  exact ⟨h1, h2⟩

/-- Points of the unit square `[0,1]²` no coordinate of which has the form `k/b^r` have all
their coordinates in `(0,1)`, in particular in `(0,1]`: `0 = 0/b^0` and `1 = 1/b^0`. -/
lemma inUnit_of_noGrid {b : ℕ} {P : Fin n → ℝ × ℝ}
    (hP : ∀ i, (P i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Icc (0 : ℝ) 1)
    (hgrid : NoGrid b P) : InUnit P := by
  intro i
  have h0 := hgrid i 0 0
  simp only [Int.cast_zero, pow_zero, div_one] at h0
  exact ⟨⟨lt_of_le_of_ne (hP i).1.1 (Ne.symm h0.1), (hP i).1.2⟩,
    ⟨lt_of_le_of_ne (hP i).2.1 (Ne.symm h0.2), (hP i).2.2⟩⟩

end

end R56Audit
