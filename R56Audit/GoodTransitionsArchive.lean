import R56Audit.GoodTransitions

/-!
# The archive's good-transition event is the event `G_j` of the manuscript

Auditor's supplement (not part of the audited archive). Not used by the proof of the
manuscript's results: Lemma 2.5(ii) is proved directly in `Crowding.lean`.

The archive defines its event `Oscillation.Direct.paperGoodTransition` through cell labels:
`rectangularBucket` sends a point to the label of the region that contains it, or to `none`,
with all intervals open on the left and closed on the right (`innerRegionIoc`). The two
conventions differ only on grid lines; for points of `(0,1]²` no coordinate of which has the
form `k/b^r` (`InUnit`, `NoGrid`; both hold almost surely) the archive's event is the event
`G_j` of `GoodTransitions.lean` (`mem_paperGoodTransition_iff`).

Consequently the archive's probability estimate is a second proof of Lemma 2.5(ii) for the
regions of the manuscript: `lemma_2_5_ii_archive`, `lemma_2_5_ii_all_archive`.
-/

namespace R56Audit

open MeasureTheory Finset Riesz Riesz.PointSets Riesz.Occupancy Oscillation Oscillation.Direct
  Oscillation.Parameters

open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ### The label classes of the archive -/

/-- The region of the archive's cell label `(c, v)`: as `innerRegion`, with all intervals
open on the left and closed on the right. -/
def innerRegionIoc (b h j c v : ℕ) : Set (ℝ × ℝ) :=
  Set.Ioc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
    Set.Ioc (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h)
      ((((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h)

/-- The two conventions give the same region, except on three grid lines: the left side of
`I` and the two horizontal sides of the inner region. -/
theorem mem_innerRegion_iff_Ioc (b h j c v : ℕ) (z : ℝ × ℝ)
    (hx : z.1 ≠ (c : ℝ) / (b : ℝ) ^ j)
    (hy1 : z.2 ≠ ((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h)
    (hy2 : z.2 ≠ (((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h) :
    z ∈ innerRegion b h j c v ↔ z ∈ innerRegionIoc b h j c v := by
  unfold innerRegion innerRegionIoc
  simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨lt_of_le_of_ne h1 (Ne.symm hx), h2⟩, lt_of_le_of_ne h3 (Ne.symm hy1), h4.le⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1.le, h2⟩, h3.le, lt_of_le_of_ne h4 hy2⟩

/-- A point that lies on no grid line is in the region of the manuscript exactly when it is
in the region of the archive's label. -/
lemma mem_innerRegion_iff_of_noGrid {b : ℕ} (h j c v : ℕ) {P : Fin n → ℝ × ℝ}
    (hP : NoGrid b P) (i : Fin n) :
    P i ∈ innerRegion b h j c v ↔ P i ∈ innerRegionIoc b h j c v := by
  refine mem_innerRegion_iff_Ioc b h j c v (P i) ?_ ?_ ?_
  · have := (hP i (c : ℤ) j).1
    push_cast at this
    exact this
  · have := (hP i ((v : ℤ) * (b : ℤ) ^ (j + 1) + (b : ℤ) ^ j) h).2
    push_cast at this
    exact this
  · have := (hP i (((v : ℤ) + 1) * (b : ℤ) ^ (j + 1) - (b : ℤ) ^ j) h).2
    push_cast at this
    exact this

/-- Membership in the region of a label, with the natural-number expressions of the
archive. -/
lemma mem_innerRegionIoc_iff {b h j : ℕ} (hb : 1 ≤ b) (c v : ℕ) (z : ℝ × ℝ) :
    z ∈ innerRegionIoc b h j c v ↔
      z.1 ∈ Set.Ioc ((c : ℝ) / (b ^ j : ℕ)) (((c + 1 : ℕ) : ℝ) / (b ^ j : ℕ)) ∧
      z.2 ∈ Set.Ioc (((v * (b * b ^ j) + b ^ j : ℕ) : ℝ) / (b ^ h : ℕ))
        (((v * (b * b ^ j) + (b - 1) * b ^ j : ℕ) : ℝ) / (b ^ h : ℕ)) := by
  have e1 : (((v * (b * b ^ j) + b ^ j : ℕ) : ℝ)) =
      (v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j := by
    push_cast; ring
  have e2 : (((v * (b * b ^ j) + (b - 1) * b ^ j : ℕ) : ℝ)) =
      ((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j := by
    push_cast [Nat.cast_sub hb]; ring
  unfold innerRegionIoc
  rw [Set.mem_prod, e1, e2]
  push_cast
  rfl

/-- For a point of `(0,1]²`, the archive's bucket `(c, v)` of the transition `j → j+1` is the
region of the label `(c, v)`. -/
theorem rectangularBucket_eq_some_iff {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h)
    (c : Fin (b ^ j)) (v : Fin (b ^ (h - j - 1))) (z : ℝ × ℝ)
    (hz1 : z.1 ∈ Set.Ioc (0 : ℝ) 1) (hz2 : z.2 ∈ Set.Ioc (0 : ℝ) 1) :
    rectangularBucket (b ^ j) (b ^ (h - j - 1)) b (b ^ j) (pow_pos (by omega) j)
        (pow_pos (by omega) _) (by omega) (pow_pos (by omega) j) z =
        some (finProdFinEquiv (c, v)) ↔
      z ∈ innerRegionIoc b h j c v := by
  have hb0 : 0 < b := by omega
  have hK : 0 < b ^ j := pow_pos hb0 j
  have hNpos : 0 < b ^ (h - j - 1) * (b * b ^ j) := by positivity
  have hN : b ^ (h - j - 1) * (b * b ^ j) = b ^ h := layer_fine_size hj
  rw [rectangularBucket_some_iff, mem_innerRegionIoc_iff (by omega)]
  have h1 := fun s => finiteGridIndex_lt_iff hK hz1 s
  have h2 := fun s => finiteGridIndex_lt_iff hNpos hz2 s
  simp only [Set.mem_Ioc, ← hN]
  constructor
  · rintro ⟨hc, hlo, hhi⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · by_contra hcon
      have := (h1 c).mpr (not_lt.mp hcon)
      omega
    · exact (h1 (c + 1)).mp (by omega)
    · by_contra hcon
      have := (h2 (v * (b * b ^ j) + b ^ j)).mpr (not_lt.mp hcon)
      omega
    · exact (h2 _).mp hhi
  · rintro ⟨⟨ha, hb'⟩, ⟨hlo, hhi⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · have hlt := (h1 (c + 1)).mpr hb'
      have hge : ¬ (finiteGridIndex (b ^ j) hK z.1).val < c := fun hlt' =>
        absurd ((h1 c).mp hlt') (not_le.mpr ha)
      omega
    · by_contra hcon
      exact absurd ((h2 _).mp (not_le.mp hcon)) (not_le.mpr hlo)
    · exact (h2 _).mpr hhi

/-- **The event `G_j` of the archive.** For points of `(0,1]²` that lie on no grid line, the
archive's `paperGoodTransition` says that at least `n/2` points lie in inner regions that are
not heavy. -/
theorem mem_paperGoodTransition_iff {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h)
    (P : Fin n → ℝ × ℝ) (hP : InUnit P) (hgrid : NoGrid b P) :
    P ∈ paperGoodTransition b h (by omega) j ↔ GoodTransition b h j P := by
  have hb0 : 0 < b := by omega
  let cell : ℝ × ℝ → Option (Fin (b ^ j * b ^ (h - j - 1))) :=
    rectangularBucket (b ^ j) (b ^ (h - j - 1)) b (b ^ j) (pow_pos hb0 j) (pow_pos hb0 _) hb0
      (pow_pos hb0 j)
  let x : Fin n → Option (Fin (b ^ j * b ^ (h - j - 1))) := fun i => cell (P i)
  have hkey : ∀ i (c : Fin (b ^ j)) (v : Fin (b ^ (h - j - 1))),
      x i = some (finProdFinEquiv (c, v)) ↔ P i ∈ innerRegion b h j c v :=
    fun i c v => (rectangularBucket_eq_some_iff hb hj c v (P i) (hP i).1 (hP i).2).trans
      (mem_innerRegion_iff_of_noGrid h j c v hgrid i).symm
  have hcount : ∀ (c : Fin (b ^ j)) (v : Fin (b ^ (h - j - 1))),
      count x (finProdFinEquiv (c, v)) = innerCount b h j P c v := by
    intro c v
    unfold count innerCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hkey i c v
  have hM : (((b ^ j * b ^ (h - j - 1) : ℕ) : ℝ)) = (b : ℝ) ^ (h - 1) := by
    rw [layer_comparison_size hj]
    push_cast
    rfl
  have hheavy : ∀ (c : Fin (b ^ j)) (v : Fin (b ^ (h - j - 1))),
      finProdFinEquiv (c, v) ∈ heavy (b : ℝ) x ↔ Heavy b h j P c v := by
    intro c v
    unfold heavy Heavy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcount c v, hM]
  have hexc : ∀ i, x i ∉ exceptional (heavy (b : ℝ) x) ↔
      ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
        P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v := by
    intro i
    constructor
    · intro hnot
      cases hx : x i with
      | none => exact absurd (by simp [exceptional, hx]) hnot
      | some a =>
        obtain ⟨⟨c, v⟩, rfl⟩ := finProdFinEquiv.surjective a
        refine ⟨c, v, (hkey i c v).mp hx, fun hh => hnot ?_⟩
        simp only [exceptional, Set.mem_ofPred_eq, hx]
        exact Or.inr ⟨_, (hheavy c v).mpr hh, rfl⟩
    · rintro ⟨c, v, hin, hnh⟩ hmem
      have hx := (hkey i c v).mpr hin
      simp only [exceptional, Set.mem_ofPred_eq, hx] at hmem
      rcases hmem with h0 | ⟨a, ha, hsome⟩
      · exact absurd h0 (by simp)
      · have : a = finProdFinEquiv (c, v) := (Option.some.inj hsome).symm
        rw [this] at ha
        exact hnh ((hheavy c v).mp ha)
  -- count the points in non-heavy inner regions
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => x i ∈ exceptional (heavy (b : ℝ) x))
  simp only [Finset.card_univ, Fintype.card_fin] at hsplit
  have hgoodset : (Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
      P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)) =
      Finset.univ.filter (fun i => ¬ x i ∈ exceptional (heavy (b : ℝ) x)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hexc i).symm
  change bucketGood (b : ℝ) x ↔ _
  unfold bucketGood GoodTransition
  rw [hgoodset]
  have hsplitR : ((Finset.univ.filter (fun i => x i ∈ exceptional (heavy (b : ℝ) x))).card : ℝ) +
      (Finset.univ.filter (fun i => ¬ x i ∈ exceptional (heavy (b : ℝ) x))).card = n := by
    exact_mod_cast hsplit
  constructor
  · intro hg
    have hgR : (2 : ℝ) * (Finset.univ.filter (fun i => x i ∈ exceptional (heavy (b : ℝ) x))).card ≤
        n := by exact_mod_cast hg
    linarith
  · intro hg
    have : (2 : ℝ) * (Finset.univ.filter (fun i => x i ∈ exceptional (heavy (b : ℝ) x))).card ≤
        n := by linarith
    exact_mod_cast this

/-! ### Lemma 2.5(ii), from the archive's estimate -/

/-- Lemma 2.5(ii), one transition, from the archive's probability estimate: if `M ≤ n`, then
`Pr(G_j^c) ≤ (48/b)^{n/2}`, for every integer base `b ≥ 3`. -/
theorem lemma_2_5_ii_archive {b h j : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n) (hj : j < h) :
    (unifPts n).real {P | ¬ GoodTransition b h j P} ≤ (48 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by omega) _) hMn
  refine le_trans ?_ (R65.bad_transition_bound hn hb hMn hj)
  have hgrid := ae_noGrid n b
  rw [← pointSampleLaw_eq_unifPts] at hgrid ⊢
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_pointSampleLaw_mem_Ioc n, hgrid] with P hP hPg
  intro hbad hgood
  exact hbad ((mem_paperGoodTransition_iff (by omega) hj P hP hPg).mp hgood)

/-- Lemma 2.5(ii), all transitions, from the archive's probability estimate: if `M ≤ n`, then
`Pr(G^c) ≤ h (48/b)^{n/2}`, where `G` is the event that all `h` transitions are good. -/
theorem lemma_2_5_ii_all_archive {b h : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n) :
    (unifPts n).real {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} ≤
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by omega) _) hMn
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have : {P : Fin n → ℝ × ℝ | ∃ j, j < 0 ∧ ¬ GoodTransition b 0 j P} = ∅ := by
      ext P; simp
    rw [this]
    simp
  refine le_trans ?_ (R65.all_good_compl_bound hn hb hh hMn)
  have hgrid := ae_noGrid n b
  rw [← pointSampleLaw_eq_unifPts] at hgrid ⊢
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_pointSampleLaw_mem_Ioc n, hgrid] with P hP hPg
  rintro ⟨j, hj, hbad⟩ hall
  exact hbad ((mem_paperGoodTransition_iff (by omega) hj P hP hPg).mp (hall j hj))

end

end R56Audit
