import Oscillation.Stages
import R56Audit.LocalGain

/-!
# The local gain of the archive's finite-probe potential, for every base

Auditor's supplement (not part of the audited archive).

The archive's potential `Oscillation.gridPotential` takes the extrema of the endpoint averages
over finitely many grid heights (probes), and its conditional-gain estimate
`Oscillation.gridPotential_drift_even` is proved for even bases only, by a different argument
(representative heights and half-digit Rademacher signs).

This file derives the same estimate for **every integer base `b ≥ 2`** from Lemma 2.3 of the
manuscript, in the form `local_gain_sets`: the blocks `B_ℓ` are the sets of probes of the old
cells, `J` is the set of probes of the comparison rectangle, and a point with vertical label
`Y i` sits at height `Y i + 1/2`, strictly between two probes.

* `endpointValue_eq_endpointAvg`, `endpointValue_refined_eq_childAvg`: the archive's endpoint
  values are `endpointAvg` and `childAvg` of `LocalGain.lean`, at integer heights;
* `gridOsc_eq_osc`: the archive's `gridOsc` is `osc` over the set of probes;
* `local_gridOsc_gain`: Lemma 2.3 on one comparison rectangle of the probe model;
* `gridPotential_drift_all`: the conditional gain (11) of the probe potential, every `b ≥ 2`.
  It has the statement of `Oscillation.gridPotential_drift_even` without `Even b`.
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ}

/-! ### The probe model as an instance of the local experiment -/

/-- A point with vertical label `Y i` is placed at height `Y i + 1/2`, so that being strictly
below the probe `y` (`Y i < y`) is `Y i + 1/2 ≤ y`. -/
def gridHeights (Y : Fin n → ℕ) : Fin n → ℝ := fun i => (Y i : ℝ) + 1 / 2

/-- The position of the point with horizontal label `p i` relative to the cell `c`. -/
def gridSide (p : Fin n → ℕ) (c : ℕ) : Fin n → Side :=
  fun i => if p i < c then Side.left else if p i = c then Side.inside else Side.right

lemma gridHeights_le_iff (Y : Fin n → ℕ) (i : Fin n) (y : ℕ) :
    gridHeights Y i ≤ (y : ℝ) ↔ Y i < y := by
  unfold gridHeights
  constructor
  · intro h
    by_contra hlt
    have : (y : ℝ) ≤ Y i := by exact_mod_cast not_lt.mp hlt
    linarith
  · intro h
    have : ((Y i : ℕ) : ℝ) + 1 ≤ y := by exact_mod_cast h
    linarith

lemma endpointWeight_eq_oldWeight (p : Fin n → ℕ) (c : ℕ) (i : Fin n) :
    endpointWeight (p i) c = oldWeight (gridSide p c i) := by
  unfold endpointWeight gridSide
  by_cases h1 : p i < c
  · have h2 : p i ≠ c := ne_of_lt h1
    simp [h1, h2, oldWeight]
  · by_cases h2 : p i = c
    · simp [h2, oldWeight]
    · simp [h1, h2, oldWeight]

lemma endpointWeight_refine_eq_childWeight {b : ℕ} (hb : 0 < b) (p : Fin n → ℕ) (c : ℕ)
    (r : Fin n → Fin b) (k : Fin b) (i : Fin n) :
    endpointWeight (b * p i + (r i).val) (b * c + k.val) =
      childWeight (gridSide p c i) (r i) k := by
  rw [endpointWeight_refine hb]
  unfold gridSide
  by_cases h1 : p i < c
  · simp [h1, childWeight]
  · by_cases h2 : p i = c
    · simp only [h2, lt_self_iff_false, ite_false, ite_true, childWeight, endpointWeight]
      by_cases h3 : r i < k
      · have h3' : (r i).val < k.val := h3
        have h4 : (r i).val ≠ k.val := ne_of_lt h3'
        simp [h3, h3', h4]
      · by_cases h4 : r i = k
        · simp [h4]
        · have h3' : ¬ (r i).val < k.val := h3
          have h4' : (r i).val ≠ k.val := fun h => h4 (Fin.ext h)
          simp [h3, h4, h3', h4']
    · simp [h1, h2, childWeight]

/-- The archive's endpoint value at the probe `y` is the endpoint average of
`LocalGain.lean` at the height `y`. -/
lemma endpointValue_eq_endpointAvg (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (c y : ℕ) :
    endpointValue χ p Y c y = endpointAvg χ (gridHeights Y) (gridSide p c) (y : ℝ) := by
  unfold endpointValue endpointAvg stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [endpointWeight_eq_oldWeight]
  by_cases h : Y i < y
  · rw [ite_eq_left h, ite_eq_left ((gridHeights_le_iff Y i y).mpr h)]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((gridHeights_le_iff Y i y).mp h'))]
    ring

/-- After the next digits `r` are revealed, the archive's endpoint value of the child cell
`b c + k` is the child function `a_{k+1}` of `LocalGain.lean`. -/
lemma endpointValue_refined_eq_childAvg {b : ℕ} (hb : 0 < b) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) (c : ℕ) (r : Fin n → Fin b) (k : Fin b) (y : ℕ) :
    endpointValue χ (refinedPositions p r) Y (b * c + k.val) y =
      childAvg χ (gridHeights Y) (gridSide p c) r k (y : ℝ) := by
  unfold endpointValue childAvg stepFn refinedPositions
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [endpointWeight_refine_eq_childWeight hb]
  by_cases h : Y i < y
  · rw [ite_eq_left h, ite_eq_left ((gridHeights_le_iff Y i y).mpr h)]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((gridHeights_le_iff Y i y).mp h'))]
    ring

/-- The archive's oscillation over `m` probes is `osc` over the whole index set. -/
lemma gridOsc_eq_osc {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) :
    gridOsc hm f = osc (Set.univ : Set (Fin m)) f := by
  have hfin : (f '' (Set.univ : Set (Fin m))).Finite := (Set.finite_univ).image f
  have hne : (Set.univ : Set (Fin m)).Nonempty := ⟨⟨0, hm⟩, trivial⟩
  apply le_antisymm
  · obtain ⟨t1, ht1⟩ := gridMax_exists hm f
    obtain ⟨t2, ht2⟩ := gridMax_exists hm (fun t => -f t)
    unfold gridOsc
    rw [ht1, ht2]
    have := sub_le_osc hfin (Set.mem_univ t1) (Set.mem_univ t2)
    linarith
  · apply osc_le hne
    intro y _ y' _
    have h1 := le_gridMax hm f y
    have h2 := le_gridMax hm (fun t => -f t) y'
    unfold gridOsc
    linarith

/-- Sampling a function of the height at the probes. -/
lemma osc_univ_comp {m : ℕ} (probe : Fin m → ℝ) (G : ℝ → ℝ) :
    osc (Set.univ : Set (Fin m)) (fun t => G (probe t)) = osc (Set.range probe) G := by
  have h : (fun t => G (probe t)) '' (Set.univ : Set (Fin m)) = G '' Set.range probe := by
    rw [Set.image_univ, ← Set.range_comp]
    rfl
  unfold osc maxOn minOn
  rw [h]

/-- The probes of the block `w` of `m` fine rows: the heights `w m + t + 1`, `t < m`. -/
def probes (m w : ℕ) : Set ℝ := Set.range (fun t : Fin m => ((w * m + t.val + 1 : ℕ) : ℝ))

lemma gridOsc_blockValues {m : ℕ} (hm : 0 < m) (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (c w : ℕ) :
    gridOsc hm (blockValues χ p Y c w) =
      osc (probes m w) (endpointAvg χ (gridHeights Y) (gridSide p c)) := by
  rw [gridOsc_eq_osc, probes, ← osc_univ_comp]
  congr 1
  funext t
  exact endpointValue_eq_endpointAvg χ p Y c _

lemma gridOsc_blockValues_refined {b m : ℕ} (hb : 0 < b) (hm : 0 < m) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) (c v : ℕ) (r : Fin n → Fin b) (k : Fin b) :
    gridOsc hm (blockValues χ (refinedPositions p r) Y (b * c + k.val) v) =
      osc (probes m v) (childAvg χ (gridHeights Y) (gridSide p c) r k) := by
  rw [gridOsc_eq_osc, probes, ← osc_univ_comp]
  congr 1
  funext t
  exact endpointValue_refined_eq_childAvg hb χ p Y c r k _

/-! ### Lemma 2.3 on one comparison rectangle of the probe model -/

/-- **Lemma 2.3 in the probe model**, for every integer base `b ≥ 2`: on the comparison
rectangle with horizontal cell `c` and vertical index `v`, the expected sum of the
oscillations of the `b` new cells is at least the sum of the oscillations of the `b` old
cells plus `(1/4) √(m_R)`, where `m_R = interiorCount b m p Y c v`. -/
theorem local_gridOsc_gain {b m : ℕ} (hb : 2 ≤ b) (hm : 0 < m) (χ : Fin n → ℝ)
    (hχ : ∀ i, |χ i| = 1) (p Y : Fin n → ℕ) (c v : ℕ) :
    (∑ l : Fin b, gridOsc hm (blockValues χ p Y c (v * b + l.val))) +
        Real.sqrt (interiorCount b m p Y c v) / 4 ≤
      finAvg (fun r : Fin n → Fin b => ∑ k : Fin b,
        gridOsc (Nat.mul_pos (by omega : 0 < b) hm)
          (blockValues χ (refinedPositions p r) Y (b * c + k.val) v)) := by
  have hb0 : 0 < b := by omega
  have H := local_gain_sets hb χ hχ (gridHeights Y) (gridSide p c) (probes (b * m) v)
    (fun l : Fin b => probes m (v * b + l.val))
    (fun l => Set.range_nonempty_iff_nonempty.mpr ⟨⟨0, hm⟩⟩)
    (by
      rintro l _ ⟨t, rfl⟩
      refine ⟨⟨l.val * m + t.val, ?_⟩, ?_⟩
      · have h1 : l.val + 1 ≤ b := l.isLt
        have h2 : t.val + 1 ≤ m := t.isLt
        nlinarith [Nat.mul_le_mul_right m h1]
      · simp only
        congr 1
        ring)
    (interiorIndices b m p Y c v)
    (by
      intro i hi
      have hi' : p i = c ∧ v * (b * m) + m ≤ Y i ∧ Y i < v * (b * m) + (b - 1) * m := by
        simpa [interiorIndices] using hi
      refine ⟨by simp [gridSide, hi'.1], ?_, ?_⟩
      · rintro _ ⟨t, rfl⟩
        have h2 : t.val + 1 ≤ m := t.isLt
        have hle : (v * b + 0) * m + t.val + 1 ≤ Y i := by nlinarith [hi'.2.1]
        have hR : (((v * b + 0) * m + t.val + 1 : ℕ) : ℝ) ≤ (Y i : ℝ) := by exact_mod_cast hle
        simp only [gridHeights]
        linarith
      · rintro _ ⟨t, rfl⟩
        have hlt : Y i < (v * b + (b - 1)) * m + t.val + 1 := by nlinarith [hi'.2.2]
        exact (gridHeights_le_iff Y i _).mpr hlt)
  have hold : ∀ l : Fin b, gridOsc hm (blockValues χ p Y c (v * b + l.val)) =
      osc (probes m (v * b + l.val)) (endpointAvg χ (gridHeights Y) (gridSide p c)) :=
    fun l => gridOsc_blockValues hm χ p Y c _
  have hnew : ∀ (r : Fin n → Fin b) (k : Fin b),
      gridOsc (Nat.mul_pos hb0 hm) (blockValues χ (refinedPositions p r) Y (b * c + k.val) v) =
        osc (probes (b * m) v) (childAvg χ (gridHeights Y) (gridSide p c) r k) :=
    fun r k => gridOsc_blockValues_refined hb0 (Nat.mul_pos hb0 hm) χ p Y c v r k
  simp_rw [hold, hnew]
  have hc : Real.sqrt (interiorCount b m p Y c v) / 4 =
      1 / 4 * Real.sqrt ((interiorIndices b m p Y c v).card) := by
    unfold interiorCount
    ring
  rw [hc]
  exact H

/-! ### Summing over the comparison rectangles: the conditional gain of the probe potential -/

lemma gridOsc_numerator_split_old (K V b m : ℕ) (hm : 0 < m) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) :
    (∑ c : Fin K, ∑ w : Fin (V * b), gridOsc hm (blockValues χ p Y c.val w.val)) =
      ∑ c : Fin K, ∑ v : Fin V, ∑ l : Fin b,
        gridOsc hm (blockValues χ p Y c.val (v.val * b + l.val)) := by
  apply Finset.sum_congr rfl
  intro c _
  simpa only [Nat.mul_comm] using
    (sum_fin_mul (K := V) (b := b) (fun w => gridOsc hm (blockValues χ p Y c.val w)))

lemma gridOsc_numerator_split_new (K V b m : ℕ) (hm : 0 < m) (χ : Fin n → ℝ)
    (p Y : Fin n → ℕ) :
    (∑ w : Fin (K * b), ∑ v : Fin V, gridOsc hm (blockValues χ p Y w.val v.val)) =
      ∑ c : Fin K, ∑ v : Fin V, ∑ k : Fin b,
        gridOsc hm (blockValues χ p Y (b * c.val + k.val) v.val) := by
  rw [sum_fin_mul (fun w => ∑ v : Fin V, gridOsc hm (blockValues χ p Y w v.val))]
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.sum_comm

/-- **The conditional gain (11) of the probe potential, for every integer base `b ≥ 2`.**
This is the statement of the archive's `Oscillation.gridPotential_drift_even` without the
hypothesis `Even b`; it is proved from Lemma 2.3 of the manuscript (`local_gain_sets`). -/
theorem gridPotential_drift_all {K V b m : ℕ} (hK : 0 < K) (hV : 0 < V) (hb : 2 ≤ b)
    (hm : 0 < m) (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (p Y : Fin n → ℕ) :
    interiorMass K V b m p Y / (4 * (b : ℝ) * (K * V : ℕ)) ≤
      finAvg (fun r : Fin n → Fin b =>
        gridPotential (K * b) V (b * m) (Nat.mul_pos (by omega : 0 < b) hm) χ
          (refinedPositions p r) Y) -
      gridPotential K (V * b) m hm χ p Y := by
  have hb0 : 0 < b := by omega
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin K))) (fun c _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin V))) (fun v _ =>
      local_gridOsc_gain hb hm χ hχ p Y c.val v.val))
  simp only [Finset.sum_add_distrib, ← Finset.sum_div] at hs
  have hn : (∑ c : Fin K, ∑ w : Fin (V * b), gridOsc hm (blockValues χ p Y c.val w.val)) +
      interiorMass K V b m p Y / 4 ≤
      finAvg (fun r : Fin n → Fin b =>
        ∑ w : Fin (K * b), ∑ v : Fin V,
          gridOsc (Nat.mul_pos hb0 hm) (blockValues χ (refinedPositions p r) Y w.val v.val)) := by
    rw [gridOsc_numerator_split_old]
    simp_rw [gridOsc_numerator_split_new, finAvg_sum]
    simpa only [finAvg_sum, interiorMass] using hs
  have hden : K * (V * b) = K * b * V := by ring
  unfold gridPotential
  rw [hden, finAvg_div_const]
  have hh := div_le_div_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ (K * b * V : ℕ))
  rw [add_div] at hh
  have he : interiorMass K V b m p Y / 4 / (K * b * V : ℕ) =
      interiorMass K V b m p Y / (4 * (b : ℝ) * (K * V : ℕ)) := by
    push_cast
    ring
  rw [he] at hh
  linarith

end

end R56Audit
