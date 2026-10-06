import Riesz.CellAverages
import Riesz.Dyadic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-!
# Rare-set occupancy under genuine iid sampling

The probability measure is `Measure.pi (fun _ : Fin n => μ)`. No independence
or occupancy conclusion is postulated: product-event probabilities follow from
`Measure.pi_pi_finset`, and all exceptional-set choices are union bounded.
-/

namespace Riesz.Occupancy

open MeasureTheory
open scoped BigOperators ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- Number of sample coordinates lying in a set. -/
noncomputable def hitCount {n : ℕ} (A : Set α) (x : Fin n → α) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => x i ∈ A)).card

/-- The event that at least half of the coordinates lie in `A`. -/
def halfHitEvent (n : ℕ) (A : Set α) : Set (Fin n → α) :=
  {x | (n : ℝ) / 2 ≤ (hitCount A x : ℝ)}

/-- Specifying the coordinates of hits gives the exact iid product probability. -/
lemma fixed_hits_measure (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set α) (s : Finset (Fin n)) :
    (Measure.pi (fun _ : Fin n => μ)) {x | ∀ i ∈ s, x i ∈ A} = μ A ^ s.card := by
  have heq : {x : Fin n → α | ∀ i ∈ s, x i ∈ A} = (s : Set (Fin n)).pi (fun _ => A) := by
    ext x
    rfl
  rw [heq, Measure.pi_pi_finset]
  simp

/-- A fixed set of mass at most `p ≤ 1` contains at least half of `n` iid samples
with probability at most `2^n p^(n/2)`. The exponent is real, so odd `n` is included. -/
theorem iid_half_hits_le (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Set α) (p : ℝ≥0∞) (hAp : μ A ≤ p) (hp : p ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)) (halfHitEvent n A) ≤
      (2 : ℝ≥0∞) ^ n * p ^ ((n : ℝ) / 2) := by
  classical
  let E (s : Finset (Fin n)) : Set (Fin n → α) :=
    if (n : ℝ) / 2 ≤ (s.card : ℝ) then {x | ∀ i ∈ s, x i ∈ A} else ∅
  have hsubset : halfHitEvent n A ⊆ ⋃ s, E s := by
    intro x hx
    let s := Finset.univ.filter (fun i : Fin n => x i ∈ A)
    apply Set.mem_iUnion.mpr
    refine ⟨s, ?_⟩
    have hs : (n : ℝ) / 2 ≤ (s.card : ℝ) := hx
    simp only [E, hs, ite_true, Set.mem_ofPred_eq]
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hE (s : Finset (Fin n)) :
      (Measure.pi (fun _ : Fin n => μ)) (E s) ≤ p ^ ((n : ℝ) / 2) := by
    by_cases hs : (n : ℝ) / 2 ≤ (s.card : ℝ)
    · simp only [E, hs, ite_true]
      rw [fixed_hits_measure]
      calc
        μ A ^ s.card ≤ p ^ s.card := pow_le_pow_left' hAp s.card
        _ = p ^ (s.card : ℝ) := (ENNReal.rpow_natCast p s.card).symm
        _ ≤ p ^ ((n : ℝ) / 2) := ENNReal.rpow_le_rpow_of_exponent_ge hp hs
    · simp only [E, hs, ite_false, measure_empty]
      exact bot_le
  calc
    (Measure.pi (fun _ : Fin n => μ)) (halfHitEvent n A)
        ≤ (Measure.pi (fun _ : Fin n => μ)) (⋃ s, E s) := measure_mono hsubset
    _ ≤ ∑ s, (Measure.pi (fun _ : Fin n => μ)) (E s) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _s : Finset (Fin n), p ^ ((n : ℝ) / 2) := Finset.sum_le_sum (fun s _ => hE s)
    _ = (2 : ℝ≥0∞) ^ n * p ^ ((n : ℝ) / 2) := by simp

/-- Union bound over all subsets of an `M`-element family. `admissible` records
any deterministic restriction, such as the total area of heavy cells. -/
theorem iid_family_half_hits_le (μ : Measure α) [IsProbabilityMeasure μ]
    (n M : ℕ) (A : Finset (Fin M) → Set α) (admissible : Finset (Fin M) → Prop)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hA : ∀ s, admissible s → μ (A s) ≤ p) :
    (Measure.pi (fun _ : Fin n => μ))
      {x | ∃ s, admissible s ∧ x ∈ halfHitEvent n (A s)} ≤
      (2 : ℝ≥0∞) ^ (M + n) * p ^ ((n : ℝ) / 2) := by
  classical
  let E (s : Finset (Fin M)) : Set (Fin n → α) :=
    if admissible s then halfHitEvent n (A s) else ∅
  have hsubset : {x | ∃ s, admissible s ∧ x ∈ halfHitEvent n (A s)} ⊆ ⋃ s, E s := by
    rintro x ⟨s, hs, hx⟩
    exact Set.mem_iUnion.mpr ⟨s, by simpa only [E, hs, ite_true] using hx⟩
  have hE (s : Finset (Fin M)) :
      (Measure.pi (fun _ : Fin n => μ)) (E s) ≤ (2 : ℝ≥0∞) ^ n * p ^ ((n : ℝ) / 2) := by
    by_cases hs : admissible s
    · simpa only [E, hs, ite_true] using iid_half_hits_le μ n (A s) p (hA s hs) hp
    · simp only [E, hs, ite_false, measure_empty]
      exact bot_le
  calc
    (Measure.pi (fun _ : Fin n => μ)) _ ≤ (Measure.pi (fun _ : Fin n => μ)) (⋃ s, E s) :=
      measure_mono hsubset
    _ ≤ ∑ s, (Measure.pi (fun _ : Fin n => μ)) (E s) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _s : Finset (Fin M), (2 : ℝ≥0∞) ^ n * p ^ ((n : ℝ) / 2) :=
      Finset.sum_le_sum (fun s _ => hE s)
    _ = (2 : ℝ≥0∞) ^ (M + n) * p ^ ((n : ℝ) / 2) := by simp [pow_add, mul_assoc]

/-- Occupancy of one cell in an arbitrary deterministic sample. -/
def cellCount {n M : ℕ} (cell : α → Fin M) (x : Fin n → α) (j : Fin M) : ℕ :=
  (Finset.univ.filter (fun i => cell (x i) = j)).card

noncomputable def heavyCells {n M : ℕ} (cell : α → Fin M) (x : Fin n → α)
    (C lam : ℝ) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter (fun j => C * lam < (cellCount cell x j : ℝ))

omit [MeasurableSpace α] in
lemma sum_cellCount {n M : ℕ} (cell : α → Fin M) (x : Fin n → α) :
    ∑ j, cellCount cell x j = n := by
  simpa [cellCount] using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin M)) (fun i => cell (x i))

omit [MeasurableSpace α] in
/-- Deterministic counting: each heavy cell consumes more than `C * lam` points. -/
theorem heavy_count_bound {n M : ℕ} (cell : α → Fin M) (x : Fin n → α) (C lam : ℝ) :
    ((heavyCells cell x C lam).card : ℝ) * C * lam ≤ n := by
  classical
  let H := heavyCells cell x C lam
  calc
    (H.card : ℝ) * C * lam = ∑ _j ∈ H, C * lam := by simp; ring
    _ ≤ ∑ j ∈ H, (cellCount cell x j : ℝ) := Finset.sum_le_sum (fun j hj =>
      le_of_lt (Finset.mem_filter.mp hj).2)
    _ ≤ ∑ j, (cellCount cell x j : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H) (fun j _ _ => Nat.cast_nonneg _)
    _ = n := by exact_mod_cast sum_cellCount cell x

omit [MeasurableSpace α] in
/-- When `n = M * lam`, the heavy cells occupy at most a `1/C` fraction of the grid. -/
theorem heavy_fraction_bound {n M : ℕ} (cell : α → Fin M) (x : Fin n → α)
    (C lam : ℝ) (hC : 0 < C) (hlam : 0 < lam) (hM : 0 < M)
    (hn : (n : ℝ) = M * lam) :
    ((heavyCells cell x C lam).card : ℝ) / M ≤ 1 / C := by
  have hh := heavy_count_bound cell x C lam
  rw [hn] at hh
  have hMc : (0 : ℝ) < M := by exact_mod_cast hM
  apply (div_le_div_iff₀ hMc hC).mpr
  have ht : ((heavyCells cell x C lam).card : ℝ) * C ≤ M := by
    nlinarith
  simpa using ht

/-- Region obtained from a selected set of cells. -/
def cellRegion {M : ℕ} (cell : α → Fin M) (s : Finset (Fin M)) : Set α :=
  {z | cell z ∈ s}

lemma cellRegion_measure_le (μ : Measure α) (M : ℕ) (cell : α → Fin M)
    (s : Finset (Fin M)) (q : ℝ≥0∞) (hcells : ∀ j, μ {z | cell z = j} ≤ q) :
    μ (cellRegion cell s) ≤ (s.card : ℝ≥0∞) * q := by
  classical
  have hsub : cellRegion cell s ⊆ ⋃ j ∈ s, {z | cell z = j} := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨cell z, Set.mem_iUnion.mpr ⟨hz, rfl⟩⟩
  calc
    μ (cellRegion cell s) ≤ μ (⋃ j ∈ s, {z | cell z = j}) := measure_mono hsub
    _ ≤ ∑ j ∈ s, μ {z | cell z = j} := measure_biUnion_finset_le s _
    _ ≤ ∑ _j ∈ s, q := Finset.sum_le_sum (fun j _ => hcells j)
    _ = (s.card : ℝ≥0∞) * q := by simp

lemma cells_and_bad_mass_le (μ : Measure α) (M : ℕ) (cell : α → Fin M)
    (bad : Set α) (C : ℝ) (hC : 0 < C) (s : Finset (Fin M))
    (hs : (s.card : ℝ) / M ≤ 1 / C)
    (hcells : ∀ j, μ {z | cell z = j} ≤ ENNReal.ofReal (1 / (M : ℝ)))
    (hbad : μ bad ≤ ENNReal.ofReal (4 / C)) :
    μ (cellRegion cell s ∪ bad) ≤ ENNReal.ofReal (5 / C) := by
  have hreg := cellRegion_measure_le μ M cell s (ENNReal.ofReal (1 / (M : ℝ))) hcells
  have hreg' : μ (cellRegion cell s) ≤ ENNReal.ofReal (1 / C) := by
    calc
      μ (cellRegion cell s) ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal (1 / (M : ℝ)) := hreg
      _ = ENNReal.ofReal ((s.card : ℝ) / M) := by
        symm
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
      _ ≤ ENNReal.ofReal (1 / C) := ENNReal.ofReal_le_ofReal hs
  calc
    μ (cellRegion cell s ∪ bad) ≤ μ (cellRegion cell s) + μ bad := measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / C) + ENNReal.ofReal (4 / C) := add_le_add hreg' hbad
    _ = ENNReal.ofReal (5 / C) := by
      rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1 / C) (by positivity : (0 : ℝ) ≤ 4 / C)]
      congr 1
      ring

/-- Number of points in nonheavy cells and outside the bad bands. -/
noncomputable def goodCount {n M : ℕ} (cell : α → Fin M) (x : Fin n → α)
    (C lam : ℝ) (bad : Set α) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i =>
    (cellCount cell x (cell (x i)) : ℝ) ≤ C * lam ∧ x i ∉ bad)).card

omit [MeasurableSpace α] in
lemma bad_hits_add_goodCount {n M : ℕ} (cell : α → Fin M) (x : Fin n → α)
    (C lam : ℝ) (bad : Set α) :
    hitCount (cellRegion cell (heavyCells cell x C lam) ∪ bad) x +
      goodCount cell x C lam bad = n := by
  classical
  have hh := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : Fin n => x i ∈ cellRegion cell (heavyCells cell x C lam) ∪ bad)
  simpa [hitCount, goodCount, cellRegion, heavyCells, not_or, not_lt] using hh

/-- Failure of the one-shape event `G_j` from the manuscript. -/
def badOccupancyEvent (n M : ℕ) (cell : α → Fin M) (C lam : ℝ) (bad : Set α) :
    Set (Fin n → α) := {x | (goodCount cell x C lam bad : ℝ) < (n : ℝ) / 2}

/-- The one-shape failure estimate, for any equal-mass partition and a bad set
of mass at most `4/C`. Both sample-dependent heavy-cell counting and the iid
probability bound are proved, rather than assumed as probabilistic hypotheses. -/
theorem bad_occupancy_le (μ : Measure α) [IsProbabilityMeasure μ]
    (n M : ℕ) (cell : α → Fin M) (bad : Set α) (C lam : ℝ)
    (hC : 20 < C) (hlam : 0 < lam) (hM : 0 < M) (hn : (n : ℝ) = M * lam)
    (hcells : ∀ j, μ {z | cell z = j} ≤ ENNReal.ofReal (1 / (M : ℝ)))
    (hbad : μ bad ≤ ENNReal.ofReal (4 / C)) :
    (Measure.pi (fun _ : Fin n => μ)) (badOccupancyEvent n M cell C lam bad) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (M + n) * (5 / C) ^ ((n : ℝ) / 2)) := by
  have hCpos : 0 < C := by linarith
  have hsubset : badOccupancyEvent n M cell C lam bad ⊆
      {x | ∃ s, (s.card : ℝ) / M ≤ 1 / C ∧
        x ∈ halfHitEvent n (cellRegion cell s ∪ bad)} := by
    intro x hx
    refine ⟨heavyCells cell x C lam, heavy_fraction_bound cell x C lam hCpos hlam hM hn, ?_⟩
    have hh := bad_hits_add_goodCount cell x C lam bad
    have hh' : (hitCount (cellRegion cell (heavyCells cell x C lam) ∪ bad) x : ℝ) +
        (goodCount cell x C lam bad : ℝ) = n := by exact_mod_cast hh
    change (goodCount cell x C lam bad : ℝ) < (n : ℝ) / 2 at hx
    change (n : ℝ) / 2 ≤ (hitCount (cellRegion cell (heavyCells cell x C lam) ∪ bad) x : ℝ)
    linarith
  have hp : ENNReal.ofReal (5 / C) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr ((div_le_one hCpos).mpr (by linarith))
  calc
    (Measure.pi (fun _ : Fin n => μ)) (badOccupancyEvent n M cell C lam bad)
        ≤ (Measure.pi (fun _ : Fin n => μ))
          {x | ∃ s, (s.card : ℝ) / M ≤ 1 / C ∧
            x ∈ halfHitEvent n (cellRegion cell s ∪ bad)} := measure_mono hsubset
    _ ≤ (2 : ℝ≥0∞) ^ (M + n) * (ENNReal.ofReal (5 / C)) ^ ((n : ℝ) / 2) :=
      iid_family_half_hits_le μ n M (fun s => cellRegion cell s ∪ bad)
        (fun s => (s.card : ℝ) / M ≤ 1 / C) (ENNReal.ofReal (5 / C)) hp
        (fun s hs => cells_and_bad_mass_le μ M cell bad C hCpos s hs hcells hbad)
    _ = ENNReal.ofReal ((2 : ℝ) ^ (M + n) * (5 / C) ^ ((n : ℝ) / 2)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ 5 / C) (by positivity)]
      norm_num

/-- The occupancy contribution over all `h` shapes, matching the manuscript. -/
theorem all_shapes_bad_occupancy_le (μ : Measure α) [IsProbabilityMeasure μ]
    (n M h : ℕ) (cell : Fin h → α → Fin M) (bad : Fin h → Set α) (C lam : ℝ)
    (hC : 20 < C) (hlam : 0 < lam) (hM : 0 < M) (hn : (n : ℝ) = M * lam)
    (hcells : ∀ j k, μ {z | cell j z = k} ≤ ENNReal.ofReal (1 / (M : ℝ)))
    (hbad : ∀ j, μ (bad j) ≤ ENNReal.ofReal (4 / C)) :
    (Measure.pi (fun _ : Fin n => μ))
      (⋃ j, badOccupancyEvent n M (cell j) C lam (bad j)) ≤
      ENNReal.ofReal ((h : ℝ) * 2 ^ (M + n) * (5 / C) ^ ((n : ℝ) / 2)) := by
  calc
    (Measure.pi (fun _ : Fin n => μ)) (⋃ j, badOccupancyEvent n M (cell j) C lam (bad j))
        ≤ ∑ j, (Measure.pi (fun _ : Fin n => μ))
          (badOccupancyEvent n M (cell j) C lam (bad j)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin h, ENNReal.ofReal ((2 : ℝ) ^ (M + n) * (5 / C) ^ ((n : ℝ) / 2)) :=
      Finset.sum_le_sum (fun j _ => bad_occupancy_le μ n M (cell j) (bad j) C lam
        hC hlam hM hn (hcells j) (hbad j))
    _ = ENNReal.ofReal ((h : ℝ) * 2 ^ (M + n) * (5 / C) ^ ((n : ℝ) / 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

open PointSets

/-- A finite cell index for the actual uniform interval partition. The choice
outside `(0,1]` is immaterial because that set is null under `μI`. -/
noncomputable def finiteGridIndex (m : ℕ) (hm : 0 < m) (x : ℝ) : Fin m :=
  if hx : x ∈ Set.Ioc (0 : ℝ) 1 then
    ⟨(gridIndex m x).toNat, by
      obtain ⟨hk, hk'⟩ := gridIndex_bounds m hm hx
      have hk0 : (0 : ℤ) ≤ gridIndex m x := by exact_mod_cast hk
      have hk1 : gridIndex m x < (m : ℤ) := by
        exact_mod_cast (show (gridIndex m x : ℝ) < m by linarith)
      omega⟩
  else ⟨0, hm⟩

lemma finiteGridIndex_eq {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ((finiteGridIndex m hm x : ℕ) : ℤ) = gridIndex m x := by
  have hk := (gridIndex_bounds m hm hx).1
  have hk0 : (0 : ℤ) ≤ gridIndex m x := by exact_mod_cast hk
  simp [finiteGridIndex, hx, Int.toNat_of_nonneg hk0]

lemma finiteGridIndex_mass (m : ℕ) (hm : 0 < m) (j : Fin m) :
    μI {x | finiteGridIndex m hm x = j} ≤ ENNReal.ofReal (1 / (m : ℝ)) := by
  have hsub : {x | finiteGridIndex m hm x = j} ⊆
      gridCell m (j : ℤ) ∪ (Set.Ioc (0 : ℝ) 1)ᶜ := by
    intro x hx
    by_cases hxunit : x ∈ Set.Ioc (0 : ℝ) 1
    · left
      have heq := finiteGridIndex_eq hm hxunit
      rw [show finiteGridIndex m hm x = j from hx] at heq
      rw [← gridIndex_fiber m hm (j : ℤ)]
      exact heq.symm
    · exact Or.inr hxunit
  calc
    μI {x | finiteGridIndex m hm x = j} ≤ μI (gridCell m (j : ℤ) ∪ (Set.Ioc (0 : ℝ) 1)ᶜ) :=
      measure_mono hsub
    _ ≤ μI (gridCell m (j : ℤ)) + μI (Set.Ioc (0 : ℝ) 1)ᶜ := measure_union_le _ _
    _ = ENNReal.ofReal (1 / (m : ℝ)) := by
      rw [μI_compl_Ioc, add_zero, gridCell_measure m hm]
      · positivity
      · exact_mod_cast j.isLt

/-- The actual `u` by `v` rectangular grid, with a finite flattened cell index. -/
noncomputable def rectangularGridIndex (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (z : ℝ × ℝ) : Fin (u * v) :=
  finProdFinEquiv (finiteGridIndex u hu z.1, finiteGridIndex v hv z.2)

lemma rectangularGridIndex_mass (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (j : Fin (u * v)) :
    (μI.prod μI) {z | rectangularGridIndex u v hu hv z = j} ≤
      ENNReal.ofReal (1 / ((u * v : ℕ) : ℝ)) := by
  have heq : {z | rectangularGridIndex u v hu hv z = j} =
      {x | finiteGridIndex u hu x = (finProdFinEquiv.symm j).1} ×ˢ
      {y | finiteGridIndex v hv y = (finProdFinEquiv.symm j).2} := by
    ext z
    simp [rectangularGridIndex, ← Equiv.eq_symm_apply, Prod.ext_iff]
  rw [heq, Measure.prod_prod]
  calc
    μI {x | finiteGridIndex u hu x = (finProdFinEquiv.symm j).1} *
        μI {y | finiteGridIndex v hv y = (finProdFinEquiv.symm j).2}
        ≤ ENNReal.ofReal (1 / (u : ℝ)) * ENNReal.ofReal (1 / (v : ℝ)) :=
      mul_le_mul' (finiteGridIndex_mass u hu _) (finiteGridIndex_mass v hv _)
    _ = ENNReal.ofReal (1 / ((u * v : ℕ) : ℝ)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring

/-- The small-value part of the actual profile lies near its three zeros. -/
lemma profile_small_subset {x ε : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : |profile x| < ε) :
    x ∈ Set.Icc 0 ε ∪ Set.Icc (1 / 2 - ε) (1 / 2 + ε) ∪ Set.Icc (1 - ε) 1 := by
  by_cases hq : x ≤ 1 / 4
  · rw [profile_first_quarter ⟨hx.1, hq⟩] at hsmall
    exact Or.inl (Or.inl ⟨hx.1, (abs_lt.mp hsmall).2.le⟩)
  · by_cases ht : x ≤ 3 / 4
    · rw [profile_middle_half ⟨by linarith, ht⟩] at hsmall
      obtain ⟨hl, hr⟩ := abs_lt.mp hsmall
      exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
    · rw [profile_last_quarter ⟨by linarith, hx.2⟩] at hsmall
      obtain ⟨hl, hr⟩ := abs_lt.mp hsmall
      exact Or.inr ⟨by linarith, hx.2⟩

/-- Three intervals covering the small-value bands in the `k`th cell. -/
def scaledProfileBands (m : ℕ) (k ε : ℝ) : Set ℝ :=
  Set.Icc (k / m) ((k + ε) / m) ∪
  Set.Icc ((k + 1 / 2 - ε) / m) ((k + 1 / 2 + ε) / m) ∪
  Set.Icc ((k + 1 - ε) / m) ((k + 1) / m)

lemma scaledProfileBands_volume_le (m : ℕ) (hm : 0 < m) (k ε : ℝ) (hε : 0 ≤ ε) :
    volume (scaledProfileBands m k ε) ≤ ENNReal.ofReal (4 * ε / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold scaledProfileBands
  calc
    volume (_ ∪ _ ∪ _) ≤ volume (_ ∪ _) + volume _ := measure_union_le _ _
    _ ≤ (volume (Set.Icc (k / m) ((k + ε) / m)) +
        volume (Set.Icc ((k + 1 / 2 - ε) / m) ((k + 1 / 2 + ε) / m))) +
        volume (Set.Icc ((k + 1 - ε) / m) ((k + 1) / m)) :=
      add_le_add (measure_union_le _ _) le_rfl
    _ = ENNReal.ofReal (4 * ε / m) := by
      simp only [Real.volume_Icc]
      rw [show (k + ε) / m - k / m = ε / m by ring,
        show (k + 1 / 2 + ε) / m - (k + 1 / 2 - ε) / m = 2 * ε / m by ring,
        show (k + 1) / m - (k + 1 - ε) / m = ε / m by ring]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The actual vertical bad set for the profile repeated on `m` uniform cells. -/
def periodicProfileBad (m : ℕ) (ε : ℝ) : Set ℝ :=
  {y | |profile ((m : ℝ) * y - gridIndex m y)| < ε}

lemma periodicProfileBad_mass (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) :
    μI (periodicProfileBad m ε) ≤ ENNReal.ofReal (4 * ε) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsub : periodicProfileBad m ε ⊆
      (⋃ k : Fin m, scaledProfileBands m k ε) ∪ (Set.Ioc (0 : ℝ) 1)ᶜ := by
    intro y hy
    by_cases hyunit : y ∈ Set.Ioc (0 : ℝ) 1
    · left
      let k := finiteGridIndex m hm y
      have hki : ((k : ℕ) : ℤ) = gridIndex m y := finiteGridIndex_eq hm hyunit
      have hkr : (k : ℝ) = (gridIndex m y : ℝ) := by exact_mod_cast hki
      have hycell : y ∈ gridCell m (gridIndex m y) := by
        rw [← gridIndex_fiber m hm]
        rfl
      have hz : (m : ℝ) * y - k ∈ Set.Icc (0 : ℝ) 1 := by
        rw [gridCell, Set.mem_Ioc] at hycell
        rw [div_lt_iff₀ hm', le_div_iff₀ hm'] at hycell
        constructor <;> nlinarith [hkr]
      have hzsmall : |profile ((m : ℝ) * y - k)| < ε := by simpa [periodicProfileBad, hkr] using hy
      have hb := profile_small_subset hz hzsmall
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      simp only [scaledProfileBands, Set.mem_union, Set.mem_Icc,
        div_le_iff₀ hm', le_div_iff₀ hm']
      rcases hb with (hleft | hmid) | hright
      · exact Or.inl (Or.inl ⟨by nlinarith [hleft.1], by nlinarith [hleft.2]⟩)
      · exact Or.inl (Or.inr ⟨by nlinarith [hmid.1], by nlinarith [hmid.2]⟩)
      · exact Or.inr ⟨by nlinarith [hright.1], by nlinarith [hright.2]⟩
    · exact Or.inr hyunit
  calc
    μI (periodicProfileBad m ε) ≤
        μI ((⋃ k : Fin m, scaledProfileBands m k ε) ∪ (Set.Ioc (0 : ℝ) 1)ᶜ) := measure_mono hsub
    _ ≤ μI (⋃ k : Fin m, scaledProfileBands m k ε) + μI (Set.Ioc (0 : ℝ) 1)ᶜ :=
      measure_union_le _ _
    _ = μI (⋃ k : Fin m, scaledProfileBands m k ε) := by rw [μI_compl_Ioc, add_zero]
    _ ≤ ∑ k : Fin m, μI (scaledProfileBands m k ε) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin m, ENNReal.ofReal (4 * ε / m) := Finset.sum_le_sum (fun k _ =>
      (Measure.restrict_le_self (scaledProfileBands m k ε)).trans
        (scaledProfileBands_volume_le m hm k ε hε))
    _ = ENNReal.ofReal (4 * ε) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

/-- The bad vertical bands of an actual rectangular grid. -/
def verticalBadBands (v : ℕ) (C : ℝ) : Set (ℝ × ℝ) :=
  Set.univ ×ˢ periodicProfileBad v (1 / C)

lemma verticalBadBands_mass (v : ℕ) (hv : 0 < v) (C : ℝ) (hC : 0 < C) :
    (μI.prod μI) (verticalBadBands v C) ≤ ENNReal.ofReal (4 / C) := by
  rw [verticalBadBands, Measure.prod_prod, measure_univ, one_mul]
  convert periodicProfileBad_mass v hv (1 / C) (by positivity) using 1
  congr 1
  ring

/-- The one-shape occupancy bound for iid uniform points of the unit square,
with actual uniform rectangular cells and the actual profile's vertical bands. -/
theorem rectangular_grid_bad_occupancy_le (n u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (C lam : ℝ) (hC : 20 < C) (hlam : 0 < lam)
    (hn : (n : ℝ) = ((u * v : ℕ) : ℝ) * lam) :
    (Measure.pi (fun _ : Fin n => μI.prod μI))
      (badOccupancyEvent n (u * v) (rectangularGridIndex u v hu hv) C lam (verticalBadBands v C)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (u * v + n) * (5 / C) ^ ((n : ℝ) / 2)) :=
  bad_occupancy_le (μI.prod μI) n (u * v) (rectangularGridIndex u v hu hv)
    (verticalBadBands v C) C lam hC hlam (Nat.mul_pos hu hv) hn
    (rectangularGridIndex_mass u v hu hv) (verticalBadBands_mass v hv C (by linarith))

/-- All shapes in the concrete two-dimensional grid. Every shape has `M` cells,
but its horizontal and vertical resolutions may differ. This proves the full
occupancy term appearing in the coefficient-sum lemma. -/
theorem grid_shapes_bad_occupancy_le (n M h : ℕ) (u v : Fin h → ℕ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j) (hM : ∀ j, u j * v j = M)
    (C lam : ℝ) (hC : 20 < C) (hlam : 0 < lam) (hn : (n : ℝ) = M * lam) :
    (Measure.pi (fun _ : Fin n => μI.prod μI))
      (⋃ j : Fin h, badOccupancyEvent n (u j * v j)
        (rectangularGridIndex (u j) (v j) (hu j) (hv j)) C lam (verticalBadBands (v j) C)) ≤
      ENNReal.ofReal ((h : ℝ) * 2 ^ (M + n) * (5 / C) ^ ((n : ℝ) / 2)) := by
  have hj (j : Fin h) :
      (Measure.pi (fun _ : Fin n => μI.prod μI))
        (badOccupancyEvent n (u j * v j)
          (rectangularGridIndex (u j) (v j) (hu j) (hv j)) C lam (verticalBadBands (v j) C)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (M + n) * (5 / C) ^ ((n : ℝ) / 2)) := by
    have heq : (n : ℝ) = ((u j * v j : ℕ) : ℝ) * lam := by rw [hM j]; exact hn
    simpa only [hM j] using rectangular_grid_bad_occupancy_le n (u j) (v j)
      (hu j) (hv j) C lam hC hlam heq
  calc
    (Measure.pi (fun _ : Fin n => μI.prod μI)) _ ≤
        ∑ j : Fin h, (Measure.pi (fun _ : Fin n => μI.prod μI))
          (badOccupancyEvent n (u j * v j)
            (rectangularGridIndex (u j) (v j) (hu j) (hv j)) C lam (verticalBadBands (v j) C)) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin h, ENNReal.ofReal ((2 : ℝ) ^ (M + n) * (5 / C) ^ ((n : ℝ) / 2)) :=
      Finset.sum_le_sum (fun j _ => hj j)
    _ = ENNReal.ofReal ((h : ℝ) * 2 ^ (M + n) * (5 / C) ^ ((n : ℝ) / 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end Riesz.Occupancy
