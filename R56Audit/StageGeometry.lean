import R56Audit.Crowding

/-!
# The partitions of Section 2.4: cells, comparison rectangles and inner regions, as sets

Auditor's supplement (not part of the audited archive).

Section 2.4, "Partitions and potential": "Fix an integer `h ≥ 1` and set `M = b^{h-1}`. At stage
`j`, `0 ≤ j ≤ h`, cut `[0,1]` horizontally into `b^j` intervals of length `b^{-j}`, and
vertically into `b^{h-j}` intervals of length `b^{j-h}`. Their products are the cells of stage
`j`. There are `b^j · b^{h-j} = bM` cells at every stage."

Section 2.4, "Transitions": "In the transition `j → j+1`, we call the objects of stage `j` old
and those of stage `j+1` new. A comparison rectangle `R = I × J` is the product of one old
horizontal interval and one new vertical interval. It is the union of `b` old cells, which are
its horizontal strips, and also of `b` new cells, which are its vertical strips, as in Figure 1.
There are `b^j` old horizontal intervals and `b^{h-j-1}` new vertical intervals, hence `M`
comparison rectangles, each of area `b^{-j} · b^{j+1-h} = 1/M`. As in Section 2.2, the inner
region of `R` is `R` without its bottom and top old cells, and `m_R` is the number of points in
it."

The other modules of the supplement give these objects by coordinates: the potential `Zpot` is
written with the two endpoints of a horizontal interval and with the vertical interval `vcell`,
and the regions `innerRegion`, `bottomStrip` and `topStrip` are products of two intervals with
explicit endpoints. This module states the two paragraphs with sets, and shows that the objects
given by coordinates are the cells, the comparison rectangles and the inner regions of the
manuscript.

| Manuscript | Here |
| --- | --- |
| `c`-th horizontal interval of stage `j`, `[c b^{-j}, (c+1) b^{-j}]` | `hcell b j c` |
| `v`-th vertical interval of stage `j`, `[v b^{j-h}, (v+1) b^{j-h})` | `vcell b h j v` |
| cell of stage `j`, the product `I × B` of two such intervals | `cell b h j c v` |
| comparison rectangle `R = I × J` of the transition `j → j+1` | `compRect b h j c v` |
| old cells of `R`, its horizontal strips `I × B_{ℓ+1}`, `ℓ < b` | `cell b h j c (b * v + ℓ)` |
| new cells of `R`, its vertical strips `C_{k+1} × J`, `k < b` | `cell b h (j + 1) (b * c + k) v` |
| boundary strips of `R`: its bottom and its top old cell | `bottomStrip`, `topStrip` |
| inner region `R^in` of `R` | `innerRegion b h j c v` |

Here `hcell`, `cell` and `compRect` are new; `vcell` is defined in `Potential.lean`,
`innerRegion` in `GoodTransitions.lean`, and `bottomStrip`, `topStrip` in `Crowding.lean`.

The objects of stage `j` are those with `c < b^j` and `v < b^{h-j}`, and the comparison
rectangles of the transition `j → j+1` are those with `c < b^j` and `v < b^{h-j-1}`. Indices
start from `0`: the block `B_{ℓ+1}` of `J` is the vertical interval `b v + ℓ` of stage `j`, and
the child `C_{k+1}` of `I` is the horizontal interval `b c + k` of stage `j+1`. The proof of
Lemma 2.4 uses that "Every old cell is a horizontal strip of exactly one comparison rectangle
`R = I × J`, and every new cell is a vertical strip of exactly one"; in the supplement this is
the reindexing of the sums in `Zstep_eq_sum_blocks` and `Zstep_succ_eq_sum_children`
(`StageGain.lean`).

Horizontal intervals are closed, `I = [I⁻, I⁺]`. "Vertical intervals are closed at the bottom
and open at the top" (Section 2.1). So the vertical intervals of a stage are disjoint, two
neighbouring horizontal intervals share an endpoint, and the cells of a stage cover
`[0,1] × [0,1)`, the unit square without its top edge. On the probability-one event of Section
2.1 no point lies on a common side of two cells or on the top edge (`NoGrid`).

The manuscript has `b ≥ 3`. The statements below assume only `b ≥ 1` (and
`innerRegion_eq_iUnion` is stated for `b ≥ 2`).

* `iUnion_hcell`, `volume_hcell`, `iUnion_vcell`, `volume_vcell`, `vcell_disjoint`: the `b^j`
  horizontal intervals of stage `j` have length `b^{-j}` and cover `[0,1]`; the `b^{h-j}`
  vertical intervals have length `b^{j-h}` and partition `[0,1)`.
* `hcell_eq_iUnion_children`, `vcell_succ_eq_iUnion`: a horizontal interval of stage `j` is the
  union of its `b` children, and a vertical interval of stage `j+1` is the union of its `b`
  blocks.
* `iUnion_cell`, `card_cells_stage`, `volume_cell`: the cells of stage `j` cover
  `[0,1] × [0,1)`; there are `b^h = bM` of them, each of area `b^{-h} = 1/(bM)`.
* `compRect_eq_iUnion_old`, `compRect_eq_iUnion_new`, `volume_compRect`: a comparison rectangle
  is the union of `b` old cells and also of `b` new cells, and it has area `1/M`. (There are
  `M` comparison rectangles: `card_compRect` in `Crowding.lean`.)
* `bottomStrip_eq_cell`, `topStrip_eq_cell`, `innerRegion_eq_diff`, `innerRegion_eq_iUnion`:
  the boundary strips of `R` are its bottom and its top old cell, and `R^in` is `R` without
  these two cells, the union of the other old cells of `R`.
* `Zpot_eq_sum_cells`: the potential of display (1) is the sum over the cells of stage `j`.
* `figure_1_cells`, `figure_1_shaded`, `figure_1_compRects`: the numbers and the shaded
  rectangle of Figure 1.
-/

namespace R56Audit

open MeasureTheory Riesz Oscillation

noncomputable section

variable {n : ℕ}

/-! ### Cells and comparison rectangles -/

/-- The `c`-th horizontal interval of stage `j`: `I = [c b^{-j}, (c+1) b^{-j}]`, the closed
interval with the endpoints `I⁻ = c b^{-j}` and `I⁺ = (c+1) b^{-j}`. The horizontal intervals of
stage `j` are those with `c < b^j`. -/
def hcell (b j c : ℕ) : Set ℝ :=
  Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j)

/-- The cell of stage `j` with indices `(c, v)`: the product of the `c`-th horizontal and the
`v`-th vertical interval of stage `j`. "Their products are the cells of stage `j`." The cells of
stage `j` are those with `c < b^j` and `v < b^{h-j}`. -/
def cell (b h j c v : ℕ) : Set (ℝ × ℝ) := hcell b j c ×ˢ vcell b h j v

/-- The comparison rectangle `R = I × J` of the transition `j → j+1` with indices `(c, v)`:
"the product of one old horizontal interval and one new vertical interval", that is, of the
`c`-th horizontal interval of stage `j` and the `v`-th vertical interval of stage `j+1`. The
comparison rectangles of the transition are those with `c < b^j` and `v < b^{h-j-1}`. -/
def compRect (b h j c v : ℕ) : Set (ℝ × ℝ) := hcell b j c ×ˢ vcell b h (j + 1) v

/-! ### The horizontal and the vertical intervals of a stage -/

/-- A number `x` lies in the `c`-th horizontal interval of stage `j` exactly when
`c ≤ b^j x ≤ c + 1`. -/
lemma mem_hcell {b : ℕ} (hb : 0 < b) {j c : ℕ} {x : ℝ} :
    x ∈ hcell b j c ↔ (c : ℝ) ≤ (b : ℝ) ^ j * x ∧ (b : ℝ) ^ j * x ≤ (c : ℝ) + 1 := by
  have hpj : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  rw [hcell, Set.mem_Icc, div_le_iff₀ hpj, le_div_iff₀ hpj, mul_comm x]

/-- The horizontal intervals of stage `j` lie in `[0, 1]`. -/
lemma hcell_subset_unit {b j c : ℕ} (hb : 0 < b) (hc : c < b ^ j) :
    hcell b j c ⊆ Set.Icc (0 : ℝ) 1 := by
  have hpj : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  have hc1 : (c : ℝ) + 1 ≤ (b : ℝ) ^ j := by exact_mod_cast hc
  rintro x ⟨h1, h2⟩
  exact ⟨le_trans (by positivity) h1, h2.trans ((div_le_one hpj).mpr hc1)⟩

/-- "\[…\] cut `[0,1]` horizontally into `b^j` intervals of length `b^{-j}`": the union of the
`b^j` horizontal intervals of stage `j` is `[0, 1]`. (The intervals are closed, so two
neighbouring ones share an endpoint.) -/
theorem iUnion_hcell {b : ℕ} (hb : 0 < b) (j : ℕ) :
    ⋃ c : Fin (b ^ j), hcell b j c = Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun c => hcell_subset_unit hb c.isLt
  · -- every `x ∈ [0, 1]` lies in one of the intervals (`exists_hcell`)
    intro x hx
    obtain ⟨c, hc, hxc⟩ := exists_hcell hb j hx
    exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hxc⟩

/-- "\[…\] `b^j` intervals of length `b^{-j}`": a horizontal interval of stage `j` has length
`b^{-j}`. -/
theorem volume_hcell {b : ℕ} (hb : 0 < b) (j c : ℕ) :
    volume (hcell b j c) = ENNReal.ofReal (1 / (b : ℝ) ^ j) := by
  rw [hcell, Real.volume_Icc]
  congr 1
  field_simp
  ring

/-- "\[…\] and vertically into `b^{h-j}` intervals of length `b^{j-h}`": the union of the
`b^{h-j}` vertical intervals of stage `j` is `[0, 1)`. "Vertical intervals are closed at the
bottom and open at the top" (Section 2.1), so the height `1` lies in none of them. -/
theorem iUnion_vcell {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) :
    ⋃ v : Fin (b ^ (h - j)), vcell b h j v = Set.Ico (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun v => vcell_subset_unit hb hj v.isLt
  · -- every height in `[0, 1)` lies in one of the intervals (`exists_vcell`)
    intro y hy
    obtain ⟨w, hw, hyw⟩ := exists_vcell hb hj hy
    exact Set.mem_iUnion.mpr ⟨⟨w, hw⟩, hyw⟩

/-- "\[…\] `b^{h-j}` intervals of length `b^{j-h}`": a vertical interval of stage `j` has length
`b^{j-h}`, the number `vlen b h j`. -/
theorem volume_vcell {b : ℕ} (hb : 0 < b) (h j v : ℕ) :
    volume (vcell b h j v) = ENNReal.ofReal ((b : ℝ) ^ j / (b : ℝ) ^ h) := by
  rw [vcell, Real.volume_Ico, vlen]
  congr 1
  field_simp
  ring

/-- Two different vertical intervals of a stage are disjoint: "Vertical intervals are closed at
the bottom and open at the top" (Section 2.1). -/
theorem vcell_disjoint {b : ℕ} (hb : 0 < b) (h j : ℕ) {v v' : ℕ} (hv : v ≠ v') :
    Disjoint (vcell b h j v) (vcell b h j v') := by
  -- the vertical intervals of stage `j` are the blocks of length `b^{j-h}` that start at `0`
  have e : ∀ w : ℕ, vcell b h j w = block 0 (vlen b h j) w := by
    intro w
    unfold vcell block
    rw [zero_add, zero_add]
  rw [e v, e v']
  exact block_disjoint 0 (vlen_pos hb h j) hv

/-! ### Children and blocks -/

/-- "Now partition `I` into children `C_1, …, C_b` of equal length, from left to right"
(Section 2.3): the `c`-th horizontal interval of stage `j` is the union of the `b` horizontal
intervals `b c, …, b c + b - 1` of stage `j+1`. The interval `b c + k` is the child
`C_{k+1}`. -/
theorem hcell_eq_iUnion_children {b : ℕ} (hb : 0 < b) (j c : ℕ) :
    hcell b j c = ⋃ k : Fin b, hcell b (j + 1) (b * c + k) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  ext x
  simp only [Set.mem_iUnion, mem_hcell hb, pow_succ, Nat.cast_add, Nat.cast_mul]
  constructor
  · rintro ⟨h1, h2⟩
    -- the position `b^j x - c ∈ [0, 1]` of `x` in `I` lies in an interval `[k/b, (k+1)/b]`
    obtain ⟨k, hk, hk1, hk2⟩ := exists_hcell hb 1 (x := (b : ℝ) ^ j * x - c)
      ⟨by linarith, by linarith⟩
    rw [pow_one] at hk hk1 hk2
    rw [div_le_iff₀ hbR] at hk1
    rw [le_div_iff₀ hbR] at hk2
    exact ⟨⟨k, hk⟩, by linarith, by linarith⟩
  · rintro ⟨k, h1, h2⟩
    -- a child of `I` lies in `I`, since `0 ≤ k` and `k + 1 ≤ b`
    have hk1 : ((k : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast k.isLt
    exact ⟨le_of_mul_le_mul_left (by linarith) hbR, le_of_mul_le_mul_left (by linarith) hbR⟩

/-- "Partition `J` into blocks `B_1, …, B_b` of equal length, from bottom to top"
(Section 2.2): the `v`-th vertical interval of stage `j+1` is the union of the `b` vertical
intervals `b v, …, b v + b - 1` of stage `j`. The interval `b v + ℓ` is the block `B_{ℓ+1}`
(`vcell_eq_block`). -/
theorem vcell_succ_eq_iUnion {b : ℕ} (hb : 0 < b) (h j v : ℕ) :
    vcell b h (j + 1) v = ⋃ ℓ : Fin b, vcell b h j (b * v + ℓ) := by
  rw [vcell_succ_eq, ← iUnion_block _ (vlen_pos hb h j) b]
  exact Set.iUnion_congr fun ℓ => (vcell_eq_block b h j v ℓ).symm

/-! ### The cells of a stage -/

/-- "Their products are the cells of stage `j`": the cells of stage `j` cover `[0,1] × [0,1)`,
the unit square without its top edge. -/
theorem iUnion_cell {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) :
    ⋃ c : Fin (b ^ j), ⋃ v : Fin (b ^ (h - j)), cell b h j c v =
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1 := by
  -- the union of the products is the product of the unions
  rw [← iUnion_hcell hb j, ← iUnion_vcell hb hj, Set.iUnion_prod_const]
  exact Set.iUnion_congr fun c => Set.prod_iUnion.symm

/-- "There are `b^j · b^{h-j} = bM` cells at every stage": the cells of stage `j` are indexed by
the pairs `(c, v)` with `c < b^j` and `v < b^{h-j}`, and there are `b^h` such pairs. (`b^h = bM`
for `h ≥ 1`, see `pow_eq_mul_pow_pred`.) -/
theorem card_cells_stage {b h j : ℕ} (hj : j ≤ h) :
    Fintype.card (Fin (b ^ j) × Fin (b ^ (h - j))) = b ^ h := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← pow_add, Nat.add_sub_cancel' hj]

/-- A cell of stage `j` has area `b^{-j} · b^{j-h} = b^{-h} = 1/(bM)`. Section 1: "\[…\] the
unit square is partitioned into cells of width `b^{-j}` and height `b^{j-h}`". -/
theorem volume_cell {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    volume (cell b h j c v) = ENNReal.ofReal (1 / (b : ℝ) ^ h) := by
  -- the area of a product is the product of the lengths
  rw [cell, Measure.volume_eq_prod, Measure.prod_prod, volume_hcell hb, volume_vcell hb,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### Comparison rectangles -/

/-- "It is the union of `b` old cells, which are its horizontal strips \[…\]": the comparison
rectangle `(c, v)` is the union of the cells `(c, b v + ℓ)`, `ℓ < b`, of stage `j`. They are
"the horizontal strips `I × B_ℓ`" of Section 2.2. -/
theorem compRect_eq_iUnion_old {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    compRect b h j c v = ⋃ ℓ : Fin b, cell b h j c (b * v + ℓ) := by
  unfold compRect cell
  -- `J` is the union of its blocks
  rw [vcell_succ_eq_iUnion hb h j v, Set.prod_iUnion]

/-- "\[…\] and also of `b` new cells, which are its vertical strips": the comparison rectangle
`(c, v)` is the union of the cells `(b c + k, v)`, `k < b`, of stage `j+1`. They are "the
vertical strips `C_k × J`" of Section 2.3. -/
theorem compRect_eq_iUnion_new {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    compRect b h j c v = ⋃ k : Fin b, cell b h (j + 1) (b * c + k) v := by
  unfold compRect cell
  -- `I` is the union of its children
  rw [hcell_eq_iUnion_children hb j c, Set.iUnion_prod_const]

/-- "\[…\] hence `M` comparison rectangles, each of area `b^{-j} · b^{j+1-h} = 1/M`", where
`M = b^{h-1}`. (There are `M` comparison rectangles: `card_compRect`.) -/
theorem volume_compRect {b h j : ℕ} (hb : 0 < b) (hj : j < h) (c v : ℕ) :
    volume (compRect b h j c v) = ENNReal.ofReal (1 / (b : ℝ) ^ (h - 1)) := by
  -- the area of a product is the product of the lengths
  rw [compRect, Measure.volume_eq_prod, Measure.prod_prod, volume_hcell hb, volume_vcell hb,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  -- `b^{-j} · b^{j+1} / b^h = b / (b M) = 1 / M`
  rw [pow_eq_mul_pow_pred (by omega : 0 < h), pow_succ]
  field_simp

/-! ### Boundary strips and inner regions -/

/-- "\[…\] a boundary strip, by which we mean the bottom or the top old cell of a comparison
rectangle": the bottom strip of the comparison rectangle `(c, v)` is the cell `(c, b v)` of
stage `j`, its bottom old cell `I × B_1`. -/
theorem bottomStrip_eq_cell (b h j c v : ℕ) : bottomStrip b h j c v = cell b h j c (b * v) :=
  bottomStrip_eq b h j c v

/-- "\[…\] a boundary strip, by which we mean the bottom or the top old cell of a comparison
rectangle": the top strip of the comparison rectangle `(c, v)` is the cell `(c, b v + b - 1)`
of stage `j`, its top old cell `I × B_b`. -/
theorem topStrip_eq_cell {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    topStrip b h j c v = cell b h j c (b * v + (b - 1)) :=
  topStrip_eq hb h j c v

/-- The vertical interval `J = [s, s + b L)` without its bottom block `B_1 = [s, s + L)` and
its top block `B_b = [s + (b - 1) L, s + b L)` is `[s + L, s + (b - 1) L)`. -/
lemma Ico_sdiff_bottom_top_block (s : ℝ) {L : ℝ} (hL : 0 ≤ L) {b : ℕ} (hb : 0 < b) :
    Set.Ico s (s + b * L) \ (block s L 0 ∪ block s L (b - 1)) =
      Set.Ico (s + L) (s + ((b : ℝ) - 1) * L) := by
  ext y
  simp only [block, Set.mem_sdiff, Set.mem_union, Set.mem_Ico, not_or, not_and, not_lt,
    Nat.cast_pred hb, Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul, sub_add_cancel]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h3 h1, lt_of_not_ge fun hy => (h4 hy).not_gt h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith, by linarith⟩, fun _ => h1, fun hy => absurd h2 hy.not_gt⟩

/-- "\[…\] the inner region of `R` is `R` without its bottom and top old cells": the region
`innerRegion b h j c v`, which is defined by the endpoints of its two intervals, is the
comparison rectangle `(c, v)` without its bottom old cell `(c, b v)` and its top old cell
`(c, b v + b - 1)`. -/
theorem innerRegion_eq_diff {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    innerRegion b h j c v =
      compRect b h j c v \ (cell b h j c (b * v) ∪ cell b h j c (b * v + (b - 1))) := by
  -- the vertical interval `b v` of stage `j` is the bottom block `B_1` of `J`
  have hB1 : vcell b h j (b * v) = block ((v : ℝ) * vlen b h (j + 1)) (vlen b h j) 0 :=
    vcell_eq_block b h j v 0
  -- `R` without the two old cells `I × B_1` and `I × B_b` is `I × (J \ (B_1 ∪ B_b))`
  rw [compRect, cell, cell, ← Set.prod_union, Set.prod_sdiff_prod, Set.sdiff_self,
    Set.empty_prod, Set.union_empty, vcell_succ_eq, hB1, vcell_eq_block,
    Ico_sdiff_bottom_top_block _ (vlen_pos hb h j).le hb]
  -- the heights of `R^in` are `[s + L, s + (b - 1) L)`, with `s = v b^{j+1-h}` and `L = b^{j-h}`
  unfold innerRegion hcell vlen
  congr 2 <;> ring

/-- "`R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})`" (Section 2.2): the inner region of the comparison
rectangle `(c, v)` is the union of its old cells other than the bottom and the top one, that
is, of the cells `(c, b v + ℓ)` of stage `j` with `1 ≤ ℓ ≤ b - 2`. -/
theorem innerRegion_eq_iUnion {b : ℕ} (hb : 2 ≤ b) (h j c v : ℕ) :
    innerRegion b h j c v = ⋃ ℓ ∈ Finset.Ico 1 (b - 1), cell b h j c (b * v + ℓ) := by
  have hb0 : 0 < b := by omega
  apply Set.Subset.antisymm
  · -- a point of `R^in` lies in an old cell of `R` that is not the bottom or the top one
    intro z hz
    rw [innerRegion_eq_diff hb0, compRect_eq_iUnion_old hb0] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨ℓ, hℓ⟩ := Set.mem_iUnion.mp hz1
    have hlt := ℓ.isLt
    have h0 : (ℓ : ℕ) ≠ 0 := fun h0 => hz2 (Or.inl (by rwa [h0, add_zero] at hℓ))
    have h1 : (ℓ : ℕ) ≠ b - 1 := fun h1 => hz2 (Or.inr (by rwa [h1] at hℓ))
    exact Set.mem_biUnion (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) hℓ
  · -- the other old cells of `R` lie in `R^in` (`prod_vcell_subset_innerRegion`)
    refine Set.iUnion₂_subset fun ℓ hℓ => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hℓ
    exact prod_vcell_subset_innerRegion hb0 h j c v h1 (by omega)

/-! ### The potential -/

/-- "As in (1), the potential is `Z_j = (1 / (bM)) Σ_{stage-j cells I × B} osc_B a^{(I)}`": the
potential `Zpot` is a sum over the cells of stage `j`. The cell with indices `(c, v)` is
`I × B = cell b h j c v`, where `I = hcell b j c = [I⁻, I⁺]` has the endpoints `I⁻ = c b^{-j}`
and `I⁺ = (c+1) b^{-j}`, and `B = vcell b h j v`. Its term is the oscillation on `B` of the
endpoint average `a^{(I)} = endAvg χ P I⁻ I⁺` of `I`, which is written with the two endpoints
of `I`. The sum is divided by `b^h = bM`, the number of the cells (`card_cells_stage`). This
is the definition of `Zpot`. -/
theorem Zpot_eq_sum_cells (χ : Fin n → ℤˣ) (b h j : ℕ) (P : Fin n → ℝ × ℝ) :
    Zpot χ b h j P = (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
      osc (vcell b h j v) (endAvg χ P (((c : ℕ) : ℝ) / (b : ℝ) ^ j)
        ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j))) / (b : ℝ) ^ h :=
  rfl

/-! ### Figure 1 -/

/-- Figure 1: "The partitions, drawn for `b = 4` and `h = 2`. Every stage has `b^h = 16`
cells \[…\]." -/
theorem figure_1_cells (j : ℕ) (hj : j ≤ 2) :
    Fintype.card (Fin (4 ^ j) × Fin (4 ^ (2 - j))) = 16 := by
  rw [card_cells_stage hj]
  norm_num

/-- Figure 1: "The shaded region is one of the four comparison rectangles of the transition
`0 → 1`: a union of `b` cells of stage `0` and also of `b` cells of stage `1`." The shaded
region of the figure is `[0,1] × [1/4, 1/2)`, the comparison rectangle with indices `(0, 1)`;
`compRect_eq_iUnion_old` and `compRect_eq_iUnion_new` give the two unions. -/
theorem figure_1_shaded :
    compRect 4 2 0 0 1 = Set.Icc (0 : ℝ) 1 ×ˢ Set.Ico (1 / 4 : ℝ) (1 / 2) := by
  unfold compRect hcell vcell vlen
  norm_num

/-- Figure 1: "\[…\] one of the four comparison rectangles of the transition `0 → 1`": for
`b = 4` and `h = 2`, the transition `0 → 1` has four comparison rectangles. -/
theorem figure_1_compRects : Fintype.card (Fin (4 ^ 0) × Fin (4 ^ (2 - 0 - 1))) = 4 := by
  rw [card_compRect (show 0 < 2 by norm_num)]
  norm_num

end

end R56Audit
