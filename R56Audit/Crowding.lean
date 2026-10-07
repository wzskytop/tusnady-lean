import R56Audit.GoodTransitions
import R56Audit.Potential

/-!
# Lemma 2.5(ii) of the manuscript (good transitions), by the proof of the manuscript

Auditor's supplement (not part of the audited archive).

**Lemma 2.5(ii).** If `M ≤ n`, then `Pr(G_j^c) ≤ (48/b)^{n/2}`, and hence
`Pr(G^c) ≤ h (48/b)^{n/2}`.

`lemma_2_5_ii` and `lemma_2_5_ii_all` are these two bounds, proved by the proof in
Section 2.4 of the manuscript. The archive's probability estimate and its cell labels are not
used (`GoodTransitionsArchive.lean` shows that they give the same bounds). The regions, the
numbers `m_R`, "heavy", the events `G_j`, and the almost sure events `InUnit` (all coordinates
in `(0,1]`) and `NoGrid` (no coordinate of the form `k/b^r`) are those of
`GoodTransitions.lean`; the old vertical intervals are `vcell` of `Potential.lean`; the law of
the points is `unifPts`.

Throughout, `M = b^{h-1}`, and the comparison rectangles of the transition `j → j+1` are
indexed by the pairs `(c, v)`, `c < b^j`, `v < b^{h-j-1}`.

| Manuscript | Here |
| --- | --- |
| boundary strip: "the bottom or the top old cell" | `bottomStrip`, `topStrip` |
| the union of the boundary strips | `boundaryStrips b h j` |
| a collection `𝒮` of inner regions | `𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))` |
| "fewer than `M/b`" regions | `(𝒮.card : ℝ) < b ^ (h - 1) / b`, `smallCollections` |
| `W_𝒮`: "the union of the boundary strips and of the regions in `𝒮`" | `Wset b h j 𝒮` |
| the collection of the heavy regions | `heavySet b h j P` |
| "the union `W` of the boundary strips and the heavy regions" | `Wset b h j (heavySet b h j P)` |
| `E_𝒮`: "the event that at least `n/2` points lie in `W_𝒮`" | `crowdEvent b h j 𝒮` |

The steps of the proof of the manuscript, with its sentences. (The manuscript proves step 3
before step 2, and the first half of step 6 before step 4.)

1. *The boundary strips and `W_𝒮`.* `bottomStrip_eq`, `topStrip_eq`,
   `prod_vcell_subset_innerRegion`: of the `b` old cells of a comparison rectangle, the
   bottom and the top one are its boundary strips, and the others lie in its inner region.
2. `innerRegion_inj`, `sum_innerCount_le`, `card_heavySet_lt`: "There are fewer than `M/b`
   heavy regions, since no point lies in two inner regions and each heavy one contains more
   than `bn/M` of the `n` points."
3. `mem_boundaryStrips_or_innerRegion`, `mem_Wset_heavySet`, `half_lt_card_Wset`: "Suppose
   that `G_j` fails, that is, fewer than `n/2` points lie in inner regions that are not
   heavy. Every other point lies in a heavy inner region or in a boundary strip \[…\]. So
   more than `n/2` points lie in the union `W` of the boundary strips and the heavy regions."
4. `volume_boundaryStrips`, `volume_innerRegion_lt`, `volume_innerRegions_lt`,
   `volume_Wset_le`, `unitSq_Wset_le`: "The boundary strips are two of the `b` old cells of
   every comparison rectangle, so they cover an area of `2/b`. The regions in `𝒮` have area
   less than `1/M` each, so they cover an area of less than `1/b`. Hence `W_𝒮` is a fixed set
   of area at most `3/b`." The first sentence is the equality `volume_boundaryStrips`, for
   `b ≥ 2`: the union of the boundary strips is the product of `[0,1]` and of the union of
   `2 b^{h-j-1}` disjoint vertical intervals of length `b^{j-h}` (`boundaryStrips_eq_prod`).
   The second sentence is `volume_innerRegion_lt` and the strict inequality
   `volume_innerRegions_lt`. The third sentence is `volume_Wset_le`; for the boundary strips
   it uses the upper bound `volume_boundaryStrips_le`, which holds for every `b ≥ 1` (for
   `b = 1` the two boundary strips of a comparison rectangle coincide).
   `volume_innerRegions_le` is the weak form of `volume_innerRegions_lt`.
5. `exists_card_eq_ceil_half`, `unifPts_forall_mem`, `unifPts_forall_mem_le`,
   `unifPts_half_mem_le`, `unifPts_crowdEvent_le`: "If `E_𝒮` occurs, then there is a set of
   `⌈n/2⌉` indices whose points all lie in `W_𝒮`. There are at most `2^n` sets of indices.
   The `n` points are independent and uniform in the unit square, so the points of a given
   set all lie in the fixed set `W_𝒮` with probability at most
   `(3/b)^{⌈n/2⌉} ≤ (3/b)^{n/2}`, since `3/b ≤ 1`. So `Pr(E_𝒮) ≤ 2^n (3/b)^{n/2}`."
6. `mem_crowdEvent_heavySet`, `bad_subset_iUnion_crowdEvent`, `bad_ae_le_iUnion_crowdEvent`,
   `card_smallCollections_le`, `unifPts_bad_le`, `two_pow_mul_rpow_le`: "if `G_j` fails, then
   `E_𝒮` occurs for the collection `𝒮` of heavy regions. So `G_j^c` is contained in the union
   of the events `E_𝒮`. \[…\] There are at most `2^M` collections of inner regions, so
   `Pr(G_j^c) ≤ 2^{M+n} (3/b)^{n/2}`. Since `M ≤ n`, we have `2^{M+n} ≤ 4^n = 16^{n/2}`, which
   gives `(48/b)^{n/2}`. A union bound over the `h` transitions gives the bound on
   `Pr(G^c)`."

**Where the probability-one event of Section 2.1 enters.** Steps 1, 4 and 5 do not need it.
Step 2 uses that no horizontal coordinate of a point has the form `k/b^j` (from `NoGrid`): the
horizontal intervals are closed, so two neighbouring inner regions share a vertical segment.
Step 3 uses that the points lie in `[0,1] × [0,1)`: a point of height `1` lies in no
comparison rectangle. On `InUnit` and `NoGrid` all coordinates lie in `(0,1)`
(`mem_unit_of_inUnit_of_noGrid`). So in step 6 the event `G_j^c` is contained in the union of
the events `E_𝒮` on these two events, which have probability one (`ae_inUnit`, `ae_noGrid`).

No set needs to be measurable for Lemma 2.5(ii): its proof uses only that a measure is
monotone and subadditive, and the product formula for boxes (`Measure.prod_prod`,
`Measure.pi_pi`). The equality `volume_boundaryStrips`, which the proof of the lemma does not
use, needs in addition that the length is additive on disjoint intervals (`measure_iUnion`,
`measure_union`).
-/

namespace R56Audit

open MeasureTheory Finset Riesz Riesz.PointSets Oscillation

open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ### 1. The boundary strips and the set `W_𝒮` -/

/-- The bottom old cell of the comparison rectangle `R = I × J` with indices `(c, v)` of the
transition `j → j+1`, where `I = [c b^{-j}, (c+1) b^{-j}]` and
`J = [v b^{j+1-h}, (v+1) b^{j+1-h})`: the points of `R` whose height lies in the bottom block
`[v b^{j+1-h}, v b^{j+1-h} + b^{j-h})` of `J`. -/
def bottomStrip (b h j c v : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
    Set.Ico ((v : ℝ) * (b : ℝ) ^ (j + 1) / (b : ℝ) ^ h)
      (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h)

/-- The top old cell of the comparison rectangle `R = I × J` with indices `(c, v)` of the
transition `j → j+1`: the points of `R` whose height lies in the top block
`[(v+1) b^{j+1-h} - b^{j-h}, (v+1) b^{j+1-h})` of `J`. -/
def topStrip (b h j c v : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
    Set.Ico ((((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h)
      (((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) / (b : ℝ) ^ h)

/-- The union of the boundary strips of the transition `j → j+1`. A boundary strip is "the
bottom or the top old cell of a comparison rectangle". -/
def boundaryStrips (b h j : ℕ) : Set (ℝ × ℝ) :=
  ⋃ p : Fin (b ^ j) × Fin (b ^ (h - j - 1)),
    bottomStrip b h j p.1 p.2 ∪ topStrip b h j p.1 p.2

/-- `W_𝒮`: "the union of the boundary strips and of the regions in `𝒮`", for a collection `𝒮`
of inner regions. -/
def Wset (b h j : ℕ) (𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) : Set (ℝ × ℝ) :=
  boundaryStrips b h j ∪ ⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2

/-- The collection of the heavy inner regions. With it, `Wset b h j (heavySet b h j P)` is
"the union `W` of the boundary strips and the heavy regions". -/
def heavySet (b h j : ℕ) (P : Fin n → ℝ × ℝ) : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1))) :=
  Finset.univ.filter (fun p => Heavy b h j P p.1 p.2)

/-- `E_𝒮`: "the event that at least `n/2` points lie in `W_𝒮`". -/
def crowdEvent (b h j : ℕ) (𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) :
    Set (Fin n → ℝ × ℝ) :=
  {P | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ Wset b h j 𝒮)).card}

/-- The collections `𝒮` "of fewer than `M/b` inner regions, whether or not its regions are
heavy". -/
def smallCollections (b h j : ℕ) : Finset (Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) :=
  Finset.univ.filter (fun 𝒮 => (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b)

/-- A region belongs to the collection `heavySet` exactly when it is heavy. -/
lemma mem_heavySet {b h j : ℕ} {P : Fin n → ℝ × ℝ} {p : Fin (b ^ j) × Fin (b ^ (h - j - 1))} :
    p ∈ heavySet b h j P ↔ Heavy b h j P p.1 p.2 := by
  simp [heavySet]

/-- A collection belongs to `smallCollections` exactly when it has fewer than `M/b`
regions. -/
lemma mem_smallCollections {b h j : ℕ} {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))} :
    𝒮 ∈ smallCollections b h j ↔ (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b := by
  simp [smallCollections]

/-- A point lies in `W_𝒮` exactly when it lies in a boundary strip or in a region of `𝒮`. -/
lemma mem_Wset {b h j : ℕ} {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))} {z : ℝ × ℝ} :
    z ∈ Wset b h j 𝒮 ↔
      z ∈ boundaryStrips b h j ∨ ∃ p ∈ 𝒮, z ∈ innerRegion b h j p.1 p.2 := by
  simp only [Wset, Set.mem_union, Set.mem_iUnion₂, exists_prop]

/-- "There are `b^j` old horizontal intervals and `b^{h-j-1}` new vertical intervals, hence
`M` comparison rectangles". -/
lemma card_compRect {b h j : ℕ} (hj : j < h) :
    Fintype.card (Fin (b ^ j) × Fin (b ^ (h - j - 1))) = b ^ (h - 1) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← pow_add]
  congr 1
  omega

/-- The bottom strip of the comparison rectangle `(c, v)` is an old cell: the product of the
`c`-th horizontal interval and of the vertical interval `b v` of stage `j`, which is the block
`B_1` of the `v`-th vertical interval of stage `j + 1` (`vcell_eq_block`). -/
lemma bottomStrip_eq (b h j c v : ℕ) :
    bottomStrip b h j c v =
      Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ vcell b h j (b * v) := by
  unfold bottomStrip vcell vlen
  push_cast
  congr 2 <;> ring

/-- The top strip of the comparison rectangle `(c, v)` is an old cell: the product of the
`c`-th horizontal interval and of the vertical interval `b v + (b - 1)` of stage `j`, which is
the block `B_b` of the `v`-th vertical interval of stage `j + 1` (`vcell_eq_block`). -/
lemma topStrip_eq {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    topStrip b h j c v =
      Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
        vcell b h j (b * v + (b - 1)) := by
  unfold topStrip vcell vlen
  push_cast [Nat.cast_pred hb]
  congr 2 <;> ring

/-- The old cells of the comparison rectangle `(c, v)` other than the bottom and the top one,
that is, those with the vertical interval `b v + ℓ` of stage `j`, `1 ≤ ℓ ≤ b - 2` (the blocks
`B_2, …, B_{b-1}`), lie in its inner region. -/
lemma prod_vcell_subset_innerRegion {b : ℕ} (hb : 0 < b) (h j c v : ℕ) {ℓ : ℕ} (h1 : 1 ≤ ℓ)
    (h2 : ℓ + 2 ≤ b) :
    Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ vcell b h j (b * v + ℓ) ⊆
      innerRegion b h j c v := by
  have hL := vlen_pos hb h j
  -- the inner vertical interval is `[(b v + 1) b^{j-h}, (b v + b - 1) b^{j-h})`
  have e1 : ((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h =
      ((b : ℝ) * v + 1) * vlen b h j := by
    unfold vlen
    ring
  have e2 : (((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h =
      ((b : ℝ) * v + b - 1) * vlen b h j := by
    unfold vlen
    ring
  have h1R : (1 : ℝ) ≤ ℓ := by exact_mod_cast h1
  have h2R : (ℓ : ℝ) + 2 ≤ b := by exact_mod_cast h2
  rintro ⟨x, y⟩ ⟨hx, hy1, hy2⟩
  push_cast at hy1 hy2
  refine Set.mk_mem_prod hx ⟨?_, ?_⟩
  · rw [e1]
    exact (mul_le_mul_of_nonneg_right (by linarith) hL.le).trans hy1
  · rw [e2]
    exact hy2.trans_le (mul_le_mul_of_nonneg_right (by linarith) hL.le)

/-! ### 2. Fewer than `M/b` heavy regions -/

/-- "\[…\] no point lies in two inner regions": a point whose horizontal coordinate is not of
the form `k/b^j` lies in at most one inner region. (The horizontal intervals are closed, so
two neighbouring inner regions share a vertical segment.) -/
lemma innerRegion_inj {b h j : ℕ} (hb : 0 < b) {z : ℝ × ℝ}
    (hz : ∀ k : ℕ, z.1 ≠ (k : ℝ) / (b : ℝ) ^ j) {c c' v v' : ℕ}
    (h1 : z ∈ innerRegion b h j c v) (h2 : z ∈ innerRegion b h j c' v') : c = c' ∧ v = v' := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpj : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  have hpj1 : (0 : ℝ) < (b : ℝ) ^ (j + 1) := by positivity
  have hph : (0 : ℝ) < (b : ℝ) ^ h := by positivity
  obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := h1
  obtain ⟨⟨hx1', hx2'⟩, hy1', hy2'⟩ := h2
  -- two horizontal intervals with a common point that is not an endpoint
  have auxh : ∀ {a a' : ℕ}, (a : ℝ) / (b : ℝ) ^ j ≤ z.1 →
      z.1 ≤ ((a' : ℝ) + 1) / (b : ℝ) ^ j → a ≤ a' := by
    intro a a' ha ha'
    have hne := hz (a' + 1)
    push_cast at hne
    have hlt : (a : ℝ) / (b : ℝ) ^ j < ((a' : ℝ) + 1) / (b : ℝ) ^ j :=
      lt_of_le_of_lt ha (lt_of_le_of_ne ha' hne)
    have hlt' : (a : ℝ) < (a' : ℝ) + 1 := (div_lt_div_iff_of_pos_right hpj).mp hlt
    have : a < a' + 1 := by exact_mod_cast hlt'
    omega
  -- two inner vertical intervals with a common point
  have auxv : ∀ {a a' : ℕ}, ((a : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h ≤ z.2 →
      z.2 < (((a' : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h → a ≤ a' := by
    intro a a' ha ha'
    have hlt := (div_lt_div_iff_of_pos_right hph).mp (lt_of_le_of_lt ha ha')
    by_contra hcon
    have hcon' : (a' : ℝ) + 1 ≤ a := by exact_mod_cast not_le.mp hcon
    have := mul_le_mul_of_nonneg_right hcon' hpj1.le
    linarith
  exact ⟨le_antisymm (auxh hx1 hx2') (auxh hx1' hx2),
    le_antisymm (auxv hy1 hy2') (auxv hy1' hy2)⟩

/-- The inner regions of a collection hold at most `n` points in total, "since no point lies
in two inner regions".

Needs that no horizontal coordinate of a point has the form `k/b^j` (from `NoGrid`). -/
lemma sum_innerCount_le {b h j : ℕ} (hb : 0 < b) {P : Fin n → ℝ × ℝ} (hgrid : NoGrid b P)
    (𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) :
    ∑ p ∈ 𝒮, innerCount b h j P p.1 p.2 ≤ n := by
  -- the sets of the points in two different inner regions are disjoint
  have hdisj : (𝒮 : Set (Fin (b ^ j) × Fin (b ^ (h - j - 1)))).PairwiseDisjoint
      (fun p => Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1 p.2)) := by
    intro p _ p' _ hne
    refine Finset.disjoint_left.mpr fun i hi hi' => hne ?_
    have hz : ∀ k : ℕ, (P i).1 ≠ (k : ℝ) / (b : ℝ) ^ j := fun k => by
      have := (hgrid i (k : ℤ) j).1
      push_cast at this
      exact this
    have := innerRegion_inj hb hz (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2
    exact Prod.ext (Fin.ext this.1) (Fin.ext this.2)
  calc ∑ p ∈ 𝒮, innerCount b h j P p.1 p.2
      = (𝒮.biUnion fun p =>
          Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1 p.2)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

/-- "There are fewer than `M/b` heavy regions, since no point lies in two inner regions and
each heavy one contains more than `bn/M` of the `n` points."

Needs that no horizontal coordinate of a point has the form `k/b^j` (from `NoGrid`). -/
theorem card_heavySet_lt {b h j : ℕ} (hb : 0 < b) {P : Fin n → ℝ × ℝ} (hgrid : NoGrid b P) :
    ((heavySet b h j P).card : ℝ) < (b : ℝ) ^ (h - 1) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  rcases (heavySet b h j P).eq_empty_or_nonempty with hH | hH
  · rw [hH, Finset.card_empty, Nat.cast_zero]
    positivity
  -- each heavy region contains more than `bn/M` points
  have h1 : ∑ _p ∈ heavySet b h j P, (b : ℝ) * n / (b : ℝ) ^ (h - 1) <
      ∑ p ∈ heavySet b h j P, (innerCount b h j P p.1 p.2 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hH fun p hp => mem_heavySet.mp hp
  -- no point lies in two inner regions
  have h2 : ∑ p ∈ heavySet b h j P, (innerCount b h j P p.1 p.2 : ℝ) ≤ n := by
    exact_mod_cast sum_innerCount_le hb hgrid (heavySet b h j P)
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  -- so `|heavy| · bn/M < n`
  have h3 : ((heavySet b h j P).card : ℝ) * ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) < n :=
    lt_of_lt_of_le h1 h2
  have hn : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) h3
  rw [lt_div_iff₀ hbR]
  have h4 : ((heavySet b h j P).card : ℝ) * b * n < (b : ℝ) ^ (h - 1) * n := by
    have h5 : ((heavySet b h j P).card : ℝ) * ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) =
        ((heavySet b h j P).card : ℝ) * b * n / (b : ℝ) ^ (h - 1) := by ring
    rw [h5, div_lt_iff₀ hM] at h3
    linarith
  exact lt_of_mul_lt_mul_right h4 hn.le

/-! ### 3. More than `n/2` points lie in `W` -/

/-- Every `x ∈ [0,1]` lies in one of the `b^j` horizontal intervals
`[c b^{-j}, (c+1) b^{-j}]` of stage `j`. -/
lemma exists_hcell {b : ℕ} (hb : 0 < b) (j : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c, c < b ^ j ∧ x ∈ Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hN : 0 < b ^ j := pow_pos hb j
  have hNR : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · -- `x < 1`: the interval `c = ⌊b^j x⌋`
    have h0 : 0 ≤ (b : ℝ) ^ j * x := mul_nonneg hNR.le hx.1
    refine ⟨⌊(b : ℝ) ^ j * x⌋₊, ?_, ?_, ?_⟩
    · rw [Nat.floor_lt h0]
      push_cast
      exact mul_lt_of_lt_one_right hNR hlt
    · rw [div_le_iff₀ hNR]
      linarith [Nat.floor_le h0]
    · rw [le_div_iff₀ hNR]
      linarith [Nat.lt_floor_add_one ((b : ℝ) ^ j * x)]
  · -- `x = 1`: the last interval, `c = b^j - 1`
    have hc : ((b ^ j - 1 : ℕ) : ℝ) = (b : ℝ) ^ j - 1 := by
      rw [Nat.cast_pred hN, Nat.cast_pow]
    refine ⟨b ^ j - 1, Nat.sub_lt hN one_pos, ?_, ?_⟩
    · rw [hc, heq, div_le_one hNR]
      linarith
    · rw [hc, heq, sub_add_cancel, div_self hNR.ne']

/-- Every height in `[0,1)` lies in one of the `b^{h-j}` vertical intervals
`[w b^{j-h}, (w+1) b^{j-h})` of stage `j`: the interval `w = ⌊b^{h-j} y⌋`. -/
lemma exists_vcell {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    ∃ w, w < b ^ (h - j) ∧ y ∈ vcell b h j w := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hL : (0 : ℝ) < (b : ℝ) ^ (h - j) := by positivity
  -- `b^{j-h} = 1 / b^{h-j}`
  have hvl : vlen b h j = 1 / (b : ℝ) ^ (h - j) := by
    unfold vlen
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add,
      Nat.add_sub_cancel' hj]
  have h0 : 0 ≤ (b : ℝ) ^ (h - j) * y := mul_nonneg hL.le hy.1
  refine ⟨⌊(b : ℝ) ^ (h - j) * y⌋₊, ?_, ?_, ?_⟩
  · rw [Nat.floor_lt h0]
    push_cast
    exact mul_lt_of_lt_one_right hL hy.2
  · rw [hvl, mul_one_div, div_le_iff₀ hL]
    linarith [Nat.floor_le h0]
  · rw [hvl, mul_one_div, lt_div_iff₀ hL]
    linarith [Nat.lt_floor_add_one ((b : ℝ) ^ (h - j) * y)]

/-- **The boundary strips and the inner regions cover `[0,1] × [0,1)`**: a point of
`[0,1] × [0,1)` lies in a boundary strip or in an inner region.

The point lies in an old cell: in a horizontal interval `c` and in a vertical interval `w` of
stage `j`. Write `w = b v + ℓ` with `ℓ < b`. For `ℓ = 0` and for `ℓ = b - 1` the old cell is a
boundary strip of the comparison rectangle `(c, v)`, and otherwise it lies in the inner region
of this rectangle. -/
theorem mem_boundaryStrips_or_innerRegion {b h j : ℕ} (hb : 0 < b) (hj : j < h) {z : ℝ × ℝ}
    (hz1 : z.1 ∈ Set.Icc (0 : ℝ) 1) (hz2 : z.2 ∈ Set.Ico (0 : ℝ) 1) :
    z ∈ boundaryStrips b h j ∨
      ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)), z ∈ innerRegion b h j c v := by
  obtain ⟨c, hc, hx⟩ := exists_hcell hb j hz1
  obtain ⟨w, hw, hy⟩ := exists_vcell hb hj.le hz2
  -- `w = b v + ℓ` with `v = w / b < b^{h-j-1}` and `ℓ = w % b < b`
  have hv : w / b < b ^ (h - j - 1) := by
    rw [Nat.div_lt_iff_lt_mul hb, ← pow_succ]
    have : h - j - 1 + 1 = h - j := by omega
    rwa [this]
  have hℓ : w % b < b := Nat.mod_lt _ hb
  rw [← Nat.div_add_mod w b] at hy
  have hmem : z ∈ Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
      vcell b h j (b * (w / b) + w % b) := ⟨hx, hy⟩
  by_cases h0 : w % b = 0
  · -- the bottom old cell
    left
    rw [h0, add_zero, ← bottomStrip_eq] at hmem
    exact Set.mem_iUnion.mpr ⟨(⟨c, hc⟩, ⟨w / b, hv⟩), Or.inl hmem⟩
  by_cases h1 : w % b = b - 1
  · -- the top old cell
    left
    rw [h1, ← topStrip_eq hb] at hmem
    exact Set.mem_iUnion.mpr ⟨(⟨c, hc⟩, ⟨w / b, hv⟩), Or.inr hmem⟩
  · -- another old cell
    right
    exact ⟨⟨c, hc⟩, ⟨w / b, hv⟩,
      prod_vcell_subset_innerRegion hb h j c (w / b) (by omega) (by omega) hmem⟩

/-- On the probability-one event of Section 2.1 the points lie in `[0,1] × [0,1)`: no height
is `1 = 1/b^0`. -/
lemma mem_unit_of_inUnit_of_noGrid {b : ℕ} {P : Fin n → ℝ × ℝ} (hP : InUnit P)
    (hgrid : NoGrid b P) (i : Fin n) :
    (P i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ico (0 : ℝ) 1 := by
  have h1 := (hgrid i 1 0).2
  simp only [Int.cast_one, pow_zero, div_one] at h1
  exact ⟨⟨(hP i).1.1.le, (hP i).1.2⟩, ⟨(hP i).2.1.le, lt_of_le_of_ne (hP i).2.2 h1⟩⟩

/-- "Every other point lies in a heavy inner region or in a boundary strip": a point of
`[0,1] × [0,1)` that does not lie in an inner region that is not heavy lies in `W`. -/
theorem mem_Wset_heavySet {b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Fin n → ℝ × ℝ} {i : Fin n}
    (hi1 : (P i).1 ∈ Set.Icc (0 : ℝ) 1) (hi2 : (P i).2 ∈ Set.Ico (0 : ℝ) 1)
    (hi : ¬ ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
      P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v) :
    P i ∈ Wset b h j (heavySet b h j P) := by
  rcases mem_boundaryStrips_or_innerRegion hb hj hi1 hi2 with hs | ⟨c, v, hin⟩
  · exact mem_Wset.mpr (Or.inl hs)
  · have hheavy : Heavy b h j P c v := by
      by_contra hnh
      exact hi ⟨c, v, hin, hnh⟩
    exact mem_Wset.mpr (Or.inr ⟨(c, v), (mem_heavySet (p := (c, v))).mpr hheavy, hin⟩)

/-- "Suppose that `G_j` fails, that is, fewer than `n/2` points lie in inner regions that are
not heavy. Every other point lies in a heavy inner region or in a boundary strip \[…\]. So
more than `n/2` points lie in the union `W` of the boundary strips and the heavy regions."

Needs that the points lie in `[0,1] × [0,1)`. -/
theorem half_lt_card_Wset {b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Fin n → ℝ × ℝ}
    (hP : ∀ i, (P i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ico (0 : ℝ) 1)
    (hbad : ¬ GoodTransition b h j P) :
    (n : ℝ) / 2 <
      (Finset.univ.filter (fun i => P i ∈ Wset b h j (heavySet b h j P))).card := by
  -- the points in inner regions that are not heavy, and the other points
  set light : Finset (Fin n) := Finset.univ.filter (fun i => ∃ c : Fin (b ^ j),
    ∃ v : Fin (b ^ (h - j - 1)), P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)
  set other : Finset (Fin n) := Finset.univ.filter (fun i => ¬ ∃ c : Fin (b ^ j),
    ∃ v : Fin (b ^ (h - j - 1)), P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)
  -- `G_j` fails: fewer than `n/2` points lie in inner regions that are not heavy
  have hfew : (light.card : ℝ) < (n : ℝ) / 2 := not_le.mp hbad
  have hsplit : (light.card : ℝ) + other.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
        P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  -- every other point lies in `W`
  have hsub : other ⊆ Finset.univ.filter (fun i => P i ∈ Wset b h j (heavySet b h j P)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      mem_Wset_heavySet hb hj (hP i).1 (hP i).2 (Finset.mem_filter.mp hi).2⟩
  have hle : (other.card : ℝ) ≤
      (Finset.univ.filter (fun i => P i ∈ Wset b h j (heavySet b h j P))).card := by
    exact_mod_cast Finset.card_le_card hsub
  linarith

/-! ### 4. `W_𝒮` has area at most `3/b` -/

/-- The area of a rectangle. -/
lemma volume_Icc_prod_Ico {a c : ℝ} (hac : a ≤ c) (d e : ℝ) :
    volume (Set.Icc a c ×ˢ Set.Ico d e) = ENNReal.ofReal ((c - a) * (e - d)) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Ico,
    ENNReal.ofReal_mul (sub_nonneg.mpr hac)]

/-- A bottom strip is an old cell, of area `b^{-j} · b^{j-h} = b^{-h} = 1/(bM)`. -/
lemma volume_bottomStrip {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    volume (bottomStrip b h j c v) = ENNReal.ofReal (1 / (b : ℝ) ^ h) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold bottomStrip
  rw [volume_Icc_prod_Ico (div_le_div_of_nonneg_right (by linarith) (by positivity))]
  congr 1
  field_simp
  ring

/-- A top strip is an old cell, of area `b^{-j} · b^{j-h} = b^{-h} = 1/(bM)`. -/
lemma volume_topStrip {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    volume (topStrip b h j c v) = ENNReal.ofReal (1 / (b : ℝ) ^ h) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold topStrip
  rw [volume_Icc_prod_Ico (div_le_div_of_nonneg_right (by linarith) (by positivity))]
  congr 1
  field_simp
  ring

/-- An inner region has area `b^{-j} · (b - 2) b^{j-h} = (b - 2) b^{-h} = (b - 2)/(bM)`. -/
lemma volume_innerRegion {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    volume (innerRegion b h j c v) = ENNReal.ofReal (((b : ℝ) - 2) / (b : ℝ) ^ h) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold innerRegion
  rw [volume_Icc_prod_Ico (div_le_div_of_nonneg_right (by linarith) (by positivity))]
  congr 1
  field_simp
  ring

/-- `b^h = b M`. -/
lemma pow_eq_mul_pow_pred {b h : ℕ} (hh : 0 < h) : (b : ℝ) ^ h = b * (b : ℝ) ^ (h - 1) := by
  rw [← pow_succ']
  congr 1
  omega

/-- "The regions in `𝒮` have area less than `1/M` each". -/
lemma volume_innerRegion_lt {b h : ℕ} (hb : 0 < b) (hh : 0 < h) (j c v : ℕ) :
    volume (innerRegion b h j c v) < ENNReal.ofReal (1 / (b : ℝ) ^ (h - 1)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  rw [volume_innerRegion hb, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    pow_eq_mul_pow_pred hh, div_lt_div_iff₀ (by positivity) hM]
  linarith

/-- Two different vertical intervals of a stage are disjoint: they are closed at the bottom and
open at the top. (`vcell_disjoint` in `StageGeometry.lean`, which imports this module, is the
same statement.) -/
lemma disjoint_vcell_of_ne {b : ℕ} (hb : 0 < b) (h j : ℕ) {v v' : ℕ} (hv : v ≠ v') :
    Disjoint (vcell b h j v) (vcell b h j v') := by
  -- the vertical intervals of stage `j` are the blocks of length `b^{j-h}` that start at `0`
  have e : ∀ w : ℕ, vcell b h j w = block 0 (vlen b h j) w := by
    intro w
    unfold vcell block
    rw [zero_add, zero_add]
  rw [e v, e v']
  exact block_disjoint 0 (vlen_pos hb h j) hv

/-- The vertical interval `b v + ℓ` of stage `j`, `ℓ < b`, lies in the `v`-th vertical interval
of stage `j + 1`: the heights of an old cell of the comparison rectangle `(c, v)` lie in the
vertical interval `J` of this rectangle. -/
lemma vcell_subset_vcell_succ {b : ℕ} (hb : 0 < b) (h j v : ℕ) {ℓ : ℕ} (hℓ : ℓ < b) :
    vcell b h j (b * v + ℓ) ⊆ vcell b h (j + 1) v := by
  rw [vcell_eq_block, vcell_succ_eq]
  exact block_subset _ (vlen_pos hb h j) hℓ

/-- The union of the `b^j` horizontal intervals `[c b^{-j}, (c+1) b^{-j}]` of stage `j` is
`[0, 1]`. (`iUnion_hcell` in `StageGeometry.lean`, which imports this module, is the same
statement.) -/
lemma iUnion_Icc_div_pow {b : ℕ} (hb : 0 < b) (j : ℕ) :
    ⋃ c : Fin (b ^ j), Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) =
      Set.Icc (0 : ℝ) 1 := by
  have hpj : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  apply Set.Subset.antisymm
  · -- each interval lies in `[0, 1]`, since `0 ≤ c` and `c + 1 ≤ b^j`
    refine Set.iUnion_subset fun c => ?_
    have hc1 : ((c : ℕ) : ℝ) + 1 ≤ (b : ℝ) ^ j := by exact_mod_cast c.isLt
    rintro x ⟨h1, h2⟩
    exact ⟨le_trans (by positivity) h1, h2.trans ((div_le_one hpj).mpr hc1)⟩
  · -- every `x ∈ [0, 1]` lies in one of the intervals (`exists_hcell`)
    intro x hx
    obtain ⟨c, hc, hxc⟩ := exists_hcell hb j hx
    exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hxc⟩

/-- The union of the boundary strips is the product of `[0, 1]` and of the union of the
vertical intervals `b v` and `b v + (b - 1)` of stage `j`, `v < b^{h-j-1}`: the union of the
horizontal intervals of stage `j` is `[0, 1]`, and the heights of the bottom and of the top
old cell of the comparison rectangle `(c, v)` do not depend on `c`. -/
lemma boundaryStrips_eq_prod {b : ℕ} (hb : 0 < b) (h j : ℕ) :
    boundaryStrips b h j = Set.Icc (0 : ℝ) 1 ×ˢ
      ⋃ v : Fin (b ^ (h - j - 1)), (vcell b h j (b * v) ∪ vcell b h j (b * v + (b - 1))) := by
  -- the product of two unions is the union of the products
  rw [← iUnion_Icc_div_pow hb j, ← Set.iUnion_prod]
  -- the bottom and the top old cell of the comparison rectangle `p = (c, v)`
  exact Set.iUnion_congr fun p => by rw [bottomStrip_eq, topStrip_eq hb, Set.prod_union]

/-- "The boundary strips are two of the `b` old cells of every comparison rectangle, so they
cover an area of `2/b`", for `b ≥ 2`. (For `b = 1` the bottom and the top old cell of a
comparison rectangle coincide.)

The union of the boundary strips is the product of `[0, 1]` and of the union of
`2 b^{h-j-1}` disjoint vertical intervals of length `b^{j-h}` (`boundaryStrips_eq_prod`). -/
theorem volume_boundaryStrips {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) :
    volume (boundaryStrips b h j) = ENNReal.ofReal (2 / (b : ℝ)) := by
  have hb0 : 0 < b := by omega
  have hL := vlen_pos hb0 h j
  -- a vertical interval of stage `j` has length `b^{j-h}`
  have hvol : ∀ w : ℕ, volume (vcell b h j w) = ENNReal.ofReal (vlen b h j) := by
    intro w
    rw [vcell, Real.volume_Ico]
    congr 1
    ring
  -- the bottom and the top old cell of a comparison rectangle are disjoint, since `b ≥ 2`
  have hterm : ∀ v : Fin (b ^ (h - j - 1)),
      volume (vcell b h j (b * v) ∪ vcell b h j (b * v + (b - 1))) =
        ENNReal.ofReal (2 * vlen b h j) := by
    intro v
    rw [measure_union (disjoint_vcell_of_ne hb0 h j (by omega)) measurableSet_Ico, hvol, hvol,
      ← ENNReal.ofReal_add hL.le hL.le, two_mul]
  -- the heights of the boundary strips of the comparison rectangle `(c, v)` lie in its
  -- vertical interval `J` (the old cells `ℓ = 0` and `ℓ = b - 1`)
  have hsub : ∀ v : ℕ,
      vcell b h j (b * v) ∪ vcell b h j (b * v + (b - 1)) ⊆ vcell b h (j + 1) v := fun v =>
    Set.union_subset (vcell_subset_vcell_succ hb0 h j v (ℓ := 0) hb0)
      (vcell_subset_vcell_succ hb0 h j v (ℓ := b - 1) (by omega))
  -- so they are disjoint for two different `v`
  have hdisj : Pairwise (Function.onFun Disjoint fun v : Fin (b ^ (h - j - 1)) =>
      vcell b h j (b * v) ∪ vcell b h j (b * v + (b - 1))) := fun v v' hvv =>
    (disjoint_vcell_of_ne hb0 h (j + 1) (Fin.val_ne_of_ne hvv)).mono (hsub v) (hsub v')
  -- `b^h = b^{h-j-1} · b^j · b`
  have hpow : (b : ℝ) ^ h = (b : ℝ) ^ (h - j - 1) * (b : ℝ) ^ j * b := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  calc volume (boundaryStrips b h j)
      = volume (⋃ v : Fin (b ^ (h - j - 1)),
          (vcell b h j (b * v) ∪ vcell b h j (b * v + (b - 1)))) := by
        -- the area of a product is the product of the lengths, and `[0, 1]` has length `1`
        rw [boundaryStrips_eq_prod hb0, Measure.volume_eq_prod, Measure.prod_prod,
          Real.volume_Icc, sub_zero, ENNReal.ofReal_one, one_mul]
    _ = ∑ v : Fin (b ^ (h - j - 1)),
          volume (vcell b h j (b * v) ∪ vcell b h j (b * v + (b - 1))) := by
        -- the length is additive on disjoint intervals
        rw [measure_iUnion hdisj fun v => measurableSet_Ico.union measurableSet_Ico,
          tsum_fintype]
    _ = ∑ _v : Fin (b ^ (h - j - 1)), ENNReal.ofReal (2 * vlen b h j) :=
        Finset.sum_congr rfl fun v _ => hterm v
    _ = ENNReal.ofReal (2 / (b : ℝ)) := by
        -- `b^{h-j-1} · 2 b^{j-h} = 2/b`
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        unfold vlen
        rw [hpow]
        push_cast
        field_simp

/-- The boundary strips cover an area of at most `2/b`, for every `b ≥ 1`: there are `M`
comparison rectangles, each of them has two boundary strips, and an old cell has area
`1/(bM)`. This bound is used for `volume_Wset_le`. The sentence "The boundary strips are two
of the `b` old cells of every comparison rectangle, so they cover an area of `2/b`" is
`volume_boundaryStrips`: for `b ≥ 2` the area is equal to `2/b`. -/
theorem volume_boundaryStrips_le {b h j : ℕ} (hb : 0 < b) (hj : j < h) :
    volume (boundaryStrips b h j) ≤ ENNReal.ofReal (2 / (b : ℝ)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  calc volume (boundaryStrips b h j)
      ≤ ∑ p : Fin (b ^ j) × Fin (b ^ (h - j - 1)),
          volume (bottomStrip b h j p.1 p.2 ∪ topStrip b h j p.1 p.2) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin (b ^ j) × Fin (b ^ (h - j - 1)), ENNReal.ofReal (2 / (b : ℝ) ^ h) := by
        refine Finset.sum_le_sum fun p _ => (measure_union_le _ _).trans ?_
        rw [volume_bottomStrip hb, volume_topStrip hb,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        ring
    _ = ENNReal.ofReal (2 / (b : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, card_compRect hj, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        rw [pow_eq_mul_pow_pred (by omega : 0 < h)]
        field_simp

/-- "The regions in `𝒮` have area less than `1/M` each, so they cover an area of less than
`1/b`", for a collection `𝒮` of fewer than `M/b` inner regions. The inequality is strict
because there are fewer than `M/b` regions; this covers the empty collection. -/
theorem volume_innerRegions_lt {b h j : ℕ} (hb : 0 < b) (hj : j < h)
    {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))}
    (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) :
    volume (⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2) < ENNReal.ofReal (1 / (b : ℝ)) := by
  calc volume (⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2)
      ≤ ∑ p ∈ 𝒮, volume (innerRegion b h j p.1 p.2) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ 𝒮, ENNReal.ofReal (1 / (b : ℝ) ^ (h - 1)) :=
        Finset.sum_le_sum fun p _ => (volume_innerRegion_lt hb (by omega) j p.1 p.2).le
    _ = ENNReal.ofReal (𝒮.card * (1 / (b : ℝ) ^ (h - 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ < ENNReal.ofReal (1 / (b : ℝ)) := by
        -- there are fewer than `M/b` regions
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        calc (𝒮.card : ℝ) * (1 / (b : ℝ) ^ (h - 1))
            < (b : ℝ) ^ (h - 1) / b * (1 / (b : ℝ) ^ (h - 1)) :=
              mul_lt_mul_of_pos_right h𝒮 (by positivity)
          _ = 1 / (b : ℝ) := by field_simp

/-- The regions in a collection `𝒮` of fewer than `M/b` inner regions cover an area of at most
`1/b`. This is the weak form of `volume_innerRegions_lt`, which is the sentence "The regions
in `𝒮` have area less than `1/M` each, so they cover an area of less than `1/b`". -/
theorem volume_innerRegions_le {b h j : ℕ} (hb : 0 < b) (hj : j < h)
    {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))}
    (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) :
    volume (⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2) ≤ ENNReal.ofReal (1 / (b : ℝ)) :=
  (volume_innerRegions_lt hb hj h𝒮).le

/-- "Hence `W_𝒮` is a fixed set of area at most `3/b`", for every collection `𝒮` of fewer
than `M/b` inner regions: the boundary strips cover an area of at most `2/b`
(`volume_boundaryStrips_le`; equal to `2/b` for `b ≥ 2`, `volume_boundaryStrips`), and the
regions in `𝒮` cover an area of less than `1/b` (`volume_innerRegions_lt`). -/
theorem volume_Wset_le {b h j : ℕ} (hb : 0 < b) (hj : j < h)
    {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))}
    (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) :
    volume (Wset b h j 𝒮) ≤ ENNReal.ofReal (3 / (b : ℝ)) := by
  calc volume (Wset b h j 𝒮)
      ≤ volume (boundaryStrips b h j) + volume (⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 / (b : ℝ)) + ENNReal.ofReal (1 / (b : ℝ)) :=
        add_le_add (volume_boundaryStrips_le hb hj) (volume_innerRegions_lt hb hj h𝒮).le
    _ = ENNReal.ofReal (3 / (b : ℝ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The area of `W_𝒮`**, for the law of one uniform point of the unit square: a uniform
point of `[0,1]²` lies in `W_𝒮` with probability at most `3/b`, for every collection `𝒮` of
fewer than `M/b` inner regions. -/
theorem unitSq_Wset_le {b h j : ℕ} (hb : 0 < b) (hj : j < h)
    {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))}
    (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) :
    (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) (Wset b h j 𝒮) ≤ ENNReal.ofReal (3 / (b : ℝ)) :=
  (Measure.restrict_apply_le _ _).trans (volume_Wset_le hb hj h𝒮)

/-! ### 5. The probability of `E_𝒮` -/

/-- "The `n` points are independent and uniform in the unit square": the points of a given set
`T` of indices all lie in a fixed set `W` with probability `|W|^{|T|}`, where `|W|` is the
probability that one uniform point lies in `W`. -/
theorem unifPts_forall_mem (T : Finset (Fin n)) (W : Set (ℝ × ℝ)) :
    unifPts n {P | ∀ i ∈ T, P i ∈ W} =
      (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ^ T.card := by
  -- the event is a box
  have hset : {P : Fin n → ℝ × ℝ | ∀ i ∈ T, P i ∈ W} =
      Set.univ.pi (fun i => if i ∈ T then W else Set.univ) := by
    ext P
    rw [Set.mem_ofPred_eq, Set.mem_univ_pi]
    refine forall_congr' fun i => ?_
    by_cases hi : i ∈ T <;> simp [hi]
  rw [hset, Measure.pi_pi]
  calc ∏ i : Fin n, (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) (if i ∈ T then W else Set.univ)
      = ∏ i : Fin n, if i ∈ T then (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W else 1 := by
        refine Finset.prod_congr rfl fun i _ => ?_
        split_ifs
        · rfl
        · exact measure_univ
    _ = (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ^ T.card := by
        rw [Fintype.prod_ite_mem, Finset.prod_const]

/-- "\[…\] the points of a given set all lie in the fixed set `W_𝒮` with probability at most
`(3/b)^{⌈n/2⌉} ≤ (3/b)^{n/2}`, since `3/b ≤ 1`": here for a set `W` in which a uniform point
lies with probability at most `q ≤ 1`, and for a set `T` of at least `n/2` indices. -/
theorem unifPts_forall_mem_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {W : Set (ℝ × ℝ)}
    (hW : (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ≤ ENNReal.ofReal q)
    {T : Finset (Fin n)} (hT : (n : ℝ) / 2 ≤ T.card) :
    unifPts n {P | ∀ i ∈ T, P i ∈ W} ≤ ENNReal.ofReal (q ^ ((n : ℝ) / 2)) := by
  calc unifPts n {P | ∀ i ∈ T, P i ∈ W}
      = (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ^ T.card := unifPts_forall_mem T W
    _ ≤ ENNReal.ofReal q ^ T.card := pow_le_pow_left' hW _
    _ = ENNReal.ofReal (q ^ ((T.card : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast, ENNReal.ofReal_pow hq0.le]
    _ ≤ ENNReal.ofReal (q ^ ((n : ℝ) / 2)) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hT)

/-- "If `E_𝒮` occurs, then there is a set of `⌈n/2⌉` indices whose points all lie in
`W_𝒮`." -/
lemma exists_card_eq_ceil_half {W : Set (ℝ × ℝ)} {P : Fin n → ℝ × ℝ}
    (hE : (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ W)).card) :
    ∃ T : Finset (Fin n), T.card = ⌈(n : ℝ) / 2⌉₊ ∧ ∀ i ∈ T, P i ∈ W := by
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (Nat.ceil_le.mpr hE)
  exact ⟨T, hTcard, fun i hi => (Finset.mem_filter.mp (hTsub hi)).2⟩

/-- "There are at most `2^n` sets of indices. \[…\] So `Pr(E_𝒮) ≤ 2^n (3/b)^{n/2}`": if a
uniform point lies in a fixed set `W` with probability at most `q ≤ 1`, then at least `n/2` of
the `n` points lie in `W` with probability at most `2^n q^{n/2}`. -/
theorem unifPts_half_mem_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {W : Set (ℝ × ℝ)}
    (hW : (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ≤ ENNReal.ofReal q) :
    unifPts n {P | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ W)).card} ≤
      ENNReal.ofReal (2 ^ n * q ^ ((n : ℝ) / 2)) := by
  -- the sets of `⌈n/2⌉` indices
  let 𝒯 : Finset (Finset (Fin n)) := Finset.univ.filter (fun T => T.card = ⌈(n : ℝ) / 2⌉₊)
  -- if the event occurs, then the points of one of these sets all lie in `W`
  have hsub : {P : Fin n → ℝ × ℝ | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ W)).card} ⊆
      ⋃ T ∈ 𝒯, {P | ∀ i ∈ T, P i ∈ W} := by
    intro P hP
    obtain ⟨T, hT, hTW⟩ := exists_card_eq_ceil_half hP
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩) hTW
  -- there are at most `2^n` sets of indices
  have hcard : 𝒯.card ≤ 2 ^ n := by
    calc 𝒯.card ≤ (Finset.univ : Finset (Finset (Fin n))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  calc unifPts n {P | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ W)).card}
      ≤ unifPts n (⋃ T ∈ 𝒯, {P | ∀ i ∈ T, P i ∈ W}) := measure_mono hsub
    _ ≤ ∑ T ∈ 𝒯, unifPts n {P | ∀ i ∈ T, P i ∈ W} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _T ∈ 𝒯, ENNReal.ofReal (q ^ ((n : ℝ) / 2)) := by
        refine Finset.sum_le_sum fun T hT => unifPts_forall_mem_le hq0 hq1 hW ?_
        rw [(Finset.mem_filter.mp hT).2]
        exact Nat.le_ceil _
    _ = (𝒯.card : ENNReal) * ENNReal.ofReal (q ^ ((n : ℝ) / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ n : ℕ) : ENNReal) * ENNReal.ofReal (q ^ ((n : ℝ) / 2)) :=
        mul_le_mul' (Nat.cast_le.mpr hcard) le_rfl
    _ = ENNReal.ofReal (2 ^ n * q ^ ((n : ℝ) / 2)) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Nat.cast_pow,
          Nat.cast_ofNat]

/-- "So `Pr(E_𝒮) ≤ 2^n (3/b)^{n/2}`", for every collection `𝒮` of fewer than `M/b` inner
regions. -/
theorem unifPts_crowdEvent_le {b h j : ℕ} (hb : 3 ≤ b) (hj : j < h)
    {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))}
    (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) :
    unifPts n (crowdEvent b h j 𝒮) ≤
      ENNReal.ofReal (2 ^ n * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) := by
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hq0 : (0 : ℝ) < 3 / (b : ℝ) := by positivity
  -- `3/b ≤ 1`
  have hq1 : 3 / (b : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hbR
  exact unifPts_half_mem_le hq0 hq1 (unitSq_Wset_le (by omega) hj h𝒮)

/-! ### 6. The union bounds -/

/-- "We have just seen that if `G_j` fails, then `E_𝒮` occurs for the collection `𝒮` of heavy
regions."

Needs that the points lie in `[0,1] × [0,1)`. -/
theorem mem_crowdEvent_heavySet {b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Fin n → ℝ × ℝ}
    (hP : ∀ i, (P i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ico (0 : ℝ) 1)
    (hbad : ¬ GoodTransition b h j P) : P ∈ crowdEvent b h j (heavySet b h j P) :=
  (half_lt_card_Wset hb hj hP hbad).le

/-- The collection of the heavy regions is a collection of fewer than `M/b` inner regions.

Needs that no horizontal coordinate of a point has the form `k/b^j` (from `NoGrid`). -/
theorem heavySet_mem_smallCollections {b h j : ℕ} (hb : 0 < b) {P : Fin n → ℝ × ℝ}
    (hgrid : NoGrid b P) : heavySet b h j P ∈ smallCollections b h j :=
  mem_smallCollections.mpr (card_heavySet_lt hb hgrid)

/-- "So `G_j^c` is contained in the union of the events `E_𝒮`", over the collections `𝒮` of
fewer than `M/b` inner regions; on the probability-one event of Section 2.1 (`InUnit`,
`NoGrid`). -/
theorem bad_subset_iUnion_crowdEvent {b h j : ℕ} (hb : 0 < b) (hj : j < h) :
    {P : Fin n → ℝ × ℝ | ¬ GoodTransition b h j P} ∩ {P | InUnit P ∧ NoGrid b P} ⊆
      ⋃ 𝒮 ∈ smallCollections b h j, crowdEvent b h j 𝒮 := by
  rintro P ⟨hbad, hP, hgrid⟩
  exact Set.mem_biUnion (heavySet_mem_smallCollections hb hgrid)
    (mem_crowdEvent_heavySet hb hj (mem_unit_of_inUnit_of_noGrid hP hgrid) hbad)

/-- "So `G_j^c` is contained in the union of the events `E_𝒮`", almost surely. -/
theorem bad_ae_le_iUnion_crowdEvent {b h j : ℕ} (hb : 0 < b) (hj : j < h) :
    {P : Fin n → ℝ × ℝ | ¬ GoodTransition b h j P} ≤ᵐ[unifPts n]
      ⋃ 𝒮 ∈ smallCollections b h j, crowdEvent b h j 𝒮 := by
  filter_upwards [ae_inUnit n, ae_noGrid n b] with P hP hgrid hbad
  exact bad_subset_iUnion_crowdEvent hb hj ⟨hbad, hP, hgrid⟩

/-- "There are at most `2^M` collections of inner regions". -/
lemma card_smallCollections_le {b h j : ℕ} (hj : j < h) :
    (smallCollections b h j).card ≤ 2 ^ b ^ (h - 1) := by
  calc (smallCollections b h j).card
      ≤ (Finset.univ : Finset (Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1))))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ b ^ (h - 1) := by rw [Finset.card_univ, Fintype.card_finset, card_compRect hj]

/-- "There are at most `2^M` collections of inner regions, so
`Pr(G_j^c) ≤ 2^{M+n} (3/b)^{n/2}`." -/
theorem unifPts_bad_le {b h j : ℕ} (hb : 3 ≤ b) (hj : j < h) :
    unifPts n {P | ¬ GoodTransition b h j P} ≤
      ENNReal.ofReal (2 ^ (b ^ (h - 1) + n) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) := by
  calc unifPts n {P | ¬ GoodTransition b h j P}
      ≤ unifPts n (⋃ 𝒮 ∈ smallCollections b h j, crowdEvent b h j 𝒮) :=
        measure_mono_ae (bad_ae_le_iUnion_crowdEvent (by omega) hj)
    _ ≤ ∑ 𝒮 ∈ smallCollections b h j, unifPts n (crowdEvent b h j 𝒮) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _𝒮 ∈ smallCollections b h j,
          ENNReal.ofReal (2 ^ n * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) :=
        Finset.sum_le_sum fun 𝒮 h𝒮 => unifPts_crowdEvent_le hb hj (mem_smallCollections.mp h𝒮)
    _ = ((smallCollections b h j).card : ENNReal) *
          ENNReal.ofReal (2 ^ n * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ b ^ (h - 1) : ℕ) : ENNReal) *
          ENNReal.ofReal (2 ^ n * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) :=
        mul_le_mul' (Nat.cast_le.mpr (card_smallCollections_le hj)) le_rfl
    _ = ENNReal.ofReal (2 ^ (b ^ (h - 1) + n) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring

/-- "Since `M ≤ n`, we have `2^{M+n} ≤ 4^n = 16^{n/2}`, which gives `(48/b)^{n/2}`." -/
lemma two_pow_mul_rpow_le {b M : ℕ} (hb : 0 < b) (hMn : M ≤ n) :
    (2 : ℝ) ^ (M + n) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2) ≤ (48 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- `2^{M+n} ≤ 4^n`
  have h1 : (2 : ℝ) ^ (M + n) ≤ 4 ^ n := by
    calc (2 : ℝ) ^ (M + n) ≤ 2 ^ (2 * n) := pow_le_pow_right₀ one_le_two (by omega)
      _ = 4 ^ n := by
          rw [pow_mul]
          norm_num
  -- `4^n = 16^{n/2}`
  have h2 : (4 : ℝ) ^ n = (16 : ℝ) ^ ((n : ℝ) / 2) := by
    have h16 : (16 : ℝ) = (4 : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      norm_num
    rw [h16, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    congr 1
    ring
  -- `16^{n/2} (3/b)^{n/2} = (48/b)^{n/2}`
  have h3 : (48 / (b : ℝ)) ^ ((n : ℝ) / 2) =
      (16 : ℝ) ^ ((n : ℝ) / 2) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    ring
  rw [h3, ← h2]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- `Pr(G_j^c) ≤ (48/b)^{n/2}` if `M ≤ n`, as an inequality in `[0, ∞]`. -/
theorem unifPts_bad_le_rpow {b h j : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n) (hj : j < h) :
    unifPts n {P | ¬ GoodTransition b h j P} ≤
      ENNReal.ofReal ((48 / (b : ℝ)) ^ ((n : ℝ) / 2)) :=
  (unifPts_bad_le hb hj).trans
    (ENNReal.ofReal_le_ofReal (two_pow_mul_rpow_le (by omega) hMn))

/-- **Lemma 2.5(ii), one transition**, by the proof of the manuscript: if `M ≤ n`, then
`Pr(G_j^c) ≤ (48/b)^{n/2}`. -/
theorem lemma_2_5_ii {b h j : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n) (hj : j < h) :
    (unifPts n).real {P | ¬ GoodTransition b h j P} ≤ (48 / (b : ℝ)) ^ ((n : ℝ) / 2) :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (unifPts_bad_le_rpow hb hMn hj)

/-- **Lemma 2.5(ii), all transitions**: if `M ≤ n`, then `Pr(G^c) ≤ h (48/b)^{n/2}`.

"A union bound over the `h` transitions gives the bound on `Pr(G^c)`." -/
theorem lemma_2_5_ii_all {b h : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n) :
    (unifPts n).real {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} ≤
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
  -- `G^c` is the union of the events `G_j^c`, `j < h`
  have hset : {P : Fin n → ℝ × ℝ | ∃ j, j < h ∧ ¬ GoodTransition b h j P} =
      ⋃ j ∈ Finset.range h, {P | ¬ GoodTransition b h j P} := by
    ext P
    simp
  rw [hset]
  calc (unifPts n).real (⋃ j ∈ Finset.range h, {P | ¬ GoodTransition b h j P})
      ≤ ∑ j ∈ Finset.range h, (unifPts n).real {P | ¬ GoodTransition b h j P} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range h, (48 / (b : ℝ)) ^ ((n : ℝ) / 2) :=
        Finset.sum_le_sum fun j hj => lemma_2_5_ii hb hMn (Finset.mem_range.mp hj)
    _ = h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end R56Audit
