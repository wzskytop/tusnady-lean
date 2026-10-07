import R56Audit.Osc
import R56Audit.SymmetricSums

/-!
# Lemma 2.3 of the manuscript (local gain), as stated: every integer base, continuous heights

Auditor's supplement (not part of the audited archive).

**The local experiment** (Section 2.3). Fix one rectangle `R = I × J`. All colors `χ_i`, all
heights `V_i`, and the position of every point relative to `I` (to the left of `I`, in `I`,
or to the right of `I`) are fixed. Each point in `I` falls into one of the children
`C_1, …, C_b` of `I`, uniformly at random and independently of the other points.

Here the data are `ε : Fin n → ℝ` with `|ε i| = 1` (the colors), `V : Fin n → ℝ` (the
heights), `side : Fin n → Side` (the positions relative to `I`), and the outcome of the
experiment is `r : Fin n → Fin b`: the point `i`, if it lies in `I`, falls into the child
`C_{r i + 1}`. The digits of the points outside `I` are present in the sample space but
nothing depends on them (`childAvg_congr`). The expectation is the uniform average
`Oscillation.finAvg` over `r`.

| Manuscript | Here |
| --- | --- |
| weight `w_i` of `P_i` in `I`: `1`, `1/2`, `0` | `oldWeight (side i)` |
| `a(y) = Σ_i χ_i w_i 1{V_i ≤ y}`, display (2) | `endpointAvg ε V side y` |
| child function `a_k` | `childAvg ε V side r k` |
| their average `ā(y) = (1/b) Σ_k a_k(y)` | `childMean ε V side r y` |
| `J`, cut into blocks `B_1, …, B_b` | `Set.Ico s (s + b * L)`, `block s L ℓ` for `ℓ < b` |
| the points of `R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})` | `S = innerPoints b V side s L` |
| their number `m_R` | `S.card` |
| jump `X_i = χ_i (b + 1 - 2r) / (2b)` | `jump b ε i d`, with `d = r - 1` |
| `D`, the sum of the jumps of the points of `R^in` | `jumpSum S (jump b ε) r` |
| `g`, "the function `ā` without these jumps" | `withoutJumps b ε V side S r` |

`mem_innerPoints_iff` shows that `innerPoints` consists of the points of `I` whose height
lies in `B_2 ∪ ⋯ ∪ B_{b-1}`.

`local_gain` is **Lemma 2.3**: in the local experiment,

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + (1/4) √(m_R)`.

The proof is the manuscript's, in its four steps. Every display of the proof is stated in
this file, except for one expression in Step 2, which occurs in a proof only. The list says
which definition or statement is which display. Where a display is a chain of relations, the
list says which statement is which link of the chain, or that the statement is the relation
between the two ends of the chain.

* **Step 1: averaging the children.** The first display defines `ā`: it is the definition
  `childMean`. The triangle inequality (`card_mul_osc_avg_le`) and Lemma 2.1
  (`vertical_comparison`), applied to `f = ā`, give display (5): `display_5`.
* **Step 2: the weights in `ā`.** `sum_childWeight` is the display on the weight of a point
  in `ā`: for a point of `I` in the child `C_r`, this weight is the right-hand side
  `1/2 + (b + 1 - 2r) / (2b)` of the display, the old weight `1/2` plus a deviation (and a
  point outside `I` keeps its old weight). The left-hand side `((b - r) + 1/2) / b` of the
  display is a step of the proof of `sum_childWeight`, not a statement. Display (6) is
  `display_6`; `childMean_eq` is the same statement with the right-hand side written as one
  step function. The jumps are symmetric (`jump_rev`), and this gives display (7):
  `finAvg_childMean`.
* **Step 3: taking expectations.** `osc_endpointAvg_le` is the display
  `E osc_{B_ℓ} ā = E max_{B_ℓ} ā - E min_{B_ℓ} ā ≥ max_{B_ℓ} a - min_{B_ℓ} a = osc_{B_ℓ} a`,
  stated as the inequality `E osc_{B_ℓ} ā ≥ osc_{B_ℓ} a` between its two ends: the two
  equalities hold by the definition of `osc` and the linearity of `E`, and the inequality in
  the middle is `maxOn_endpointAvg_le` and `finAvg_minOn_childMean_le`. Taking expectations
  in (5) gives display (8): `display_8`.
* **Step 4: the gain.** `withoutJumps_eq` is the display that defines `g`, and `offset_eq` is
  the display `mid_{B_b} ā - mid_{B_1} ā = θ + D`, where `θ = mid_{B_b} g - mid_{B_1} g`. In
  the rest of the step `r = d + 1` is the index of the child and `σ² = (b² - 1) / (12 b²)`.
  * The sentences before the next display: `jump_sq_eq` is `X_i² = (r - (b+1)/2)² / b²`;
    `finAvg_childIndex` and `finAvg_childIndex_sq` are the mean `(b+1)/2` and the second
    moment `(b+1)(2b+1)/6` of `r`; `finAvg_childIndex_var` is its variance,
    `(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12` (both equalities); and `abs_jump_le` is
    `|X_i| ≤ (b-1)/(2b)`.
  * The display on the moments of the jumps: `finAvg_jump_sq` is `E X_i² = σ²`. The chain
    `E X_i⁴ ≤ ((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴` is `finAvg_jump_fourth_le_sq` (its
    first inequality) and `sq_mul_sigma_sq_le` (its second inequality and its equality);
    `finAvg_jump_fourth_le` is the inequality `E X_i⁴ ≤ 3σ⁴` between its two ends.
  * The last display,
    `E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b²-1) / (6b)) √(m_R) ≥ √(m_R) / 8`:
    `expected_offset_ge_sigma` is its first inequality, by Fact 2.2 (`symmetric_sum_abs`, an
    application of `fact_2_2_general`); `sigma_mul_sqrt_eq` is its equality;
    `sqrt_sq_sub_one_div_ge` is its last inequality; `sqrt_div_eight_le` is the equality and
    the last inequality together, `σ √(m/3) ≥ √m / 8`; and `expected_offset_ge` is the
    inequality between the two ends of the display.

"Together with (8), this proves the inequality of the lemma": `local_gain` is proved from
`display_8` and `expected_offset_ge`.

**Blocks of an interval, and arbitrary sets of heights.** `display_5`, `display_8`,
`offset_eq`, `expected_offset_ge_sigma` and `expected_offset_ge` are stated as in the
manuscript, for the blocks `B_1, …, B_b` of an interval `J` and the points of `R^in`. The
first four are proved from statements of the same form for sets of heights in place of the
blocks:

* `display_5` from `avg_comparison_core`, and `display_8` from `expected_comparison_core`
  (which is proved from `avg_comparison_core` and `osc_endpointAvg_le`). These two are stated
  for nonempty subsets `B_1, …, B_b` of a set `J` of heights, with the inequality of
  Lemma 2.1 as a hypothesis; for the blocks of an interval this hypothesis is
  `vertical_comparison`.
* `offset_eq` from `offset_core`, and `expected_offset_ge_sigma` from
  `expected_offset_core_sigma` (which is proved from `offset_core` and Fact 2.2). These two
  are stated for nonempty sets `B_1, …, B_b` of heights and a set `S` of points of `I` whose
  heights lie above all of `B_1` and at or below all of `B_b`; for the blocks of an interval
  and the points of `R^in` this hypothesis is `innerPoints_between_blocks`.

`expected_offset_ge` is proved from `expected_offset_ge_sigma` and `sqrt_div_eight_le`. In
the same way `expected_offset_core`, the same inequality for sets of heights, is proved from
`expected_offset_core_sigma` and `sqrt_div_eight_le`. Display (6) does not involve the
blocks: `display_6` is proved from `childMean_eq`.

So the same steps serve for intervals and for sampled heights: `local_gain_core`, proved
from `expected_comparison_core` and `expected_offset_core`, and `local_gain_sets` are
Lemma 2.3 in this generality.

`EndpointAverage.lean` proves that `endpointAvg` and `childAvg` are the endpoint averages
`(F(I⁻, y) + F(I⁺, y)) / 2` of `I` and of its children (first equality of display (2)).
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ}

/-! ### Step functions of the height -/

/-- The function `y ↦ Σ_i c_i 1{V_i ≤ y}` of the height. The manuscript's functions of the
height are of this form up to an additive constant; those of Lemma 2.3 (`endpointAvg`,
`childAvg` and their average) are exactly of this form. -/
def stepFn (V : Fin n → ℝ) (c : Fin n → ℝ) (y : ℝ) : ℝ := ∑ i, if V i ≤ y then c i else 0

lemma stepFn_add (V c c' : Fin n → ℝ) (y : ℝ) :
    stepFn V (fun i => c i + c' i) y = stepFn V c y + stepFn V c' y := by
  unfold stepFn
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma stepFn_sum {ι : Type*} (s : Finset ι) (V : Fin n → ℝ) (c : ι → Fin n → ℝ) (y : ℝ) :
    stepFn V (fun i => ∑ k ∈ s, c k i) y = ∑ k ∈ s, stepFn V (c k) y := by
  unfold stepFn
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma stepFn_div (V c : Fin n → ℝ) (t : ℝ) (y : ℝ) :
    stepFn V (fun i => c i / t) y = stepFn V c y / t := by
  unfold stepFn
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma stepFn_congr (V : Fin n → ℝ) {c c' : Fin n → ℝ} (h : ∀ i, c i = c' i) (y : ℝ) :
    stepFn V c y = stepFn V c' y := by
  unfold stepFn
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- "They take finitely many values". -/
lemma stepFn_image_finite (V c : Fin n → ℝ) (B : Set ℝ) : ((stepFn V c) '' B).Finite := by
  classical
  refine (Set.finite_range (fun T : Finset (Fin n) => ∑ i ∈ T, c i)).subset ?_
  rintro _ ⟨y, -, rfl⟩
  refine ⟨Finset.univ.filter (fun i => V i ≤ y), ?_⟩
  simp only [stepFn]
  rw [Finset.sum_filter]

/-- Below all the heights that carry a nonzero coefficient, the function vanishes. -/
lemma stepFn_eq_zero (V : Fin n → ℝ) {c : Fin n → ℝ} {y : ℝ} (h : ∀ i, c i ≠ 0 → y < V i) :
    stepFn V c y = 0 := by
  unfold stepFn
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hi
  · by_contra hc
    exact absurd hi (not_le.mpr (h i hc))
  · rfl

/-- Above all the heights that carry a nonzero coefficient, the function is the sum of the
coefficients. -/
lemma stepFn_eq_sum (V : Fin n → ℝ) {c : Fin n → ℝ} {y : ℝ} (h : ∀ i, c i ≠ 0 → V i ≤ y) :
    stepFn V c y = ∑ i, c i := by
  unfold stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rfl
  · by_contra hc
    exact hi (h i (fun h0 => hc (by rw [h0])))

lemma finAvg_stepFn {α : Type*} [Fintype α] [Nonempty α] (V : Fin n → ℝ) (c : α → Fin n → ℝ)
    (y : ℝ) :
    finAvg (fun r => stepFn V (c r) y) = stepFn V (fun i => finAvg (fun r => c r i)) y := by
  unfold stepFn
  rw [finAvg_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · exact finAvg_const 0

/-- `Σ_i 1{p_i} x_i 1{V_i ≤ y} = Σ_{i : p_i, V_i ≤ y} x_i`: a step function whose
coefficients vanish outside a set of points is the sum of the coefficients of the points of
this set of height at most `y`. -/
lemma stepFn_ite (V x : Fin n → ℝ) (p : Fin n → Prop) [DecidablePred p] (y : ℝ) :
    stepFn V (fun i => if p i then x i else 0) y =
      ∑ i ∈ Finset.univ.filter (fun i => p i ∧ V i ≤ y), x i := by
  unfold stepFn
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : V i ≤ y <;> by_cases h2 : p i <;> simp [h1, h2]

/-! ### The local experiment -/

/-- The position of a point relative to the horizontal interval `I`. -/
inductive Side
  | left
  | inside
  | right
  deriving DecidableEq

/-- The weight `w_i` of a point in `I`: `1` to the left of `I`, `1/2` in `I`, `0` to the
right of `I`. -/
def oldWeight : Side → ℝ
  | .left => 1
  | .inside => 1 / 2
  | .right => 0

/-- The weight of a point in the child `C_{k+1}` of `I`. A point outside `I` lies on the same
side of every child. A point of `I` in the child `C_{r+1}` lies to the left of `C_{k+1}` if
`r < k`, in it if `r = k`, and to the right of it if `r > k`. -/
def childWeight {b : ℕ} (sd : Side) (r k : Fin b) : ℝ :=
  match sd with
  | .left => 1
  | .inside => if r < k then 1 else if r = k then 1 / 2 else 0
  | .right => 0

/-- The endpoint average `a(y) = Σ_i χ_i w_i 1{V_i ≤ y}` of `I`, display (2): the old
function. -/
def endpointAvg (ε V : Fin n → ℝ) (side : Fin n → Side) : ℝ → ℝ :=
  stepFn V (fun i => ε i * oldWeight (side i))

/-- The endpoint average `a_{k+1}` of the child `C_{k+1}`: a child function. -/
def childAvg {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n → Fin b)
    (k : Fin b) : ℝ → ℝ :=
  stepFn V (fun i => ε i * childWeight (side i) (r i) k)

/-- The child functions depend on the outcome only through the children of the points in
`I`. -/
lemma childAvg_congr {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) {r r' : Fin n → Fin b}
    (h : ∀ i, side i = Side.inside → r i = r' i) (k : Fin b) :
    childAvg ε V side r k = childAvg ε V side r' k := by
  funext y
  refine stepFn_congr V (fun i => ?_) y
  cases hs : side i with
  | left => simp [childWeight]
  | right => simp [childWeight]
  | inside => rw [h i hs]

/-- The points of the inner region `R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})`: the points of `I` whose
height lies in `[s + L, s + (b-1) L)`. -/
def innerPoints (b : ℕ) (V : Fin n → ℝ) (side : Fin n → Side) (s L : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => side i = Side.inside ∧ s + L ≤ V i ∧ V i < s + ((b : ℝ) - 1) * L)

/-- `R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})`: the points of the inner region are the points of `I`
whose height lies in one of the inner blocks `B_2, …, B_{b-1}` (indices `1, …, b-2` here). -/
theorem mem_innerPoints_iff {b : ℕ} (hb : 2 ≤ b) (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ)
    {L : ℝ} (hL : 0 < L) (i : Fin n) :
    i ∈ innerPoints b V side s L ↔
      side i = Side.inside ∧ V i ∈ ⋃ ℓ ∈ Finset.Ico 1 (b - 1), block s L ℓ := by
  rw [iUnion_inner_blocks s hL hb]
  simp [innerPoints]

/-! ### Step 1: averaging the children -/

/-- `ā`: the average of the child functions, `ā(y) = (1/b) Σ_k a_k(y)`. -/
def childMean {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n → Fin b) : ℝ → ℝ :=
  fun y => (∑ k : Fin b, childAvg ε V side r k y) / b

/-- "They take finitely many values": `ā` is a step function of the height, like the child
functions. -/
lemma childMean_image_finite {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side)
    (r : Fin n → Fin b) (A : Set ℝ) : ((childMean ε V side r) '' A).Finite := by
  have h : childMean ε V side r =
      stepFn V (fun i => (∑ k : Fin b, ε i * childWeight (side i) (r i) k) / b) := by
    funext y
    unfold childMean childAvg
    rw [stepFn_div, stepFn_sum]
  rw [h]
  exact stepFn_image_finite V _ A

/-- **Display (5)** for subsets `B_1, …, B_b` of a set `J` of heights for which the
inequality of Lemma 2.1 holds (hypothesis `hcomp`): for every outcome of the local
experiment,

`Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} ā + 2 |mid_{B_b} ā - mid_{B_1} ā|`.

`display_5` is the case of the blocks of an interval. -/
theorem avg_comparison_core {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (J : Set ℝ) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J)
    (hcomp : ∀ f : ℝ → ℝ, (f '' J).Finite →
      ∑ ℓ : Fin b, osc (B ℓ) f +
          2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f)
    (r : Fin n → Fin b) :
    ∑ ℓ : Fin b, osc (B ℓ) (childMean ε V side r) +
        2 * |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
          mid (B ⟨0, by omega⟩) (childMean ε V side r)| ≤
      ∑ k : Fin b, osc J (childAvg ε V side r k) := by
  have hb0 : 0 < b := by omega
  have : Nonempty (Fin b) := ⟨⟨0, hb0⟩⟩
  have hJ : J.Nonempty := (hne ⟨0, hb0⟩).mono (hsub ⟨0, hb0⟩)
  -- "By the triangle inequality for the oscillation,
  -- `Σ_k osc_J a_k ≥ osc_J (Σ_k a_k) = b osc_J ā`."
  have h1 : (b : ℝ) * osc J (childMean ε V side r) ≤
      ∑ k : Fin b, osc J (childAvg ε V side r k) := by
    have h := card_mul_osc_avg_le (ι := Fin b) (B := J)
      (f := fun k => childAvg ε V side r k) hJ (fun k => stepFn_image_finite V _ _)
    rw [Fintype.card_fin] at h
    exact h
  -- "So Lemma 2.1, applied to `f = ā`, gives" display (5)
  exact (hcomp _ (childMean_image_finite ε V side r J)).trans h1

/-- **Display (5).** "By the triangle inequality for the oscillation,
`Σ_k osc_J a_k ≥ osc_J (Σ_k a_k) = b osc_J ā`. So Lemma 2.1, applied to `f = ā`, gives"

`Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} ā + 2 |mid_{B_b} ā - mid_{B_1} ā|`,

for every outcome of the local experiment. -/
theorem display_5 {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ}
    (hL : 0 < L) (r : Fin n → Fin b) :
    ∑ ℓ : Fin b, osc (block s L ℓ) (childMean ε V side r) +
        2 * |mid (block s L (b - 1)) (childMean ε V side r) -
          mid (block s L 0) (childMean ε V side r)| ≤
      ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k) :=
  avg_comparison_core hb ε V side (Set.Ico s (s + b * L)) (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (fun ℓ => block_subset s hL ℓ.isLt)
    (fun f hf => vertical_comparison hb s hL f hf) r

/-! ### Step 2: the weights in `ā` -/

/-- "So its weight in `ā` is `((b - r) + 1/2) / b = 1/2 + (b + 1 - 2r) / (2b)`": the average
over the `b` children of the weight of a point is its old weight plus a deviation, which
vanishes for points outside `I`. -/
lemma sum_childWeight {b : ℕ} (hb : 0 < b) (sd : Side) (r : Fin b) :
    (∑ k : Fin b, childWeight sd r k) / b =
      oldWeight sd + (if sd = Side.inside then ((b : ℝ) - 1 - 2 * (r : ℕ)) / (2 * b) else 0) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  cases sd with
  | left =>
    simp only [childWeight, oldWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, reduceCtorEq, ite_false, add_zero]
    field_simp
  | right =>
    simp [childWeight, oldWeight]
  | inside =>
    simp only [childWeight, oldWeight, ite_true]
    have hsplit : ∀ k : Fin b, (if r < k then (1 : ℝ) else if r = k then 1 / 2 else 0) =
        (if r < k then (1 : ℝ) else 0) + (if r = k then 1 / 2 else 0) := by
      intro k
      by_cases h1 : r < k
      · have h2 : r ≠ k := ne_of_lt h1
        simp [h1, h2]
      · simp [h1]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ r (fun _ => (1 / 2 : ℝ)),
      ite_eq_left (Finset.mem_univ r), Finset.sum_boole]
    have hcard : (Finset.univ.filter (fun k : Fin b => r < k)).card = b - 1 - r := by
      rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    rw [hcard]
    have hr : (r : ℕ) + 1 ≤ b := r.isLt
    have hcast : ((b - 1 - (r : ℕ) : ℕ) : ℝ) = (b : ℝ) - 1 - (r : ℕ) := by
      have h : (b - 1 - (r : ℕ)) + (r : ℕ) + 1 = b := by omega
      have h' := congrArg (Nat.cast : ℕ → ℝ) h
      push_cast at h'
      linarith
    rw [hcast]
    field_simp
    ring

/-- The jump `X_i = χ_i (b + 1 - 2r) / (2b)` of a point of `I` in the child `C_r`, written
with `d = r - 1 ∈ {0, …, b-1}`: the deviation of its weight in `ā` from its old weight `1/2`,
multiplied by its color. -/
def jump (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) (d : Fin b) : ℝ :=
  ε i * (((b : ℝ) - 1 - 2 * (d : ℕ)) / (2 * b))

/-- Display (6) with its right-hand side written as one step function,
`ā(y) = Σ_i (χ_i w_i + 1{U_i ∈ I} X_i) 1{V_i ≤ y}`: the function `ā` "counts each point with
the average of its weights in the `b` children", which is its old weight for a point outside
`I` and "its old weight `1/2` plus a deviation" for a point in `I`. See `display_6` for the
manuscript's form. -/
lemma childMean_eq {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (r : Fin n → Fin b) (y : ℝ) :
    childMean ε V side r y =
      stepFn V (fun i => ε i * oldWeight (side i) +
        (if side i = Side.inside then jump b ε i (r i) else 0)) y := by
  unfold childMean childAvg
  rw [← stepFn_sum, ← stepFn_div]
  refine stepFn_congr V (fun i => ?_) y
  rw [← Finset.mul_sum, mul_div_assoc, sum_childWeight hb, mul_add]
  unfold jump
  split_ifs <;> ring

/-- **Display (6)** in the manuscript's form. "The old function `a` counts every point with
its old weight, by (2). So, for every height `y`,"

`ā(y) = a(y) + Σ_{i : U_i ∈ I, V_i ≤ y} X_i`.

"In words, `ā` follows the old function and makes an extra jump `X_i` at the height of each
point in `I`." -/
theorem display_6 {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (r : Fin n → Fin b) (y : ℝ) :
    childMean ε V side r y = endpointAvg ε V side y +
      ∑ i ∈ Finset.univ.filter (fun i => side i = Side.inside ∧ V i ≤ y), jump b ε i (r i) := by
  rw [childMean_eq hb, stepFn_add, stepFn_ite, endpointAvg]

/-- "So `b + 1 - 2r` is uniform on the symmetric set `{1 - b, 3 - b, …, b - 1}`, and the `X_i`
are independent and symmetric, whatever the colors are": reversing the order of the children
changes the sign of the jump. -/
lemma jump_rev (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) (d : Fin b) :
    jump b ε i (Fin.revPerm d) = -jump b ε i d := by
  have hd : (d : ℕ) + 1 ≤ b := d.isLt
  have hcast : (((Fin.rev d : Fin b) : ℕ) : ℝ) = (b : ℝ) - 1 - (d : ℕ) := by
    rw [Fin.val_rev]
    have h : (b - ((d : ℕ) + 1)) + (d : ℕ) + 1 = b := by omega
    have h' := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at h'
    linarith
  unfold jump
  rw [Fin.revPerm_apply, hcast]
  ring

/-- "In particular `E X_i = 0`", because the jumps are symmetric. -/
lemma finAvg_jump (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) : finAvg (jump b ε i) = 0 :=
  finAvg_eq_zero_of_symm Fin.revPerm (jump b ε i) (jump_rev b ε i)

/-- **Display (7)**: "In particular `E X_i = 0`, and (6) gives"

`E ā(y) = a(y)` "for every height `y`". -/
lemma finAvg_childMean {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side) (y : ℝ) :
    finAvg (fun r : Fin n → Fin b => childMean ε V side r y) = endpointAvg ε V side y := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  simp_rw [childMean_eq hb]
  rw [finAvg_stepFn]
  unfold endpointAvg
  refine stepFn_congr V (fun i => ?_) y
  rw [finAvg_add, finAvg_const]
  by_cases hs : side i = Side.inside
  · -- the jump of a point in `I` has expectation zero
    simp only [hs, ite_true]
    rw [finAvg_coord i (jump b ε i), finAvg_jump, add_zero]
  · simp only [hs, ite_false]
    rw [finAvg_const, add_zero]

/-! ### Step 3: taking expectations -/

/-- "The expectation of a maximum is at least the maximum of the expectations": by display
(7), `E max_B ā ≥ max_B a` for every nonempty set `B` of heights. -/
lemma maxOn_endpointAvg_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) :
    maxOn B (endpointAvg ε V side) ≤
      finAvg (fun r : Fin n → Fin b => maxOn B (childMean ε V side r)) := by
  apply maxOn_le hB
  intro y hy
  rw [← finAvg_childMean hb ε V side y]
  exact finAvg_mono fun r => le_maxOn (childMean_image_finite ε V side r B) hy

/-- "\[…\] and the expectation of a minimum is at most the minimum of the expectations": by
display (7), `E min_B ā ≤ min_B a` for every nonempty set `B` of heights. -/
lemma finAvg_minOn_childMean_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) :
    finAvg (fun r : Fin n → Fin b => minOn B (childMean ε V side r)) ≤
      minOn B (endpointAvg ε V side) := by
  apply le_minOn hB
  intro y hy
  rw [← finAvg_childMean hb ε V side y]
  exact finAvg_mono fun r => minOn_le (childMean_image_finite ε V side r B) hy

/-- "So (7) gives, for every `ℓ`,"

`E osc_{B_ℓ} ā = E max_{B_ℓ} ā - E min_{B_ℓ} ā ≥ max_{B_ℓ} a - min_{B_ℓ} a = osc_{B_ℓ} a`,

here for every nonempty set `B` of heights in place of `B_ℓ`. -/
lemma osc_endpointAvg_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) :
    osc B (endpointAvg ε V side) ≤
      finAvg (fun r : Fin n → Fin b => osc B (childMean ε V side r)) := by
  have hmax := maxOn_endpointAvg_le hb ε V side hB
  have hmin := finAvg_minOn_childMean_le hb ε V side hB
  unfold osc
  rw [finAvg_sub]
  linarith

/-- **Display (8)** for subsets `B_1, …, B_b` of a set `J` of heights for which the
inequality of Lemma 2.1 holds (hypothesis `hcomp`):

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + 2 E|mid_{B_b} ā - mid_{B_1} ā|`.

`display_8` is the case of the blocks of an interval. -/
theorem expected_comparison_core {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (J : Set ℝ) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J)
    (hcomp : ∀ f : ℝ → ℝ, (f '' J).Finite →
      ∑ ℓ : Fin b, osc (B ℓ) f +
          2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f) :
    ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) +
        2 * finAvg (fun r : Fin n → Fin b =>
          |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
            mid (B ⟨0, by omega⟩) (childMean ε V side r)|) ≤
      finAvg (fun r : Fin n → Fin b => ∑ k : Fin b, osc J (childAvg ε V side r k)) := by
  have hb0 : 0 < b := by omega
  -- "Taking expectations in (5)"
  have hE := finAvg_mono (avg_comparison_core hb ε V side J B hne hsub hcomp)
  rw [finAvg_add, finAvg_sum, finAvg_const_mul] at hE
  -- `E osc_{B_ℓ} ā ≥ osc_{B_ℓ} a` for every `ℓ`
  have hblocks : ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) ≤
      ∑ ℓ : Fin b, finAvg (fun r : Fin n → Fin b => osc (B ℓ) (childMean ε V side r)) :=
    Finset.sum_le_sum fun ℓ _ => osc_endpointAvg_le hb0 ε V side (hne ℓ)
  linarith

/-- **Display (8).** "Taking expectations in (5), we get"

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + 2 E|mid_{B_b} ā - mid_{B_1} ā|`.

"The first term on the right is what the horizontal strips had. The second term is the
gain." -/
theorem display_8 {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ}
    (hL : 0 < L) :
    ∑ ℓ : Fin b, osc (block s L ℓ) (endpointAvg ε V side) +
        2 * finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
          mid (block s L 0) (childMean ε V side r)|) ≤
      finAvg (fun r : Fin n → Fin b =>
        ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k)) :=
  expected_comparison_core hb ε V side (Set.Ico s (s + b * L)) (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (fun ℓ => block_subset s hL ℓ.isLt)
    (fun f hf => vertical_comparison hb s hL f hf)

/-! ### Step 4: the gain

In the manuscript `D` is the sum of the jumps of the points of `R^in`, and `g` is `ā` without
these jumps. In the statements below a set `S` of points of `I` takes the place of the set of
the points of `R^in`: `D = jumpSum S (jump b ε) r` (`jumpSum` is defined in
`SymmetricSums.lean`) and `g = withoutJumps b ε V side S r`. -/

/-- `g`: "the function `ā` without these jumps", the jumps of the points of `S`. Like `ā` in
`childMean_eq`, it is written as one step function; see `withoutJumps_eq` for the
manuscript's form. -/
def withoutJumps (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side) (S : Finset (Fin n))
    (r : Fin n → Fin b) : ℝ → ℝ :=
  stepFn V (fun i => ε i * oldWeight (side i) +
    (if side i = Side.inside ∧ i ∉ S then jump b ε i (r i) else 0))

/-- The display that defines `g`, with `S` in place of the set of the points of `R^in`:
`g(y) = a(y) + Σ_{i : U_i ∈ I, P_i ∉ R^in, V_i ≤ y} X_i`. -/
lemma withoutJumps_eq (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side) (S : Finset (Fin n))
    (r : Fin n → Fin b) (y : ℝ) :
    withoutJumps b ε V side S r y = endpointAvg ε V side y +
      ∑ i ∈ Finset.univ.filter (fun i => side i = Side.inside ∧ i ∉ S ∧ V i ≤ y),
        jump b ε i (r i) := by
  unfold withoutJumps endpointAvg
  rw [stepFn_add, stepFn_ite]
  congr 1
  exact Finset.sum_congr (Finset.filter_congr fun i _ => and_assoc) fun _ _ => rfl

/-- "They take finitely many values": `g` is a step function of the height. -/
lemma withoutJumps_image_finite (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (S : Finset (Fin n)) (r : Fin n → Fin b) (A : Set ℝ) :
    ((withoutJumps b ε V side S r) '' A).Finite :=
  stepFn_image_finite V _ A

/-- "The heights of the points of `R^in` lie above `B_1` and below `B_b`": above every
height of the bottom block `B_1 = block s L 0`, and at or below every height of the top block
`B_b = block s L (b - 1)`. -/
lemma innerPoints_between_blocks {b : ℕ} (hb : 2 ≤ b) (V : Fin n → ℝ) (side : Fin n → Side)
    (s L : ℝ) :
    ∀ i ∈ innerPoints b V side s L, side i = Side.inside ∧
      (∀ y ∈ block s L 0, y < V i) ∧ (∀ y ∈ block s L (b - 1), V i ≤ y) := by
  intro i hi
  have hi' : side i = Side.inside ∧ s + L ≤ V i ∧ V i < s + ((b : ℝ) - 1) * L := by
    simpa [innerPoints] using hi
  refine ⟨hi'.1, fun y hy => ?_, fun y hy => ?_⟩
  · have h2 : y < s + ((0 : ℕ) + 1 : ℝ) * L := hy.2
    simp only [Nat.cast_zero, zero_add, one_mul] at h2
    linarith [hi'.2.1]
  · have h2 : s + ((b - 1 : ℕ) : ℝ) * L ≤ y := hy.1
    rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one] at h2
    linarith [hi'.2.2]

/-- By display (6), `ā` is `g` plus the jumps of the points of `S`, for every set `S` of
points of `I`: `ā(y) = g(y) + Σ_{i ∈ S, V_i ≤ y} X_i`, where the last sum is written as a
step function. -/
lemma childMean_eq_withoutJumps_add {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ)
    (side : Fin n → Side) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside)
    (r : Fin n → Fin b) (y : ℝ) :
    childMean ε V side r y = withoutJumps b ε V side S r y +
      stepFn V (fun i => if i ∈ S then jump b ε i (r i) else 0) y := by
  rw [childMean_eq hb]
  unfold withoutJumps
  rw [← stepFn_add]
  refine stepFn_congr V (fun i => ?_) y
  by_cases hi : i ∈ S
  · simp [hi, hS i hi]
  · simp [hi]

/-- "So by (6), their jumps do not enter `ā` on `B_1`": `ā(y) = g(y)` at every height `y`
below the heights of the points of `S`. -/
lemma childMean_eq_withoutJumps_of_lt {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ)
    (side : Fin n → Side) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside)
    (r : Fin n → Fin b) {y : ℝ} (hy : ∀ i ∈ S, y < V i) :
    childMean ε V side r y = withoutJumps b ε V side S r y := by
  rw [childMean_eq_withoutJumps_add hb ε V side S hS, stepFn_eq_zero, add_zero]
  exact fun i hi => hy i (ite_ne_right_iff.mp hi).1

/-- "\[…\] and they add the constant `D` to `ā` on `B_b`": `ā(y) = g(y) + D` at every height
`y` at or above the heights of the points of `S`. -/
lemma childMean_eq_withoutJumps_add_jumpSum_of_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ)
    (side : Fin n → Side) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside)
    (r : Fin n → Fin b) {y : ℝ} (hy : ∀ i ∈ S, V i ≤ y) :
    childMean ε V side r y = withoutJumps b ε V side S r y + jumpSum S (jump b ε) r := by
  rw [childMean_eq_withoutJumps_add hb ε V side S hS, stepFn_eq_sum]
  · rw [Finset.sum_ite_mem, Finset.univ_inter, jumpSum]
  · exact fun i hi => hy i (ite_ne_right_iff.mp hi).1

/-- "`mid_{B_b} ā - mid_{B_1} ā = θ + D`, where `θ = mid_{B_b} g - mid_{B_1} g`", for
nonempty sets `B_1, …, B_b` of heights and any set `S` of points of `I` whose heights lie
above all of `B_1` and at or below all of `B_b`. `offset_eq` is the case of the blocks of an
interval and the points of `R^in`. -/
theorem offset_core {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧
      (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y))
    (r : Fin n → Fin b) :
    mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
        mid (B ⟨0, by omega⟩) (childMean ε V side r) =
      (mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
        mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r)) +
      jumpSum S (jump b ε) r := by
  have hb0 : 0 < b := by omega
  have hI : ∀ i ∈ S, side i = Side.inside := fun i hi => (hS i hi).1
  -- "That is, `ā = g` on `B_1` and `ā = g + D` on `B_b`."
  have hbot : ∀ y ∈ B ⟨0, by omega⟩,
      childMean ε V side r y = withoutJumps b ε V side S r y := fun y hy =>
    childMean_eq_withoutJumps_of_lt hb0 ε V side S hI r fun i hi => (hS i hi).2.1 y hy
  have htop : ∀ y ∈ B ⟨b - 1, by omega⟩,
      childMean ε V side r y = withoutJumps b ε V side S r y + jumpSum S (jump b ε) r :=
    fun y hy => childMean_eq_withoutJumps_add_jumpSum_of_le hb0 ε V side S hI r
      fun i hi => (hS i hi).2.2 y hy
  -- "Adding the constant `D` to a function adds `D` to its midpoint"
  rw [mid_congr hbot, mid_congr htop,
    mid_add_const (hne _) (withoutJumps_image_finite b ε V side S r _)]
  ring

/-- "Adding the constant `D` to a function adds `D` to its midpoint, so"

`mid_{B_b} ā - mid_{B_1} ā = θ + D`, "where `θ = mid_{B_b} g - mid_{B_1} g`".

Here `D = jumpSum (innerPoints b V side s L) (jump b ε) r` is the sum of the jumps of the
points of `R^in`, and `g = withoutJumps b ε V side (innerPoints b V side s L) r`. -/
theorem offset_eq {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ}
    (hL : 0 < L) (r : Fin n → Fin b) :
    mid (block s L (b - 1)) (childMean ε V side r) - mid (block s L 0) (childMean ε V side r) =
      (mid (block s L (b - 1)) (withoutJumps b ε V side (innerPoints b V side s L) r) -
        mid (block s L 0) (withoutJumps b ε V side (innerPoints b V side s L) r)) +
      jumpSum (innerPoints b V side s L) (jump b ε) r :=
  offset_core hb ε V side (fun ℓ : Fin b => block s L ℓ) (fun ℓ => block_nonempty s hL ℓ)
    (innerPoints b V side s L) (innerPoints_between_blocks hb V side s L) r

/-- "Now condition on the children of all other points in `I` \[…\]. This fixes the function
`g`": `g` depends on the outcome only through the children of the points of `I` that are
not in `S`. -/
lemma withoutJumps_congr (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side) (S : Finset (Fin n))
    {r r' : Fin n → Fin b} (h : ∀ i, side i = Side.inside → i ∉ S → r i = r' i) :
    withoutJumps b ε V side S r = withoutJumps b ε V side S r' := by
  funext y
  refine stepFn_congr V (fun i => ?_) y
  by_cases hi : side i = Side.inside ∧ i ∉ S
  · rw [h i hi.1 hi.2]
  · simp [hi]

/-! ### Step 4: the moments of the jumps

"By definition, `X_i² = (r - (b+1)/2)² / b²` with `r` uniform on `{1, …, b}`. Here `r` has
mean `(b+1)/2` and second moment `(b+1)(2b+1)/6`, so its variance is
`(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12`. Also `|X_i| ≤ (b-1)/(2b)`." These sentences are
`jump_sq_eq`, then `finAvg_childIndex`, `finAvg_childIndex_sq` and `finAvg_childIndex_var`,
then `abs_jump_le`. In this file the digit `d = r - 1` is uniform on `{0, …, b-1}`, and the
index `r` of the child is written `d + 1`.

The display that follows these sentences,

`E X_i² = (b²-1)/(12b²) =: σ²`,   `E X_i⁴ ≤ ((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴`,

is `finAvg_jump_sq`, then `finAvg_jump_fourth_le_sq` (the first inequality of the chain) and
`sq_mul_sigma_sq_le` (its second inequality and its equality). `finAvg_jump_fourth_le` is
the inequality between the two ends of the chain.

`sum_centered_sq` is the same variance written with the digit `d`:
`X_i² = (b - 1 - 2d)² / (4b²)`, and `(1/b) Σ_d (b - 1 - 2d)² / 4 = (b² - 1) / 12`. The proofs
below do not use it. -/

/-- `Σ_{d=0}^{N-1} d = N (N - 1) / 2`. -/
lemma sum_range_id_real (N : ℕ) : ∑ d ∈ Finset.range N, (d : ℝ) = (N : ℝ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `Σ_{d=0}^{N-1} d² = N (N - 1) (2N - 1) / 6`. -/
lemma sum_range_sq_real (N : ℕ) :
    ∑ d ∈ Finset.range N, (d : ℝ) ^ 2 = (N : ℝ) * (N - 1) * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `Σ_{d=0}^{b-1} (b - 1 - 2d)² = b (b² - 1) / 3`: the variance of a uniform digit is
`(b² - 1) / 12`. -/
lemma sum_centered_sq (b : ℕ) :
    ∑ d : Fin b, ((b : ℝ) - 1 - 2 * (d : ℕ)) ^ 2 = (b : ℝ) * ((b : ℝ) ^ 2 - 1) / 3 := by
  rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => ((b : ℝ) - 1 - 2 * (d : ℝ)) ^ 2) b]
  have hexp : ∀ d : ℕ, ((b : ℝ) - 1 - 2 * (d : ℝ)) ^ 2 =
      ((b : ℝ) - 1) ^ 2 - 4 * ((b : ℝ) - 1) * (d : ℝ) + 4 * (d : ℝ) ^ 2 := fun d => by ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_range_id_real, sum_range_sq_real]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- "By definition, `X_i² = (r - (b+1)/2)² / b²`", where `r = d + 1` is the index of the
child: the jump is `X_i = χ_i (b + 1 - 2r) / (2b)`, and `χ_i² = 1`. That `r` is uniform on
`{1, …, b}` is expressed in the next lemmas by the average `finAvg` over the digit `d`. -/
lemma jump_sq_eq {b : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n) (d : Fin b) :
    jump b ε i d ^ 2 = ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2 / (b : ℝ) ^ 2 := by
  have hε2 : ε i ^ 2 = 1 := by rw [← sq_abs, hε i]; norm_num
  unfold jump
  rw [mul_pow, hε2]
  ring

/-- "Here `r` has mean `(b+1)/2`": the mean of the index `r = d + 1` of the child. -/
lemma finAvg_childIndex {b : ℕ} (hb : 0 < b) :
    finAvg (fun d : Fin b => ((d : ℕ) : ℝ) + 1) = ((b : ℝ) + 1) / 2 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  -- `Σ_{r=1}^{b} r = Σ_{r=0}^{b} r = b (b + 1) / 2`
  have hsum : ∑ d : Fin b, (((d : ℕ) : ℝ) + 1) = (b : ℝ) * ((b : ℝ) + 1) / 2 := by
    have h := sum_range_id_real (b + 1)
    rw [Finset.sum_range_succ'] at h
    push_cast at h
    rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => (d : ℝ) + 1) b]
    linarith
  -- divide by the number `b` of children
  unfold finAvg
  rw [hsum, Fintype.card_fin]
  field_simp

/-- "\[…\] and second moment `(b+1)(2b+1)/6`": the mean of `r²` for the index `r = d + 1` of
the child. -/
lemma finAvg_childIndex_sq {b : ℕ} (hb : 0 < b) :
    finAvg (fun d : Fin b => (((d : ℕ) : ℝ) + 1) ^ 2) = ((b : ℝ) + 1) * (2 * b + 1) / 6 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  -- `Σ_{r=1}^{b} r² = Σ_{r=0}^{b} r² = b (b + 1) (2b + 1) / 6`
  have hsum : ∑ d : Fin b, (((d : ℕ) : ℝ) + 1) ^ 2 =
      (b : ℝ) * ((b : ℝ) + 1) * (2 * b + 1) / 6 := by
    have h := sum_range_sq_real (b + 1)
    rw [Finset.sum_range_succ'] at h
    push_cast at h
    rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => ((d : ℝ) + 1) ^ 2) b]
    linarith
  -- divide by the number `b` of children
  unfold finAvg
  rw [hsum, Fintype.card_fin]
  field_simp

/-- "\[…\] so its variance is `(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12`": the variance of the
index `r = d + 1` of the child is its second moment minus the square of its mean (the first
equality), and this number is `(b² - 1) / 12` (the second equality). -/
lemma finAvg_childIndex_var {b : ℕ} (hb : 0 < b) :
    finAvg (fun d : Fin b => ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2) =
        ((b : ℝ) + 1) * (2 * b + 1) / 6 - ((b : ℝ) + 1) ^ 2 / 4 ∧
      ((b : ℝ) + 1) * (2 * b + 1) / 6 - ((b : ℝ) + 1) ^ 2 / 4 = ((b : ℝ) ^ 2 - 1) / 12 := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  refine ⟨?_, by ring⟩
  -- `(r - μ)² = r² - 2μ r + μ²` for the mean `μ = (b+1)/2`
  have hexp : ∀ d : Fin b, ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2 =
      (((d : ℕ) : ℝ) + 1) ^ 2 - ((b : ℝ) + 1) * (((d : ℕ) : ℝ) + 1) + ((b : ℝ) + 1) ^ 2 / 4 :=
    fun d => by ring
  -- take expectations, and use the mean and the second moment of `r`
  rw [finAvg_congr hexp, finAvg_add, finAvg_sub, finAvg_const_mul, finAvg_const,
    finAvg_childIndex_sq hb, finAvg_childIndex hb]
  ring

/-- `E X_i² = (b² - 1) / (12 b²) =: σ²`, the first formula of the display on the moments of
the jumps: `X_i² = (r - (b+1)/2)² / b²` (`jump_sq_eq`), and the variance of `r` is
`(b² - 1) / 12` (`finAvg_childIndex_var`). -/
lemma finAvg_jump_sq {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n) :
    finAvg (fun d : Fin b => jump b ε i d ^ 2) = ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := by
  -- "By definition, `X_i² = (r - (b+1)/2)² / b²` with `r` uniform on `{1, …, b}`."
  rw [finAvg_congr (jump_sq_eq ε hε i), finAvg_div_const]
  -- the variance of `r` is `(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12`
  rw [(finAvg_childIndex_var hb).1, (finAvg_childIndex_var hb).2, div_div]

/-- `|X_i| ≤ (b - 1) / (2b)`. -/
lemma abs_jump_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n)
    (d : Fin b) : |jump b ε i d| ≤ ((b : ℝ) - 1) / (2 * b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hd0 : (0 : ℝ) ≤ (d : ℕ) := Nat.cast_nonneg _
  have hd1 : ((d : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast d.isLt
  unfold jump
  rw [abs_mul, hε i, one_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * b)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [abs_le]
  constructor <;> linarith

/-- The first inequality of the chain for the fourth moment, `E X_i⁴ ≤ ((b-1)/(2b))² σ²`,
where `σ² = (b² - 1) / (12 b²)`: `X_i⁴ ≤ ((b-1)/(2b))² X_i²` because `|X_i| ≤ (b-1)/(2b)`
(`abs_jump_le`), and `E X_i² = σ²` (`finAvg_jump_sq`). -/
lemma finAvg_jump_fourth_le_sq {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (i : Fin n) :
    finAvg (fun d : Fin b => jump b ε i d ^ 4) ≤
      (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) := by
  -- `X_i⁴ ≤ ((b-1)/(2b))² X_i²`, because `|X_i| ≤ (b-1)/(2b)`
  have hpt : ∀ d : Fin b, jump b ε i d ^ 4 ≤
      (((b : ℝ) - 1) / (2 * b)) ^ 2 * jump b ε i d ^ 2 := by
    intro d
    have h1 : jump b ε i d ^ 2 ≤ (((b : ℝ) - 1) / (2 * b)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_jump_le hb ε hε i d) 2
    have h2 : (0 : ℝ) ≤ jump b ε i d ^ 2 := sq_nonneg _
    calc jump b ε i d ^ 4 = jump b ε i d ^ 2 * jump b ε i d ^ 2 := by ring
      _ ≤ (((b : ℝ) - 1) / (2 * b)) ^ 2 * jump b ε i d ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h2
  -- take expectations, and use `E X_i² = σ²`
  calc finAvg (fun d : Fin b => jump b ε i d ^ 4)
      ≤ finAvg (fun d : Fin b => (((b : ℝ) - 1) / (2 * b)) ^ 2 * jump b ε i d ^ 2) :=
        finAvg_mono hpt
    _ = (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) := by
        rw [finAvg_const_mul, finAvg_jump_sq hb ε hε i]

/-- The rest of the chain for the fourth moment,
`((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴`, where `σ² = (b² - 1) / (12 b²)`. The
inequality holds because `(b - 1)² ≤ b² - 1` for `b ≥ 1` and `σ² ≥ 0`, and the equality
because `(b² - 1) / (4b²) = 3σ²`. -/
lemma sq_mul_sigma_sq_le {b : ℕ} (hb : 0 < b) :
    (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ≤
        ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ∧
      ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) =
        3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  refine ⟨?_, by ring⟩
  -- `σ² ≥ 0`
  have hs : (0 : ℝ) ≤ ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  -- `((b-1)/(2b))² ≤ (b²-1)/(4b²)`, because `(b - 1)² ≤ b² - 1` for `b ≥ 1`
  have hk : (((b : ℝ) - 1) / (2 * b)) ^ 2 ≤ ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) := by
    rw [div_pow, show (2 * (b : ℝ)) ^ 2 = 4 * (b : ℝ) ^ 2 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  exact mul_le_mul_of_nonneg_right hk hs

/-- `E X_i⁴ ≤ 3σ⁴`, where `σ² = (b² - 1) / (12 b²)`: the inequality between the two ends of
the chain `E X_i⁴ ≤ ((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴`, whose links are
`finAvg_jump_fourth_le_sq` and `sq_mul_sigma_sq_le`. This is the fourth-moment hypothesis of
Fact 2.2. -/
lemma finAvg_jump_fourth_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (i : Fin n) :
    finAvg (fun d : Fin b => jump b ε i d ^ 4) ≤
      3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 :=
  calc finAvg (fun d : Fin b => jump b ε i d ^ 4)
      ≤ (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) :=
        finAvg_jump_fourth_le_sq hb ε hε i
    _ ≤ ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) :=
        (sq_mul_sigma_sq_le hb).1
    _ = 3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 := (sq_mul_sigma_sq_le hb).2

/-! ### Step 4: the last display

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b²-1) / (6b)) √(m_R) ≥ √(m_R) / 8`,

where `σ² = (b² - 1) / (12 b²)`. The first inequality is `expected_offset_ge_sigma`, the
equality is `sigma_mul_sqrt_eq`, the last inequality is `sqrt_sq_sub_one_div_ge`, and
`expected_offset_ge` is the inequality between the two ends of the display.
`sqrt_div_eight_le` is the equality and the last inequality together. -/

/-- The equality of the last display, `σ √(m/3) = (√(b² - 1) / (6b)) √m`, where
`σ² = (b² - 1) / (12 b²)`. -/
lemma sigma_mul_sqrt_eq {b : ℕ} (hb : 0 < b) (m : ℕ) :
    Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (m / 3) =
      Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hnum : (0 : ℝ) ≤ (b : ℝ) ^ 2 - 1 := by nlinarith
  -- `√(12 b²) √3 = √(36 b²) = 6b`
  have h6 : Real.sqrt (12 * (b : ℝ) ^ 2) * Real.sqrt 3 = 6 * b := by
    rw [← Real.sqrt_mul (by positivity), show 12 * (b : ℝ) ^ 2 * 3 = (6 * b) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  -- `σ = √(b² - 1) / √(12 b²)` and `√(m/3) = √m / √3`
  rw [Real.sqrt_div hnum, Real.sqrt_div (Nat.cast_nonneg m), div_mul_div_comm, h6]
  ring

/-- The last inequality of the last display, `(√(b² - 1) / (6b)) √m ≥ √m / 8`, "because
`16 (b² - 1) ≥ 9 b²` for `b ≥ 2`". -/
lemma sqrt_sq_sub_one_div_ge {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    Real.sqrt m / 8 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  -- "because `16 (b² - 1) ≥ 9 b²` for `b ≥ 2`"
  have h16 : 9 * (b : ℝ) ^ 2 ≤ 16 * ((b : ℝ) ^ 2 - 1) := by nlinarith
  -- so `3b/4 ≤ √(b² - 1)`, that is, `1/8 ≤ √(b² - 1) / (6b)`
  have h34 : 3 * (b : ℝ) / 4 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) := by
    apply Real.le_sqrt_of_sq_le
    linarith [show (3 * (b : ℝ) / 4) ^ 2 = 9 * (b : ℝ) ^ 2 / 16 by ring]
  have hc : (1 : ℝ) / 8 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- multiply by `√m ≥ 0`
  calc Real.sqrt m / 8 = 1 / 8 * Real.sqrt m := by ring
    _ ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m :=
        mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)

/-- `σ √(m/3) ≥ √m / 8` for `σ² = (b² - 1) / (12 b²)` and `b ≥ 2`: the equality and the last
inequality of the last display together (`sigma_mul_sqrt_eq`, `sqrt_sq_sub_one_div_ge`). -/
lemma sqrt_div_eight_le {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    Real.sqrt m / 8 ≤
      Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (m / 3) := by
  -- `σ √(m/3) = (√(b² - 1) / (6b)) √m`
  rw [sigma_mul_sqrt_eq (by omega) m]
  -- `(√(b² - 1) / (6b)) √m ≥ √m / 8`
  exact sqrt_sq_sub_one_div_ge hb m

/-- The first inequality of the last display, `E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m/3)` with
`σ² = (b² - 1) / (12 b²)`, for nonempty sets `B_1, …, B_b` of heights and any set `S` of `m`
points of `I` whose heights lie above all of `B_1` and at or below all of `B_b`. Fact 2.2
(`symmetric_sum_abs`) is applied to the jumps of the points of `S`.
`expected_offset_ge_sigma` is the case of the blocks of an interval and the points of
`R^in`. -/
theorem expected_offset_core_sigma {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty)
    (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧
      (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y)) :
    Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (S.card / 3) ≤
      finAvg (fun r : Fin n → Fin b =>
        |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
          mid (B ⟨0, by omega⟩) (childMean ε V side r)|) := by
  have hb0 : 0 < b := by omega
  have : Nonempty (Fin b) := ⟨⟨0, hb0⟩⟩
  -- `σ² = (b² - 1) / (12 b²)`
  have hs2 : (0 : ℝ) ≤ ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := by
    apply div_nonneg _ (by positivity)
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb0
    nlinarith
  have hσ2 : Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 =
      ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := Real.sq_sqrt hs2
  have hσ4 : Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 4 =
      (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hσ2]
  -- "This fixes the function `g`, and hence the number `θ`."
  have hθ : ∀ r r' : Fin n → Fin b, (∀ i, i ∉ S → r i = r' i) →
      mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r) =
        mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r') -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r') := by
    intro r r' h
    rw [withoutJumps_congr b ε V side S fun i _ hi => h i hi]
  -- "So Fact 2.2 applies to `θ + D`, with `m = m_R`. Its bound holds for every `θ`, so the
  -- children of the other points cannot reduce it": `E|θ + D| ≥ σ √(m/3)`
  have hF : Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (S.card / 3) ≤
      finAvg (fun r : Fin n → Fin b =>
        |mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r) + jumpSum S (jump b ε) r|) :=
    symmetric_sum_abs S (jump b ε) (fun _ => Fin.revPerm)
      (fun i _ d => jump_rev b ε i d) (Real.sqrt_nonneg _)
      (fun i _ => by rw [hσ2]; exact finAvg_jump_sq hb0 ε hε i)
      (fun i _ => by rw [hσ4]; exact finAvg_jump_fourth_le hb0 ε hε i)
      (fun r => mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
        mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r)) hθ
  -- `mid_{B_b} ā - mid_{B_1} ā = θ + D`
  rw [finAvg_congr fun r => congrArg abs (offset_core hb ε V side B hne S hS r)]
  exact hF

/-- The inequality between the two ends of the last display,
`E|mid_{B_b} ā - mid_{B_1} ā| ≥ √m / 8`, for nonempty sets `B_1, …, B_b` of heights and any
set `S` of `m` points of `I` whose heights lie above all of `B_1` and at or below all of
`B_b`. It follows from the first inequality of the display in this generality
(`expected_offset_core_sigma`) by `sqrt_div_eight_le`, and it is used for `local_gain_core`.
`expected_offset_ge` is the same inequality for the blocks of an interval and the points of
`R^in`. -/
theorem expected_offset_core {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty)
    (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧
      (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y)) :
    Real.sqrt S.card / 8 ≤
      finAvg (fun r : Fin n → Fin b =>
        |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
          mid (B ⟨0, by omega⟩) (childMean ε V side r)|) :=
  (sqrt_div_eight_le hb S.card).trans (expected_offset_core_sigma hb ε hε V side B hne S hS)

/-- "So Fact 2.2 applies to `θ + D`, with `m = m_R`. Its bound holds for every `θ`, so the
children of the other points cannot reduce it. Conditionally, and hence also without the
conditioning,"

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3)`,

where `σ² = (b² - 1) / (12 b²)`: the first inequality of the last display. -/
theorem expected_offset_ge_sigma {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L) :
    Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) *
        Real.sqrt ((innerPoints b V side s L).card / 3) ≤
      finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
        mid (block s L 0) (childMean ε V side r)|) :=
  expected_offset_core_sigma hb ε hε V side (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (innerPoints b V side s L)
    (innerPoints_between_blocks hb V side s L)

/-- The last display of the proof,

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b² - 1) / (6b)) √(m_R) ≥ √(m_R) / 8`,

"because `16 (b² - 1) ≥ 9 b²` for `b ≥ 2`." The statement is the inequality between the two
ends of this display. The first inequality of the display is `expected_offset_ge_sigma`; its
equality and its last inequality are `sigma_mul_sqrt_eq` and `sqrt_sq_sub_one_div_ge`, which
together are `sqrt_div_eight_le`. -/
theorem expected_offset_ge {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L) :
    Real.sqrt (innerPoints b V side s L).card / 8 ≤
      finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
        mid (block s L 0) (childMean ε V side r)|) :=
  (sqrt_div_eight_le hb (innerPoints b V side s L).card).trans
    (expected_offset_ge_sigma hb ε hε V side s hL)

/-! ### Lemma 2.3 -/

/-- **Lemma 2.3** for subsets `B_1, …, B_b` of a set `J` of heights for which the inequality
of Lemma 2.1 holds (hypothesis `hcomp`), and for any set `S` of points of `I` whose heights
lie above all of `B_1` and at or below all of `B_b`:

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + (1/4) √|S|`.

The proof is the last sentence of the manuscript's proof, with display (8) in the form
`expected_comparison_core` (Steps 1–3) and the last display in the form
`expected_offset_core` (Step 4). `local_gain` is the case of the blocks of an interval. -/
theorem local_gain_core {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (J : Set ℝ) (B : Fin b → Set ℝ)
    (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧
      (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y))
    (hcomp : ∀ f : ℝ → ℝ, (f '' J).Finite →
      ∑ ℓ : Fin b, osc (B ℓ) f +
          2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f) :
    ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) + (1 / 4) * Real.sqrt S.card ≤
      finAvg (fun r : Fin n → Fin b => ∑ k : Fin b, osc J (childAvg ε V side r k)) := by
  have h8 := expected_comparison_core hb ε V side J B hne hsub hcomp
  have h4 := expected_offset_core hb ε hε V side B hne S hS
  -- "Together with (8), this proves the inequality of the lemma."
  linarith

/-- Lemma 2.3 for arbitrary nonempty subsets `B_1, …, B_b` of a set `J` of heights in place
of the blocks of an interval (for instance heights sampled on a finite grid, as in
`GridDrift.lean`). -/
theorem local_gain_sets {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (J : Set ℝ) (B : Fin b → Set ℝ)
    (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧
      (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y)) :
    ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) + (1 / 4) * Real.sqrt S.card ≤
      finAvg (fun r : Fin n → Fin b => ∑ k : Fin b, osc J (childAvg ε V side r k)) :=
  local_gain_core hb ε hε V side J B hne hsub S hS
    fun f hf => vertical_comparison_sets hb J B hne hsub f hf

/-- **Lemma 2.3 (local gain).** In the local experiment,

`E Σ_{k=1}^{b} osc_J a_k ≥ Σ_{ℓ=1}^{b} osc_{B_ℓ} a + (1/4) √(m_R)`,

for every integer `b ≥ 2` (the manuscript has `b ≥ 3`), all colors, all heights (ties
allowed), and all positions relative to `I`. The proof is the last sentence of the
manuscript's proof: it combines display (8) (`display_8`: Steps 1–3, with Lemma 2.1) and the
last display (`expected_offset_ge`: Step 4, with Fact 2.2). -/
theorem local_gain {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L) :
    ∑ ℓ : Fin b, osc (block s L ℓ) (endpointAvg ε V side) +
        (1 / 4) * Real.sqrt (innerPoints b V side s L).card ≤
      finAvg (fun r : Fin n → Fin b =>
        ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k)) := by
  have h8 := display_8 hb ε V side s hL
  have h4 := expected_offset_ge hb ε hε V side s hL
  -- "Together with (8), this proves the inequality of the lemma."
  linarith

end

end R56Audit
