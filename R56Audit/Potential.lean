import Oscillation
import R56Audit.SupNorm
import R56Audit.EndpointAverage
import R56Audit.StepOsc

/-!
# The potential `Z_j` of the manuscript (display (1)), with heights in the continuum

Auditor's supplement (not part of the audited archive).

Section 2.4: fix `h ≥ 1` and `M = b^{h-1}`. "At stage `j`, `0 ≤ j ≤ h`, cut `[0,1]`
horizontally into `b^j` intervals of length `b^{-j}`, and vertically into `b^{h-j}` intervals
of length `b^{j-h}`. Their products are the cells of stage `j`. \[…\] the potential is

`Z_j = (1 / (bM)) Σ_{stage-j cells I × B} osc_B a^{(I)}`",

where `a^{(I)}(y) = (F(I⁻, y) + F(I⁺, y)) / 2` is the endpoint average of `I = [I⁻, I⁺]`, the
vertical intervals are closed at the bottom and open at the top, and `osc_B` is the
oscillation over all heights `y ∈ B`.

| Manuscript | Here |
| --- | --- |
| length `b^{j-h}` of a vertical interval of stage `j` | `vlen b h j` |
| the `v`-th vertical interval `[v b^{j-h}, (v+1) b^{j-h})` of stage `j` | `vcell b h j v` |
| the `c`-th horizontal interval `[c b^{-j}, (c+1) b^{-j}]` of stage `j` | its endpoints |
| endpoint average `a^{(I)}`, display (2) | `endAvg χ P I⁻ I⁺` |
| the potential `Z_j`, display (1) | `Zpot χ b h j P` |

`Zpot` is the definition of the manuscript, word for word, for the function `F_χ` of
`Notation.lean`. Its extrema are over the continuum of heights of each cell; nothing is
sampled.

For the proofs it is convenient to read the potential from the heights and from the index of
the stage-`j` horizontal interval that contains each point (`Zstep`): for points with
nonnegative coordinates the two agree (`Zpot_eq_Zstep`). The index is
`Riesz.gridIndex (b^j) u = ⌈b^j u⌉ - 1`, the number `c` with `c b^{-j} < u ≤ (c+1) b^{-j}`;
this matches `F_χ`, which counts the points of the closed rectangle `[0,x] × [0,y]`.

* `Zpot_nonneg`, `Zpot_le_two_supNorm`: **display (9)**, `0 ≤ Z_j ≤ 2 ‖F‖∞`;
* `measurable_Zstep_uncurry`: the potential is a measurable function of the heights and the
  indices;
* `gridIndex_succ`: the index at stage `j+1` is `b` times the index at stage `j` plus the
  next digit.
-/

namespace R56Audit

open Finset MeasureTheory Riesz Oscillation

noncomputable section

variable {n : ℕ}

/-! ### Stage geometry -/

/-- `b^{j-h}`, the length of the vertical intervals of stage `j`. -/
def vlen (b h j : ℕ) : ℝ := (b : ℝ) ^ j / (b : ℝ) ^ h

lemma vlen_pos {b : ℕ} (hb : 0 < b) (h j : ℕ) : 0 < vlen b h j := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold vlen
  positivity

lemma vlen_succ (b h j : ℕ) : vlen b h (j + 1) = b * vlen b h j := by
  unfold vlen
  rw [pow_succ]
  ring

/-- The `v`-th vertical interval of stage `j`: `[v b^{j-h}, (v+1) b^{j-h})`, closed at the
bottom and open at the top. -/
def vcell (b h j v : ℕ) : Set ℝ := Set.Ico (v * vlen b h j) ((v + 1) * vlen b h j)

lemma vcell_lt {b : ℕ} (hb : 0 < b) (h j v : ℕ) :
    (v : ℝ) * vlen b h j < ((v : ℝ) + 1) * vlen b h j := by
  have := vlen_pos hb h j
  nlinarith

lemma vcell_nonempty {b : ℕ} (hb : 0 < b) (h j v : ℕ) : (vcell b h j v).Nonempty :=
  ⟨v * vlen b h j, le_rfl, vcell_lt hb h j v⟩

/-- The vertical intervals of stage `j ≤ h` lie in `[0, 1)`. -/
lemma vcell_subset_unit {b h j v : ℕ} (hb : 0 < b) (hj : j ≤ h) (hv : v < b ^ (h - j)) :
    vcell b h j v ⊆ Set.Ico (0 : ℝ) 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hL := vlen_pos hb h j
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have hv1 : (v : ℝ) + 1 ≤ (b : ℝ) ^ (h - j) := by exact_mod_cast hv
  have hfull : (b : ℝ) ^ (h - j) * vlen b h j = 1 := by
    unfold vlen
    rw [← mul_div_assoc, ← pow_add, Nat.sub_add_cancel hj]
    exact div_self (by positivity)
  rintro y ⟨h1, h2⟩
  constructor
  · exact (mul_nonneg hv0 hL.le).trans h1
  · calc y < ((v : ℝ) + 1) * vlen b h j := h2
      _ ≤ (b : ℝ) ^ (h - j) * vlen b h j := mul_le_mul_of_nonneg_right hv1 hL.le
      _ = 1 := hfull

/-- The vertical interval `b v + ℓ` of stage `j` is the block `B_{ℓ+1}` of the `v`-th vertical
interval of stage `j + 1`. -/
lemma vcell_eq_block (b h j v ℓ : ℕ) :
    vcell b h j (b * v + ℓ) = block ((v : ℝ) * vlen b h (j + 1)) (vlen b h j) ℓ := by
  unfold vcell block
  rw [vlen_succ]
  push_cast
  congr 1 <;> ring

/-- The `v`-th vertical interval of stage `j + 1`, as the interval `J` of Lemma 2.3. -/
lemma vcell_succ_eq (b h j v : ℕ) :
    vcell b h (j + 1) v =
      Set.Ico ((v : ℝ) * vlen b h (j + 1)) ((v : ℝ) * vlen b h (j + 1) + b * vlen b h j) := by
  unfold vcell
  rw [vlen_succ]
  congr 1
  ring

/-! ### The potential, as in the manuscript -/

/-- The endpoint average `a^{(I)}(y) = (F(I⁻, y) + F(I⁺, y)) / 2` of the horizontal interval
`I = [xm, xp]`, display (2). -/
def endAvg (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (xm xp : ℝ) : ℝ → ℝ :=
  fun y => (F χ P xm y + F χ P xp y) / 2

/-- **The potential, display (1)**:
`Z_j = (1 / b^h) Σ_{stage-j cells I × B} osc_B a^{(I)}`, the sum over the `b^j` horizontal
intervals `I = [c b^{-j}, (c+1) b^{-j}]` and the `b^{h-j}` vertical intervals
`B = [v b^{j-h}, (v+1) b^{j-h})` of stage `j`. (`b^h = bM`.) -/
def Zpot (χ : Fin n → ℤˣ) (b h j : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
    osc (vcell b h j v)
      (endAvg χ P (((c : ℕ) : ℝ) / (b : ℝ) ^ j) ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j))) /
    (b : ℝ) ^ h

/-! ### The potential, read from the heights and the cell indices -/

/-- The position, relative to the `c`-th horizontal interval of a stage, of a point whose
horizontal coordinate lies in the interval with index `g` of that stage. -/
def sideIdx (g : ℤ) (c : ℕ) : Side :=
  if g < c then Side.left else if g = c then Side.inside else Side.right

lemma sideIdx_eq_inside_iff {g : ℤ} {c : ℕ} : sideIdx g c = Side.inside ↔ g = c := by
  unfold sideIdx
  split_ifs with h1 h2
  · simp only [false_iff]
    omega
  · simp [h2]
  · simp [h2]

/-- The potential of stage `j` for colors `ε`, heights `V` and stage-`j` indices `g`. -/
def Zstep (ε : Fin n → ℝ) (b h j : ℕ) (V : Fin n → ℝ) (g : Fin n → ℤ) : ℝ :=
  (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
    osc (vcell b h j v) (endpointAvg ε V (fun i => sideIdx (g i) c))) / (b : ℝ) ^ h

/-- `u ≤ z / N` exactly when the index of the cell `(k/N, (k+1)/N]` containing `u` is less
than `z`. -/
lemma le_div_iff_gridIndex_lt {N : ℕ} (hN : 0 < N) (u : ℝ) (z : ℤ) :
    u ≤ (z : ℝ) / N ↔ gridIndex N u < z := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold gridIndex
  rw [le_div_iff₀ hNR, mul_comm u, ← Int.ceil_le]
  omega

/-- The position of a point relative to the `c`-th horizontal interval of stage `j` is
determined by its stage-`j` index. -/
lemma sideOf_grid {b : ℕ} (hb : 0 < b) (j c : ℕ) (u : ℝ) :
    sideOf (((c : ℕ) : ℝ) / (b : ℝ) ^ j) ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j) u =
      sideIdx (gridIndex (b ^ j) u) c := by
  have hN : 0 < b ^ j := pow_pos hb j
  have h1 : u ≤ ((c : ℕ) : ℝ) / (b : ℝ) ^ j ↔ gridIndex (b ^ j) u < (c : ℤ) := by
    have := le_div_iff_gridIndex_lt hN u (c : ℤ)
    push_cast at this
    exact this
  have h2 : u ≤ (((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j ↔ gridIndex (b ^ j) u < (c : ℤ) + 1 := by
    have := le_div_iff_gridIndex_lt hN u ((c : ℤ) + 1)
    push_cast at this
    exact this
  unfold sideOf sideIdx
  by_cases a1 : gridIndex (b ^ j) u < (c : ℤ)
  · rw [ite_eq_left (h1.mpr a1), ite_eq_left a1]
  · rw [ite_eq_right (fun h => a1 (h1.mp h)), ite_eq_right a1]
    by_cases a2 : gridIndex (b ^ j) u = (c : ℤ)
    · rw [ite_eq_left (h2.mpr (by omega)), ite_eq_left a2]
    · rw [ite_eq_right (fun h => a2 (by have := h2.mp h; omega)), ite_eq_right a2]

/-- For points with nonnegative coordinates, the potential of the manuscript is the potential
read from the heights and the stage-`j` indices. -/
theorem Zpot_eq_Zstep {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (h j : ℕ) (P : Fin n → ℝ × ℝ)
    (hP : ∀ i, 0 ≤ (P i).1 ∧ 0 ≤ (P i).2) :
    Zpot χ b h j P =
      Zstep (sgn χ) b h j (fun i => (P i).2) (fun i => gridIndex (b ^ j) (P i).1) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold Zpot Zstep
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun v _ => ?_
  congr 1
  funext y
  have hx : ((c : ℕ) : ℝ) / (b : ℝ) ^ j ≤ (((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  change (F χ P _ y + F χ P _ y) / 2 = _
  rw [endpointAvg_eq_F χ P hP hx y]
  congr 1
  funext i
  exact sideOf_grid hb j c (P i).1

/-! ### Bounds: display (9) -/

lemma abs_oldWeight_le (sd : Side) : |oldWeight sd| ≤ 1 := by
  cases sd with
  | left => simp [oldWeight]
  | inside => rw [oldWeight, abs_of_pos (by norm_num)]; norm_num
  | right => simp [oldWeight]

lemma osc_endpointAvg_le_card (ε V : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) : osc B (endpointAvg ε V side) ≤ n := by
  refine (osc_stepFn_le V _ hB).trans ?_
  calc ∑ i, |ε i * oldWeight (side i)| ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        calc |ε i| * |oldWeight (side i)| ≤ 1 * 1 :=
              mul_le_mul (hε i) (abs_oldWeight_le _) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = n := by simp

lemma Zstep_nonneg {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) (V : Fin n → ℝ)
    (g : Fin n → ℤ) : 0 ≤ Zstep ε b h j V g := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold Zstep
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun v _ =>
    osc_stepFn_nonneg V _ (vcell_nonempty hb h j v)

lemma card_cells {b h j : ℕ} (hj : j ≤ h) : (b : ℝ) ^ j * (b : ℝ) ^ (h - j) = (b : ℝ) ^ h := by
  rw [← pow_add, Nat.add_sub_cancel' hj]

/-- For `j ≤ h` the potential is at most `n`. -/
lemma Zstep_le {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (V : Fin n → ℝ) (g : Fin n → ℤ) : Zstep ε b h j V g ≤ n := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold Zstep
  rw [div_le_iff₀ (by positivity)]
  calc ∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
        osc (vcell b h j v) (endpointAvg ε V (fun i => sideIdx (g i) c))
      ≤ ∑ _c : Fin (b ^ j), ∑ _v : Fin (b ^ (h - j)), (n : ℝ) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun v _ =>
          osc_endpointAvg_le_card ε V hε _ (vcell_nonempty hb h j v)
    _ = n * (b : ℝ) ^ h := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [← card_cells hj]
        ring

lemma abs_Zstep_le {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (ε : Fin n → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) (V : Fin n → ℝ) (g : Fin n → ℤ) : |Zstep ε b h j V g| ≤ n := by
  rw [abs_of_nonneg (Zstep_nonneg hb ε h j V g)]
  exact Zstep_le hb hj ε hε V g

/-- `F_χ(x, ·)` is a step function of the height, for all positions of the points. -/
lemma F_eq_stepFn (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ) :
    F χ P x y = stepFn (fun i => (P i).2)
      (fun i => if 0 ≤ (P i).1 ∧ (P i).1 ≤ x ∧ 0 ≤ (P i).2 then sgn χ i else 0) y := by
  classical
  rw [F_eq_filter, Finset.sum_filter]
  unfold stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  by_cases hy : (P i).2 ≤ y
  · by_cases hc : 0 ≤ (P i).1 ∧ (P i).1 ≤ x ∧ 0 ≤ (P i).2
    · rw [ite_eq_left hy, ite_eq_left hc, ite_eq_left ⟨hc.1, hc.2.1, hc.2.2, hy⟩]
      rfl
    · rw [ite_eq_left hy, ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩)]
  · rw [ite_eq_right hy, ite_eq_right (fun h => hy h.2.2.2)]

/-- The endpoint average takes finitely many values. -/
lemma endAvg_image_finite (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (xm xp : ℝ) (B : Set ℝ) :
    ((endAvg χ P xm xp) '' B).Finite := by
  have h : endAvg χ P xm xp = stepFn (fun i => (P i).2)
      (fun i => ((if 0 ≤ (P i).1 ∧ (P i).1 ≤ xm ∧ 0 ≤ (P i).2 then sgn χ i else 0) +
        (if 0 ≤ (P i).1 ∧ (P i).1 ≤ xp ∧ 0 ≤ (P i).2 then sgn χ i else 0)) / 2) := by
    funext y
    unfold endAvg
    rw [F_eq_stepFn, F_eq_stepFn, stepFn_div, stepFn_add]
  rw [h]
  exact stepFn_image_finite _ _ B

/-- **Display (9), lower bound**: `0 ≤ Z_j`. -/
theorem Zpot_nonneg {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (h j : ℕ) (P : Fin n → ℝ × ℝ) :
    0 ≤ Zpot χ b h j P := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold Zpot
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun v _ =>
    osc_nonneg (vcell_nonempty hb h j v) (endAvg_image_finite χ P _ _ _)

/-- **Display (9), upper bound**: `Z_j ≤ 2 ‖F‖∞` for `0 ≤ j ≤ h`. "By (3), an oscillation
`osc_B a^{(I)}` is a difference of two values of `a^{(I)}`, and each of them is an average of
two values of `F`." -/
theorem Zpot_le_two_supNorm {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (χ : Fin n → ℤˣ)
    (P : Fin n → ℝ × ℝ) : Zpot χ b h j P ≤ 2 * supNorm χ P := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpow : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  unfold Zpot
  rw [div_le_iff₀ (by positivity)]
  have hcell : ∀ (c : Fin (b ^ j)) (v : Fin (b ^ (h - j))),
      osc (vcell b h j v)
        (endAvg χ P (((c : ℕ) : ℝ) / (b : ℝ) ^ j) ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j)) ≤
        2 * supNorm χ P := by
    intro c v
    have hc0 : (0 : ℝ) ≤ (c : ℕ) := Nat.cast_nonneg _
    have hc1 : ((c : ℕ) : ℝ) + 1 ≤ (b : ℝ) ^ j := by exact_mod_cast c.isLt
    have hxm : ((c : ℕ) : ℝ) / (b : ℝ) ^ j ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hpow).mpr (by linarith)⟩
    have hxp : (((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hpow).mpr hc1⟩
    apply osc_le (vcell_nonempty hb h j v)
    intro y hy y' hy'
    have hyu := vcell_subset_unit hb hj v.isLt hy
    have hyu' := vcell_subset_unit hb hj v.isLt hy'
    have hY : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hyu.1, hyu.2.le⟩
    have hY' : y' ∈ Set.Icc (0 : ℝ) 1 := ⟨hyu'.1, hyu'.2.le⟩
    have a1 := abs_le.mp (le_supNorm χ P hxm hY)
    have a2 := abs_le.mp (le_supNorm χ P hxp hY)
    have a3 := abs_le.mp (le_supNorm χ P hxm hY')
    have a4 := abs_le.mp (le_supNorm χ P hxp hY')
    unfold endAvg
    linarith [a1.2, a2.2, a3.1, a4.1]
  calc ∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
        osc (vcell b h j v)
          (endAvg χ P (((c : ℕ) : ℝ) / (b : ℝ) ^ j) ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j))
      ≤ ∑ _c : Fin (b ^ j), ∑ _v : Fin (b ^ (h - j)), 2 * supNorm χ P :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun v _ => hcell c v
    _ = 2 * supNorm χ P * (b : ℝ) ^ h := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [← card_cells hj]
        ring

/-! ### Measurability -/

/-- The potential is a measurable function of the heights. -/
lemma measurable_Zstep {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) (g : Fin n → ℤ) :
    Measurable (fun V : Fin n → ℝ => Zstep ε b h j V g) := by
  unfold Zstep
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ fun c _ => Finset.measurable_sum _ fun v _ => ?_
  exact measurable_osc_Ico_stepFn _ (vcell_lt hb h j v)

/-- The potential is a measurable function of the heights and the indices. -/
theorem measurable_Zstep_uncurry {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℤ) => Zstep ε b h j p.1 p.2) :=
  measurable_from_prod_countable_left fun g => measurable_Zstep hb ε h j g

/-! ### The next digit -/

/-- The stage-`(j+1)` indices of points with stage-`j` indices `g` and next digits `r`. -/
def refineIdx {b : ℕ} (g : Fin n → ℤ) (r : Fin n → Fin b) : Fin n → ℤ :=
  fun i => (b : ℤ) * g i + ((r i : ℕ) : ℤ)

/-- The index at stage `j + 1` is `b` times the index at stage `j` plus the next digit. -/
lemma gridIndex_succ {b : ℕ} (hb : 0 < b) (j : ℕ) (u : ℝ) :
    gridIndex (b ^ (j + 1)) u =
      (b : ℤ) * gridIndex (b ^ j) u + ((freshGridIndex (b ^ j) b hb u : ℕ) : ℤ) := by
  have h1 := freshGridIndex_eq_emod (b ^ j) b (pow_pos hb j) hb u
  have h2 := gridIndex_mul_ediv (b ^ j) b hb u
  have h3 := Int.mul_ediv_add_emod (gridIndex (b ^ j * b) u) (b : ℤ)
  rw [pow_succ, h1, ← h2]
  exact h3.symm

end

end R56Audit
