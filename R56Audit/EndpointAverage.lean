import R56Audit.Notation
import R56Audit.LocalGain

/-!
# Display (2): the endpoint averages of `LocalGain.lean` are the manuscript's

Auditor's supplement (not part of the audited archive).

The manuscript defines the endpoint average of a horizontal interval `I = [I⁻, I⁺]` from the
signed counting function, `a(y) = (F(I⁻, y) + F(I⁺, y)) / 2`, and then observes that it is
`Σ_i χ_i w_i 1{V_i ≤ y}` (display (2)). `LocalGain.lean` takes the second expression as the
definition of `endpointAvg` and `childAvg`. This file proves the first equality, for `F` of
`Notation.lean`, so that Lemma 2.3 is a statement about the manuscript's objects:

* `endpointAvg_eq_F`: `(F(I⁻, y) + F(I⁺, y)) / 2 = endpointAvg … y`, when the position of a
  point relative to `I` is read from its horizontal coordinate (`sideOf`);
* `childAvg_eq_F`: the same for the child `C_{k+1} = [I⁻ + k|I|/b, I⁻ + (k+1)|I|/b]`, when
  `r i` is the index of the child that contains the point `i` of `I`;
* `exists_childIndex`: every point of `I` lies in such a child.

The identities are exact for all points with nonnegative coordinates. A point on a common
endpoint of two intervals is assigned to the left one (`sideOf`, `exists_childIndex`); the
manuscript ignores such points, which almost surely do not occur.
-/

namespace R56Audit

open Finset

noncomputable section

variable {n : ℕ}

/-- The colors `χ ∈ {±1}ⁿ` as real numbers. -/
def sgn (χ : Fin n → ℤˣ) : Fin n → ℝ := fun i => (((χ i : ℤˣ) : ℤ) : ℝ)

lemma abs_sgn (χ : Fin n → ℤˣ) (i : Fin n) : |sgn χ i| = 1 := by
  rcases Int.units_eq_one_or (χ i) with h | h <;> simp [sgn, h]

/-- The position of a point with horizontal coordinate `u` relative to `I = [xm, xp]`: to the
left of `I` if `u ≤ xm`, in `I` if `xm < u ≤ xp`, to the right of `I` if `xp < u`. -/
def sideOf (xm xp u : ℝ) : Side :=
  if u ≤ xm then Side.left else if u ≤ xp then Side.inside else Side.right

lemma sideOf_eq_inside_iff {xm xp u : ℝ} :
    sideOf xm xp u = Side.inside ↔ xm < u ∧ u ≤ xp := by
  unfold sideOf
  split_ifs with h1 h2
  · simp [not_lt.mpr h1]
  · simp [not_le.mp h1, h2]
  · simp [h2]

/-- `F_χ(x, y) = Σ_i χ_i 1{U_i ≤ x} 1{V_i ≤ y}` for points with nonnegative coordinates. -/
lemma F_eq_sum_ite (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ)
    (hP : ∀ i, 0 ≤ (P i).1 ∧ 0 ≤ (P i).2) (x y : ℝ) :
    F χ P x y = ∑ i, if (P i).2 ≤ y then (if (P i).1 ≤ x then sgn χ i else 0) else 0 := by
  classical
  rw [F_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := (hP i).1
  have h2 := (hP i).2
  by_cases hy : (P i).2 ≤ y
  · by_cases hx : (P i).1 ≤ x
    · simp [hy, hx, h1, h2, sgn]
    · simp [hy, hx]
  · simp [hy]

/-- **Display (2)**, first equality: the endpoint average of `I = [xm, xp]`,
`a(y) = (F(I⁻, y) + F(I⁺, y)) / 2`, counts a point with weight `1`, `1/2` or `0` according to
its position relative to `I`. -/
theorem endpointAvg_eq_F (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ)
    (hP : ∀ i, 0 ≤ (P i).1 ∧ 0 ≤ (P i).2) {xm xp : ℝ} (hx : xm ≤ xp) (y : ℝ) :
    (F χ P xm y + F χ P xp y) / 2 =
      endpointAvg (sgn χ) (fun i => (P i).2) (fun i => sideOf xm xp (P i).1) y := by
  rw [F_eq_sum_ite χ P hP, F_eq_sum_ite χ P hP, ← Finset.sum_add_distrib, Finset.sum_div]
  unfold endpointAvg stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hy : (P i).2 ≤ y
  · simp only [hy, ite_true]
    unfold sideOf
    by_cases h1 : (P i).1 ≤ xm
    · have h2 : (P i).1 ≤ xp := h1.trans hx
      simp [h1, h2, oldWeight]
    · by_cases h2 : (P i).1 ≤ xp
      · simp [h1, h2, oldWeight]
        ring
      · simp [h1, h2, oldWeight]
  · simp [hy]

/-- Every point of `I = (xm, xp]` lies in exactly one of the `b` children
`(xm + r |I|/b, xm + (r+1) |I|/b]`; this lemma gives the existence. -/
lemma exists_childIndex {b : ℕ} (hb : 0 < b) {xm xp u : ℝ} (hu : xm < u ∧ u ≤ xp) :
    ∃ r : Fin b, xm + (r : ℕ) * ((xp - xm) / b) < u ∧
      u ≤ xm + ((r : ℕ) + 1) * ((xp - xm) / b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hw : 0 < (xp - xm) / b := div_pos (by linarith) hbR
  have hfull : (b : ℝ) * ((xp - xm) / b) = xp - xm := by field_simp
  obtain ⟨t, ht⟩ : ∃ t : ℝ, u - xm = t * ((xp - xm) / b) :=
    ⟨(u - xm) / ((xp - xm) / b), (div_mul_cancel₀ _ hw.ne').symm⟩
  have ht0 : 0 < t := by
    by_contra h
    have := mul_le_mul_of_nonneg_right (not_lt.mp h) hw.le
    linarith
  have htb : t ≤ b := by
    by_contra h
    have := mul_lt_mul_of_pos_right (not_le.mp h) hw
    linarith
  have hceil_pos : 0 < ⌈t⌉₊ := Nat.ceil_pos.mpr ht0
  have hceil_le : ⌈t⌉₊ ≤ b := Nat.ceil_le.mpr htb
  have hc : ((⌈t⌉₊ - 1 : ℕ) : ℝ) = (⌈t⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil_pos, Nat.cast_one]
  refine ⟨⟨⌈t⌉₊ - 1, by omega⟩, ?_, ?_⟩
  · have h1 : ((⌈t⌉₊ - 1 : ℕ) : ℝ) < t := by
      rw [hc]
      linarith [Nat.ceil_lt_add_one ht0.le]
    have := mul_lt_mul_of_pos_right h1 hw
    simp only
    linarith
  · have h2 : t ≤ ((⌈t⌉₊ - 1 : ℕ) : ℝ) + 1 := by
      rw [hc]
      linarith [Nat.le_ceil t]
    have := mul_le_mul_of_nonneg_right h2 hw.le
    simp only
    linarith

/-- **Display (2) for a child**: let `r i` be the index of the child of `I = [xm, xp]` that
contains the point `i`, for every point of `I`. Then the endpoint average of the child
`C_{k+1} = [xm + k |I|/b, xm + (k+1) |I|/b]` is the child function `childAvg … r k` of
`LocalGain.lean`. -/
theorem childAvg_eq_F {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ)
    (hP : ∀ i, 0 ≤ (P i).1 ∧ 0 ≤ (P i).2) {xm xp : ℝ} (hx : xm < xp) (r : Fin n → Fin b)
    (hr : ∀ i, xm < (P i).1 ∧ (P i).1 ≤ xp →
      xm + (r i : ℕ) * ((xp - xm) / b) < (P i).1 ∧
        (P i).1 ≤ xm + ((r i : ℕ) + 1) * ((xp - xm) / b))
    (k : Fin b) (y : ℝ) :
    (F χ P (xm + (k : ℕ) * ((xp - xm) / b)) y +
        F χ P (xm + ((k : ℕ) + 1) * ((xp - xm) / b)) y) / 2 =
      childAvg (sgn χ) (fun i => (P i).2) (fun i => sideOf xm xp (P i).1) r k y := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hw : 0 < (xp - xm) / b := div_pos (by linarith) hbR
  have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
  have hk1 : ((k : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast k.isLt
  have hfull : (b : ℝ) * ((xp - xm) / b) = xp - xm := by field_simp
  rw [F_eq_sum_ite χ P hP, F_eq_sum_ite χ P hP, ← Finset.sum_add_distrib, Finset.sum_div]
  unfold childAvg stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hy : (P i).2 ≤ y
  · simp only [hy, ite_true]
    by_cases h1 : (P i).1 ≤ xm
    · -- to the left of `I`: to the left of every child
      have ha : (P i).1 ≤ xm + (k : ℕ) * ((xp - xm) / b) := by nlinarith
      have hb' : (P i).1 ≤ xm + ((k : ℕ) + 1) * ((xp - xm) / b) := by nlinarith
      simp [sideOf, h1, ha, hb', childWeight]
    · by_cases h2 : (P i).1 ≤ xp
      · -- in `I`, in the child with index `r i`
        obtain ⟨hlo, hhi⟩ := hr i ⟨not_le.mp h1, h2⟩
        have hside : sideOf xm xp (P i).1 = Side.inside := by simp [sideOf, h1, h2]
        simp only [hside, childWeight]
        rcases lt_trichotomy (r i) k with hlt | heq | hgt
        · have hlt' : ((r i : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast hlt
          have ha : (P i).1 ≤ xm + (k : ℕ) * ((xp - xm) / b) := by nlinarith
          have hb' : (P i).1 ≤ xm + ((k : ℕ) + 1) * ((xp - xm) / b) := by nlinarith
          simp [hlt, ha, hb']
        · have ha : ¬ (P i).1 ≤ xm + (k : ℕ) * ((xp - xm) / b) := by
            rw [← heq]; exact not_le.mpr hlo
          have hb' : (P i).1 ≤ xm + ((k : ℕ) + 1) * ((xp - xm) / b) := by
            rw [← heq]; exact hhi
          simp [heq, ha, hb']
          ring
        · have hgt' : ((k : ℕ) : ℝ) + 1 ≤ (r i : ℕ) := by exact_mod_cast hgt
          have ha : ¬ (P i).1 ≤ xm + (k : ℕ) * ((xp - xm) / b) := by
            apply not_le.mpr; nlinarith
          have hb' : ¬ (P i).1 ≤ xm + ((k : ℕ) + 1) * ((xp - xm) / b) := by
            apply not_le.mpr; nlinarith
          have hne : r i ≠ k := ne_of_gt hgt
          simp [not_lt.mpr hgt.le, hne, ha, hb']
      · -- to the right of `I`: to the right of every child
        have h2' : xp < (P i).1 := not_le.mp h2
        have ha : ¬ (P i).1 ≤ xm + (k : ℕ) * ((xp - xm) / b) := by
          apply not_le.mpr; nlinarith
        have hb' : ¬ (P i).1 ≤ xm + ((k : ℕ) + 1) * ((xp - xm) / b) := by
          apply not_le.mpr; nlinarith
        simp [sideOf, h1, h2, ha, hb', childWeight]
  · simp [hy]

end

end R56Audit
