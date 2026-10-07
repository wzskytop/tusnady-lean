import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# The objects of Section 1 of the manuscript, in its own notation

Auditor's supplement (not part of the audited archive).

| Manuscript (Section 1) | Here |
| --- | --- |
| `F_χ(x,y) = Σ_i χ_i 1{P_i ∈ [0,x] × [0,y]}` | `R56Audit.F χ P x y` |
| `‖F_χ‖∞`, the supremum of `|F_χ|` over `[0,1]²` | `R56Audit.supNorm χ P` |

Colorings are `χ : Fin n → ℤˣ`, that is `χ ∈ {±1}ⁿ`; the points are `P : Fin n → ℝ × ℝ`.
-/

namespace R56Audit

open Finset

noncomputable section

variable {n : ℕ}

open Classical in
/-- The signed counting function `F_χ(x,y) = Σ_i χ_i 1[P_i ∈ [0,x] × [0,y]]`. -/
def F (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ) : ℝ :=
  ∑ i, if P i ∈ Set.Icc (0 : ℝ × ℝ) (x, y) then (((χ i : ℤˣ) : ℤ) : ℝ) else 0

/-- `‖F_χ‖∞ = sup_{(x,y) ∈ [0,1]²} |F_χ(x,y)|`, the largest imbalance on an anchored
rectangle. The family is bounded by `n` (`abs_F_le`), so this is a genuine supremum. -/
def supNorm (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) : ℝ :=
  ⨆ z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, |F χ P z.1 z.2|

/-! ### Elementary facts -/

lemma abs_F_le (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ) : |F χ P x y| ≤ n := by
  classical
  unfold F
  calc |∑ i, (if P i ∈ Set.Icc (0 : ℝ × ℝ) (x, y) then (((χ i : ℤˣ) : ℤ) : ℝ) else 0)|
      ≤ ∑ i, |(if P i ∈ Set.Icc (0 : ℝ × ℝ) (x, y) then (((χ i : ℤˣ) : ℤ) : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · rcases Int.units_eq_one_or (χ i) with h | h <;> simp [h]
        · simp
    _ = n := by simp

lemma bddAbove_F (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) :
    BddAbove (Set.range fun z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 => |F χ P z.1 z.2|) :=
  ⟨n, by rintro _ ⟨z, rfl⟩; exact abs_F_le χ P _ _⟩

/-- Every anchored rectangle `[0,x] × [0,y]` with `x, y ∈ [0,1]` has imbalance at most
`‖F_χ‖∞`. -/
lemma le_supNorm (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |F χ P x y| ≤ supNorm χ P :=
  le_ciSup (f := fun z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 => |F χ P z.1 z.2|)
    (bddAbove_F χ P) (⟨x, hx⟩, ⟨y, hy⟩)

/-- `‖F_χ‖∞ ≤ B` exactly when every anchored rectangle has imbalance at most `B`. -/
lemma supNorm_le_iff (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (B : ℝ) :
    supNorm χ P ≤ B ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |F χ P x y| ≤ B := by
  have : Nonempty (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) :=
    ⟨(⟨0, by simp⟩, ⟨0, by simp⟩)⟩
  unfold supNorm
  rw [ciSup_le_iff (bddAbove_F χ P)]
  constructor
  · intro h x hx y hy
    exact h (⟨x, hx⟩, ⟨y, hy⟩)
  · intro h z
    exact h z.1 z.1.2 z.2 z.2.2

lemma supNorm_nonneg (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) : 0 ≤ supNorm χ P :=
  (abs_nonneg _).trans (le_supNorm χ P (x := 0) (y := 0) (by simp) (by simp))

/-- `F_χ` written with the four coordinate inequalities. -/
lemma F_eq_filter (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ) :
    F χ P x y = ∑ t ∈ Finset.univ.filter
      (fun t => 0 ≤ (P t).1 ∧ (P t).1 ≤ x ∧ 0 ≤ (P t).2 ∧ (P t).2 ≤ y),
        (((χ t : ℤˣ) : ℤ) : ℝ) := by
  classical
  unfold F
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h : P t ∈ Set.Icc (0 : ℝ × ℝ) (x, y) ↔
      (0 ≤ (P t).1 ∧ (P t).1 ≤ x ∧ 0 ≤ (P t).2 ∧ (P t).2 ≤ y) := by
    simp only [Set.mem_Icc, Prod.le_def, Prod.fst_zero, Prod.snd_zero]
    tauto
  by_cases hq : P t ∈ Set.Icc (0 : ℝ × ℝ) (x, y)
  · rw [ite_eq_left hq, ite_eq_left (h.mp hq)]
  · rw [ite_eq_right hq, ite_eq_right (fun h' => hq (h.mpr h'))]

end

end R56Audit
