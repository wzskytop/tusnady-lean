import R56Audit
import Lean.Util.CollectAxioms

/-!
# Statement gates for the auditor's supplement (manuscript r65)

Auditor's check script (not part of the audited archive, and not part of the supplement
library). Run with

    lake env lean -DautoImplicit=false -DwarningAsError=true audit-claude/Gates.lean

The file is the reading list of the supplement: it contains, in the order of the manuscript,
the definitions and the statements that correspond to the manuscript, and Lean checks each of
them against the library.

* A statement gate `example : (statement) = type_of% @T := rfl` fails unless the statement of
  `T` in the library is the statement written here (up to unfolding of definitions). It pins
  the statement in both directions: `T` proves neither more nor less. The statements are
  copied from the sources by `audit-claude/mkgates.py`, from the list in
  `audit-claude/Gates.template`, so that the two cannot drift apart; `check.sh` regenerates
  the file and compares. `audit-claude/mutants.py` is the negative test: it changes one
  hypothesis, constant or relation at a time and checks that the gate then fails.
* A definition gate `example : X = (body) := rfl` (or `Iff.rfl`) does the same for a
  definition, with the body written out by hand. (`oldWeight` and `childWeight` are given by
  their values at the three positions, and `nextDigits` by its value as a natural number; the
  inductive type `Side` and the archive's `freshGridIndex` are described by proved facts
  instead.)

Whether a statement written here says what the manuscript says is a matter of reading; the
auditor's reading is recorded item by item in `AUDIT_CLAUDE.md`.

The names in this file are read with the namespaces `R56Audit`, `Riesz`, `Riesz.PointSets`,
`Oscillation`, `MeasureTheory` and `ProbabilityTheory` open. `SupplementAudit.lean` checks
that no name of the supplement coincides with a name of the root namespace or of another open
namespace, apart from a short list. Of that list this file uses only `maxOn` and `minOn`
without their prefix (Lean's core library has other functions of these names): in the
definition gates they are written `R56Audit.maxOn`, `R56Audit.minOn`, and in a statement gate
a name read in the wrong way would make the `rfl` fail.

The last part of the file checks the axioms of every declaration of the supplement; the
route of the proof of Theorem 1.1: it goes through the statements of the manuscript, it uses
none of a list of declarations of the archive's own proof, and what it uses of the archive
lies in eight named modules; and the reading list: every definition of the supplement or of
the archive that occurs in a statement gate (outside the last section, on the archive's own
routes) has a definition gate.
-/

open MeasureTheory ProbabilityTheory Riesz Riesz.PointSets Oscillation R56Audit

open scoped Classical

-- The hypotheses of the statements below keep the names they have in the sources; the names
-- are not referred to, so the unused-variable linter is switched off in this script.
set_option linter.unusedVariables false

-- Any other warning stops the script.
set_option warningAsError true

/-! ## Section 1. `F_χ`, `‖F_χ‖∞`, Theorem 1.1, Corollary 1.2 -/

-- The law of `n` independent uniform points of `[0,1]²` (the archive's definition).
example (n : ℕ) : unifPts n =
    Measure.pi fun _ : Fin n => (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1) := rfl

-- `F_χ(x, y) = Σ_i χ_i 1{P_i ∈ [0,x] × [0,y]}`; a coloring is `χ : Fin n → ℤˣ = {±1}ⁿ`.
example {n : ℕ} (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ) :
    F χ P x y =
      ∑ i, if P i ∈ Set.Icc (0 : ℝ × ℝ) (x, y) then (((χ i : ℤˣ) : ℤ) : ℝ) else 0 := rfl

-- `F_eq_filter` (Notation)
example : (∀ {n : ℕ} (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ),
      F χ P x y = ∑ t ∈ Finset.univ.filter
        (fun t => 0 ≤ (P t).1 ∧ (P t).1 ≤ x ∧ 0 ≤ (P t).2 ∧ (P t).2 ≤ y),
          (((χ t : ℤˣ) : ℤ) : ℝ)) =
    type_of% @R56Audit.F_eq_filter := rfl

-- `‖F_χ‖∞`: the supremum of `|F_χ|` over `[0,1]²`. It is attained, so it is a maximum.
example {n : ℕ} (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) :
    supNorm χ P = ⨆ z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, |F χ P z.1 z.2| := rfl

-- `exists_eq_supNorm` (SupNorm)
example : (∀ {n : ℕ} (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ),
      ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, |F χ P x y| = supNorm χ P) =
    type_of% @R56Audit.exists_eq_supNorm := rfl

-- `supNorm_le_iff` (Notation)
example : (∀ {n : ℕ} (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (B : ℝ),
      supNorm χ P ≤ B ↔
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |F χ P x y| ≤ B) =
    type_of% @R56Audit.supNorm_le_iff := rfl

-- `measurable_supNorm` (SupNorm)
example : (∀ {n : ℕ} (χ : Fin n → ℤˣ),
      Measurable (supNorm χ)) =
    type_of% @R56Audit.measurable_supNorm := rfl

-- The events of Theorem 1.1 and of Proposition 2.7 are measurable.
-- `measurableSet_forall_le_supNorm` (SupNorm)
example : (∀ {n : ℕ} (t : ℝ),
      MeasurableSet {P : Fin n → ℝ × ℝ | ∀ χ : Fin n → ℤˣ, t ≤ supNorm χ P}) =
    type_of% @R56Audit.measurableSet_forall_le_supNorm := rfl

-- `measurableSet_exists_supNorm_le` (SupNorm)
example : (∀ {n : ℕ} (B : ℝ),
      MeasurableSet {P : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ B}) =
    type_of% @R56Audit.measurableSet_exists_supNorm_le := rfl

-- **Theorem 1.1.**
-- `theorem_1_1` (Parameters)
example : (
      ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal (1 - Real.exp (-A * n)) ≤
          unifPts n {P | ∀ χ : Fin n → ℤˣ, c * Real.logb 2 n ^ (3 / 2 : ℝ) ≤ supNorm χ P}) =
    type_of% @R56Audit.theorem_1_1 := rfl

-- The same statement without any definition of the supplement or of the archive.
-- `theorem_1_1_unfolded` (Parameters)
example : (
      ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal (1 - Real.exp (-A * n)) ≤
          (MeasureTheory.Measure.pi fun _ : Fin n =>
              (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))
            {P : Fin n → ℝ × ℝ | ∀ χ : Fin n → ℤˣ,
              ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1,
                c * Real.logb 2 (n : ℝ) ^ (3 / 2 : ℝ) ≤
                  |∑ i : Fin n, if 0 ≤ (P i).1 ∧ (P i).1 ≤ x ∧ 0 ≤ (P i).2 ∧ (P i).2 ≤ y
                    then (((χ i : ℤˣ) : ℤ) : ℝ) else 0|}) =
    type_of% @R56Audit.theorem_1_1_unfolded := rfl

-- The constant: `c_A = b⁻⁸ / (1 + log₂ b)^{3/2}` for any integer `b` satisfying (15).
example (b : ℕ) : cA b = ((b : ℝ) ^ 8)⁻¹ / (1 + Real.logb 2 b) ^ (3 / 2 : ℝ) := rfl

-- `theorem_1_1_constant` (Parameters)
example : (∀ {A : ℝ} (hA : 0 < A) {b : ℕ} (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A +
    2 + Real.log 2 ≤ (b : ℝ) / 4096) {n : ℕ} (hn : 1 ≤ n),
      ENNReal.ofReal (1 - Real.exp (-A * n)) ≤
        unifPts n {P | ∀ χ : Fin n → ℤˣ, cA b * Real.logb 2 n ^ (3 / 2 : ℝ) ≤ supNorm χ P}) =
    type_of% @R56Audit.theorem_1_1_constant := rfl

-- On a measurable event: distinct points of `[0,1]²`, strict inequality (as the proof gives).
-- `theorem_1_1_constant_event` (Parameters)
example : (∀ {A : ℝ} (hA : 0 < A) {b : ℕ} (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A +
    2 + Real.log 2 ≤ (b : ℝ) / 4096) {n : ℕ} (hn : 1 ≤ n),
      ∃ G : Set (Fin n → ℝ × ℝ), MeasurableSet G ∧
        ENNReal.ofReal (1 - Real.exp (-A * n)) ≤ unifPts n G ∧
        ∀ P ∈ G, Function.Injective P ∧ (∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1) ∧
          ∀ χ : Fin n → ℤˣ, cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P) =
    type_of% @R56Audit.theorem_1_1_constant_event := rfl

-- "there is an `n`-point set for which every coloring leaves an anchored rectangle with
-- imbalance at least `c_A (log₂ n)^{3/2}`"
-- `exists_points` (Parameters)
example : (∀ {A : ℝ} (hA : 0 < A) {b : ℕ} (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A +
    2 + Real.log 2 ≤ (b : ℝ) / 4096) {n : ℕ} (hn : 1 ≤ n),
      ∃ P : Fin n → ℝ × ℝ, Function.Injective P ∧ (∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1) ∧
        ∀ χ : Fin n → ℤˣ, cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P) =
    type_of% @R56Audit.exists_points := rfl

-- **Corollary 1.2, lower bound.** `Δ₂(n)` is the archive's definition: the largest
-- discrepancy of an `n`-point set with respect to closed axis-parallel rectangles.
example (n : ℕ) : Δ₂ n = ⨆ X : {X : Finset (ℝ × ℝ) // X.card = n}, rectDisc X.1 := rfl

example (X : Finset (ℝ × ℝ)) : rectDisc X =
    ⨅ χ : X → ℤˣ, ⨆ ab : (ℝ × ℝ) × (ℝ × ℝ), (colorSum X χ (Set.Icc ab.1 ab.2)).natAbs := rfl

example (X : Finset (ℝ × ℝ)) (χ : X → ℤˣ) (R : Set (ℝ × ℝ)) :
    colorSum X χ R = ∑ p : X, if (p : ℝ × ℝ) ∈ R then ((χ p : ℤˣ) : ℤ) else 0 := rfl

-- `corollary_1_2_lower` (Parameters)
example : (
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * Real.logb 2 n ^ (3 / 2 : ℝ) < Δ₂ n) =
    type_of% @R56Audit.corollary_1_2_lower := rfl

-- "Anchored rectangles are a subfamily of all rectangles"
-- `lt_Δ₂_of_supNorm` (ArchiveInterface)
example : (∀ {n : ℕ} {t : ℝ} (P : Fin n → ℝ × ℝ) (hP : Function.Injective P) (h : ∀ χ : Fin n →
    ℤˣ, t < supNorm χ P),
      t < Δ₂ n) =
    type_of% @R56Audit.lt_Δ₂_of_supNorm := rfl

/-! ## Section 2.1. Setup -/

-- The probability-one event: all heights are distinct, and no coordinate of a point has the
-- form `k / b^r` with integers `k` and `r ≥ 0`.
example {n : ℕ} (b : ℕ) (P : Fin n → ℝ × ℝ) :
    SetupEvent b P ↔ (Function.Injective fun i => (P i).2) ∧
      ∀ i, ∀ (k : ℤ) (r : ℕ), (P i).1 ≠ (k : ℝ) / (b : ℝ) ^ r ∧ (P i).2 ≠ (k : ℝ) / (b : ℝ) ^ r :=
  Iff.rfl

example {n : ℕ} (b : ℕ) (P : Fin n → ℝ × ℝ) :
    NoGrid b P ↔
      ∀ i, ∀ (k : ℤ) (r : ℕ), (P i).1 ≠ (k : ℝ) / (b : ℝ) ^ r ∧ (P i).2 ≠ (k : ℝ) / (b : ℝ) ^ r :=
  Iff.rfl

-- `ae_setupEvent` (GoodTransitions)
example : (∀ (n b : ℕ),
      ∀ᵐ P ∂unifPts n, SetupEvent b P) =
    type_of% @R56Audit.ae_setupEvent := rfl

-- `ae_heights_injective` (GoodTransitions)
example : (∀ (n : ℕ),
      ∀ᵐ P ∂unifPts n, Function.Injective fun i => (P i).2) =
    type_of% @R56Audit.ae_heights_injective := rfl

-- `ae_noGrid` (GoodTransitions)
example : (∀ (n b : ℕ),
      ∀ᵐ P ∂unifPts n, NoGrid b P) =
    type_of% @R56Audit.ae_noGrid := rfl

-- On that event the points lie in `(0,1]²` (indeed in `(0,1)²`).
example {n : ℕ} (P : Fin n → ℝ × ℝ) :
    InUnit P ↔ ∀ i, (P i).1 ∈ Set.Ioc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ioc (0 : ℝ) 1 := Iff.rfl

-- `inUnit_of_noGrid` (GoodTransitions)
example : (∀ {n : ℕ} {b : ℕ} {P : Fin n → ℝ × ℝ} (hP : ∀ i, (P i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P
    i).2 ∈ Set.Icc (0 : ℝ) 1) (hgrid : NoGrid b P),
      InUnit P) =
    type_of% @R56Audit.inUnit_of_noGrid := rfl

-- `ae_inUnit` (GoodTransitions)
example : (∀ (n : ℕ),
      ∀ᵐ P ∂unifPts n, InUnit P) =
    type_of% @R56Audit.ae_inUnit := rfl

/-! ### Endpoint average, display (2) -/

-- `a^{(I)}(y) = (F(I⁻, y) + F(I⁺, y)) / 2`, for `I = [xm, xp]`.
example {n : ℕ} (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (xm xp y : ℝ) :
    endAvg χ P xm xp y = (F χ P xm y + F χ P xp y) / 2 := rfl

-- The position of a point relative to `I`, and its weight: `1` to the left of `I`, `1/2` in
-- `I`, `0` to the right of `I`.
example (xm xp u : ℝ) :
    sideOf xm xp u = if u ≤ xm then Side.left else if u ≤ xp then Side.inside else Side.right :=
  rfl

example (sd : Side) : sd = Side.left ∨ sd = Side.inside ∨ sd = Side.right := by
  cases sd <;> simp

example : Side.left ≠ Side.inside ∧ Side.left ≠ Side.right ∧ Side.inside ≠ Side.right := by
  decide

example : oldWeight Side.left = 1 ∧ oldWeight Side.inside = 1 / 2 ∧ oldWeight Side.right = 0 :=
  ⟨rfl, rfl, rfl⟩

example {n : ℕ} (χ : Fin n → ℤˣ) (i : Fin n) : sgn χ i = (((χ i : ℤˣ) : ℤ) : ℝ) := rfl

-- `Σ_i c_i 1{V_i ≤ y}`, and the right-hand side of display (2), `Σ_i χ_i w_i 1{V_i ≤ y}`.
example {n : ℕ} (V c : Fin n → ℝ) (y : ℝ) : stepFn V c y = ∑ i, if V i ≤ y then c i else 0 := rfl

example {n : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) (y : ℝ) :
    endpointAvg ε V side y = ∑ i, if V i ≤ y then ε i * oldWeight (side i) else 0 := rfl

-- Display (2).
-- `endpointAvg_eq_F` (EndpointAverage)
example : (∀ {n : ℕ} (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (hP : ∀ i, 0 ≤ (P i).1 ∧ 0 ≤ (P i).2)
    {xm xp : ℝ} (hx : xm ≤ xp) (y : ℝ),
      (F χ P xm y + F χ P xp y) / 2 =
        endpointAvg (sgn χ) (fun i => (P i).2) (fun i => sideOf xm xp (P i).1) y) =
    type_of% @R56Audit.endpointAvg_eq_F := rfl

/-! ### Oscillation and midpoint, display (3) -/

-- (Lean's core library has other functions called `maxOn` and `minOn`. In this file the names
-- stand for the two functions defined here.)
example {α : Type*} (B : Set α) (f : α → ℝ) : R56Audit.maxOn B f = sSup (f '' B) := rfl

example {α : Type*} (B : Set α) (f : α → ℝ) : R56Audit.minOn B f = sInf (f '' B) := rfl

example {α : Type*} (B : Set α) (f : α → ℝ) : osc B f = sSup (f '' B) - sInf (f '' B) := rfl

example {α : Type*} (B : Set α) (f : α → ℝ) : mid B f = (sSup (f '' B) + sInf (f '' B)) / 2 := rfl

-- "They take finitely many values, so these extrema exist, and they are
-- `mid_B f ± ½ osc_B f`."
-- `maxOn_mem` (Osc)
example {α : Type*} : (∀ {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite),
      ∃ y ∈ B, f y = maxOn B f) =
    type_of% (@R56Audit.maxOn_mem α) := rfl

-- `minOn_mem` (Osc)
example {α : Type*} : (∀ {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite),
      ∃ y ∈ B, f y = minOn B f) =
    type_of% (@R56Audit.minOn_mem α) := rfl

-- `le_maxOn` (Osc)
example {α : Type*} : (∀ {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y : α} (hy : y ∈ B),
      f y ≤ maxOn B f) =
    type_of% (@R56Audit.le_maxOn α) := rfl

-- `minOn_le` (Osc)
example {α : Type*} : (∀ {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y : α} (hy : y ∈ B),
      minOn B f ≤ f y) =
    type_of% (@R56Audit.minOn_le α) := rfl

-- `maxOn_eq_mid_add` (Osc)
example {α : Type*} : (∀ (B : Set α) (f : α → ℝ),
      maxOn B f = mid B f + osc B f / 2) =
    type_of% (@R56Audit.maxOn_eq_mid_add α) := rfl

-- `minOn_eq_mid_sub` (Osc)
example {α : Type*} : (∀ (B : Set α) (f : α → ℝ),
      minOn B f = mid B f - osc B f / 2) =
    type_of% (@R56Audit.minOn_eq_mid_sub α) := rfl

-- `stepFn_image_finite` (LocalGain)
example : (∀ {n : ℕ} (V c : Fin n → ℝ) (B : Set ℝ),
      ((stepFn V c) '' B).Finite) =
    type_of% @R56Audit.stepFn_image_finite := rfl

-- `endAvg_image_finite` (Potential)
example : (∀ {n : ℕ} (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (xm xp : ℝ) (B : Set ℝ),
      ((endAvg χ P xm xp) '' B).Finite) =
    type_of% @R56Audit.endAvg_image_finite := rfl

-- "`osc_B(cf) = |c| osc_B f`"; shift invariance; the triangle inequality, for two functions
-- and for finite sums; the reverse triangle inequality.
-- `osc_const_mul` (Osc)
example {α : Type*} : (∀ (B : Set α) (f : α → ℝ) (c : ℝ),
      osc B (fun y => c * f y) = |c| * osc B f) =
    type_of% (@R56Audit.osc_const_mul α) := rfl

-- `osc_add_const` (Osc)
example {α : Type*} : (∀ {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) (c :
    ℝ),
      osc B (fun y => f y + c) = osc B f) =
    type_of% (@R56Audit.osc_add_const α) := rfl

-- `mid_add_const` (Osc)
example {α : Type*} : (∀ {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) (c :
    ℝ),
      mid B (fun y => f y + c) = mid B f + c) =
    type_of% (@R56Audit.mid_add_const α) := rfl

-- "because the maximum of `f+g` on `B` is at most `max_B f + max_B g`, and its minimum is at
-- least `min_B f + min_B g`"
-- `maxOn_add_le` (Osc)
example {α : Type*} : (∀ {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) (hg
    : (g '' B).Finite),
      maxOn B (fun y => f y + g y) ≤ maxOn B f + maxOn B g) =
    type_of% (@R56Audit.maxOn_add_le α) := rfl

-- `add_minOn_le` (Osc)
example {α : Type*} : (∀ {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) (hg
    : (g '' B).Finite),
      minOn B f + minOn B g ≤ minOn B (fun y => f y + g y)) =
    type_of% (@R56Audit.add_minOn_le α) := rfl

-- `osc_add_le` (Osc)
example {α : Type*} : (∀ {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) (hg
    : (g '' B).Finite),
      osc B (fun y => f y + g y) ≤ osc B f + osc B g) =
    type_of% (@R56Audit.osc_add_le α) := rfl

-- `osc_sum_le` (Osc)
example {α : Type*} {ι : Type*} : (∀ (s : Finset ι) {B : Set α} {f : ι → α → ℝ} (hB :
    B.Nonempty) (hf : ∀ k ∈ s, ((f k) '' B).Finite),
      osc B (fun y => ∑ k ∈ s, f k y) ≤ ∑ k ∈ s, osc B (f k)) =
    type_of% (@R56Audit.osc_sum_le α ι) := rfl

-- "using `osc_B(-g) = osc_B g` gives `osc_B f ≤ osc_B(f+g) + osc_B g`"
-- `osc_neg` (Osc)
example {α : Type*} : (∀ (B : Set α) (g : α → ℝ),
      osc B (fun y => -g y) = osc B g) =
    type_of% (@R56Audit.osc_neg α) := rfl

-- `osc_le_osc_add_add` (StepOsc)
example {α : Type*} : (∀ {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) (hg
    : (g '' B).Finite),
      osc B f ≤ osc B (fun y => f y + g y) + osc B g) =
    type_of% (@R56Audit.osc_le_osc_add_add α) := rfl

-- `abs_osc_add_sub_le` (StepOsc)
example {α : Type*} : (∀ {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) (hg
    : (g '' B).Finite),
      |osc B (fun y => f y + g y) - osc B f| ≤ osc B g) =
    type_of% (@R56Audit.abs_osc_add_sub_le α) := rfl

/-! ## Section 2.2. A deterministic comparison -/

-- The blocks `B_1, …, B_b` of `J = [s, s + bL)`: `B_{ℓ+1} = [s + ℓL, s + (ℓ+1)L)`.
example (s L : ℝ) (ℓ : ℕ) : block s L ℓ = Set.Ico (s + ℓ * L) (s + (ℓ + 1) * L) := rfl

-- `iUnion_block` (Osc)
example : (∀ (s : ℝ) {L : ℝ} (hL : 0 < L) (b : ℕ),
      ⋃ ℓ : Fin b, block s L ℓ = Set.Ico s (s + b * L)) =
    type_of% @R56Audit.iUnion_block := rfl

-- `block_disjoint` (Osc)
example : (∀ (s : ℝ) {L : ℝ} (hL : 0 < L) {ℓ ℓ' : ℕ} (h : ℓ ≠ ℓ'),
      Disjoint (block s L ℓ) (block s L ℓ')) =
    type_of% @R56Audit.block_disjoint := rfl

-- `B_2 ∪ ⋯ ∪ B_{b-1}`, the heights of the inner region; "it is not empty because `b ≥ 3`".
-- `iUnion_inner_blocks` (Osc)
example : (∀ (s : ℝ) {L : ℝ} (hL : 0 < L) {b : ℕ} (hb : 2 ≤ b),
      ⋃ ℓ ∈ Finset.Ico 1 (b - 1), block s L ℓ = Set.Ico (s + L) (s + ((b : ℝ) - 1) * L)) =
    type_of% @R56Audit.iUnion_inner_blocks := rfl

-- `inner_blocks_nonempty` (Osc)
example : (∀ (s : ℝ) {L : ℝ} (hL : 0 < L) {b : ℕ} (hb : 3 ≤ b),
      (Set.Ico (s + L) (s + ((b : ℝ) - 1) * L)).Nonempty) =
    type_of% @R56Audit.inner_blocks_nonempty := rfl

-- **Lemma 2.1**, display (4).
-- `vertical_comparison` (Osc)
example : (∀ {b : ℕ} (hb : 2 ≤ b) (s : ℝ) {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) (hf : (f '' Set.Ico s
    (s + b * L)).Finite),
      ∑ ℓ : Fin b, osc (block s L ℓ) f +
          2 * |mid (block s L (b - 1)) f - mid (block s L 0) f| ≤
        b * osc (Set.Ico s (s + b * L)) f) =
    type_of% @R56Audit.vertical_comparison := rfl

-- Its proof: the first display (each line is these two statements, the second line with the
-- two blocks exchanged); "Taking the larger of the two right-hand sides"; "Also
-- `osc_J f ≥ osc_{B_ℓ} f`". The lemma is proved for arbitrary nonempty subsets of `J`.
-- `maxOn_sub_minOn_le_osc` (Osc)
example {α : Type*} : (∀ {A C J : Set α} {f : α → ℝ} (hA : A.Nonempty) (hC : C.Nonempty) (hAJ :
    A ⊆ J) (hCJ : C ⊆ J) (hf : (f '' J).Finite),
      maxOn C f - minOn A f ≤ osc J f) =
    type_of% (@R56Audit.maxOn_sub_minOn_le_osc α) := rfl

-- `maxOn_sub_minOn_eq` (Osc)
example {α : Type*} : (∀ (A C : Set α) (f : α → ℝ),
      maxOn C f - minOn A f = (osc A f + osc C f) / 2 + (mid C f - mid A f)) =
    type_of% (@R56Audit.maxOn_sub_minOn_eq α) := rfl

-- `half_osc_add_abs_mid_sub_le` (Osc)
example {α : Type*} : (∀ {A C J : Set α} {f : α → ℝ} (hA : A.Nonempty) (hC : C.Nonempty) (hAJ :
    A ⊆ J) (hCJ : C ⊆ J) (hf : (f '' J).Finite),
      (osc A f + osc C f) / 2 + |mid C f - mid A f| ≤ osc J f) =
    type_of% (@R56Audit.half_osc_add_abs_mid_sub_le α) := rfl

-- `osc_mono` (Osc)
example {α : Type*} : (∀ {A J : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAJ : A ⊆ J) (hf : (f ''
    J).Finite),
      osc A f ≤ osc J f) =
    type_of% (@R56Audit.osc_mono α) := rfl

-- `vertical_comparison_sets` (Osc)
example {α : Type*} : (∀ {b : ℕ} (hb : 2 ≤ b) (J : Set α) (B : Fin b → Set α) (hne : ∀ ℓ, (B
    ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J) (f : α → ℝ) (hf : (f '' J).Finite),
      ∑ ℓ : Fin b, osc (B ℓ) f +
          2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f) =
    type_of% (@R56Audit.vertical_comparison_sets α) := rfl

/-! ## Section 2.3. Horizontal refinement and the random gain -/

-- The local experiment: colors `ε`, heights `V` and positions `side` relative to `I` are
-- fixed; `r i` is the child of the point `i` (used only for points in `I`), and the
-- expectation is the average over all `r : Fin n → Fin b`.
example {α : Type*} [Fintype α] (f : α → ℝ) : finAvg f = (∑ x, f x) / Fintype.card α := rfl

-- The weight of a point in the child `C_{k+1}`, given its position relative to `I` and its
-- own child `C_{r+1}`; the child function `a_k`.
example {b : ℕ} (r k : Fin b) :
    childWeight Side.left r k = 1 ∧ childWeight Side.right r k = 0 ∧
      childWeight Side.inside r k = (if r < k then 1 else if r = k then 1 / 2 else 0) :=
  ⟨rfl, rfl, rfl⟩

example {n b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n → Fin b) (k : Fin b)
    (y : ℝ) :
    childAvg ε V side r k y =
      ∑ i, if V i ≤ y then ε i * childWeight (side i) (r i) k else 0 := rfl

-- The child functions are the endpoint averages of the children of `I`.
-- `exists_childIndex` (EndpointAverage)
example : (∀ {b : ℕ} (hb : 0 < b) {xm xp u : ℝ} (hu : xm < u ∧ u ≤ xp),
      ∃ r : Fin b, xm + (r : ℕ) * ((xp - xm) / b) < u ∧
        u ≤ xm + ((r : ℕ) + 1) * ((xp - xm) / b)) =
    type_of% @R56Audit.exists_childIndex := rfl

-- `childAvg_eq_F` (EndpointAverage)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (hP : ∀ i, 0 ≤ (P
    i).1 ∧ 0 ≤ (P i).2) {xm xp : ℝ} (hx : xm < xp) (r : Fin n → Fin b) (hr : ∀ i, xm < (P i).1 ∧
    (P i).1 ≤ xp → xm + (r i : ℕ) * ((xp - xm) / b) < (P i).1 ∧ (P i).1 ≤ xm + ((r i : ℕ) + 1) *
    ((xp - xm) / b)) (k : Fin b) (y : ℝ),
      (F χ P (xm + (k : ℕ) * ((xp - xm) / b)) y +
          F χ P (xm + ((k : ℕ) + 1) * ((xp - xm) / b)) y) / 2 =
        childAvg (sgn χ) (fun i => (P i).2) (fun i => sideOf xm xp (P i).1) r k y) =
    type_of% @R56Audit.childAvg_eq_F := rfl

-- `m_R`: the number of points in the inner region.
example {n : ℕ} (b : ℕ) (V : Fin n → ℝ) (side : Fin n → Side) (s L : ℝ) :
    innerPoints b V side s L = Finset.univ.filter
      (fun i => side i = Side.inside ∧ s + L ≤ V i ∧ V i < s + ((b : ℝ) - 1) * L) := rfl

-- `mem_innerPoints_iff` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ}
    (hL : 0 < L) (i : Fin n),
      i ∈ innerPoints b V side s L ↔
        side i = Side.inside ∧ V i ∈ ⋃ ℓ ∈ Finset.Ico 1 (b - 1), block s L ℓ) =
    type_of% @R56Audit.mem_innerPoints_iff := rfl

-- **Fact 2.2.**
-- `fact_2_2_general` (SymmetricSumsGeneral)
example {Ω ι : Type*} : (∀ [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype
    ι] (X : ι → Ω → ℝ) (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i
    ω) μ μ) {σ : ℝ} (hσ : 0 < σ) (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2) (h4i : ∀ i, Integrable
    (fun ω => X i ω ^ 4) μ) (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ 3 * σ ^ 4) (θ : ℝ),
      σ * Real.sqrt (Fintype.card ι / 3) ≤ ∫ ω, |θ + ∑ i, X i ω| ∂μ) =
    type_of% (@R56Audit.fact_2_2_general Ω ι) := rfl

-- The instance used in Lemma 2.3: independent uniform digits; "symmetric" is witnessed by a
-- permutation of the digits.
-- `fact_2_2_uniform` (UniformDigits)
example {ι D : Type*} : (∀ [Fintype ι] [DecidableEq ι] [Fintype D] [Nonempty D] (x : ι → D → ℝ)
    (φ : ι → D ≃ D) (hφ : ∀ i d, x i (φ i d) = -x i d) {σ : ℝ} (hσ : 0 < σ) (h2 : ∀ i, finAvg
    (fun d => x i d ^ 2) = σ ^ 2) (h4 : ∀ i, finAvg (fun d => x i d ^ 4) ≤ 3 * σ ^ 4) (θ : ℝ),
      σ * Real.sqrt (Fintype.card ι / 3) ≤ finAvg (fun r : ι → D => |θ + ∑ i, x i (r i)|)) =
    type_of% (@R56Audit.fact_2_2_uniform ι D) := rfl

-- `exists_symm_perm_iff` (SymmetricSums)
example {D : Type*} : (∀ [Fintype D] (x : D → ℝ),
      (∃ φ : D ≃ D, ∀ d, x (φ d) = -x d) ↔
        ∀ v : ℝ, Nat.card {d // x d = v} = Nat.card {d // x d = -v}) =
    type_of% (@R56Audit.exists_symm_perm_iff D) := rfl

-- The form in which the proof of Lemma 2.3 uses it: the shift `θ` may depend on the digits of
-- the other points ("condition on the children of all other points").
example {n : ℕ} {D : Type*} [Fintype D] (S : Finset (Fin n)) (x : Fin n → D → ℝ)
    (r : Fin n → D) : jumpSum S x r = ∑ i ∈ S, x i (r i) := rfl

-- `symmetric_sum_abs` (SymmetricSums)
example {n : ℕ} {D : Type*} : (∀ [Fintype D] [Nonempty D] (S : Finset (Fin n)) (x : Fin n → D →
    ℝ) (φ : Fin n → D ≃ D) (hφ : ∀ i ∈ S, ∀ d, x i (φ i d) = -x i d) {σ : ℝ} (hσ : 0 ≤ σ) (h2 :
    ∀ i ∈ S, finAvg (fun d => x i d ^ 2) = σ ^ 2) (h4 : ∀ i ∈ S, finAvg (fun d => x i d ^ 4) ≤ 3
    * σ ^ 4) (θ : (Fin n → D) → ℝ) (hθ : ∀ r r' : Fin n → D, (∀ i, i ∉ S → r i = r' i) → θ r = θ
    r'),
      σ * Real.sqrt (S.card / 3) ≤ finAvg (fun r : Fin n → D => |θ r + jumpSum S x r|)) =
    type_of% (@R56Audit.symmetric_sum_abs n D) := rfl

-- **Lemma 2.3.**
-- `local_gain` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (V : Fin n → ℝ)
    (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L),
      ∑ ℓ : Fin b, osc (block s L ℓ) (endpointAvg ε V side) +
          (1 / 4) * Real.sqrt (innerPoints b V side s L).card ≤
        finAvg (fun r : Fin n → Fin b =>
          ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k))) =
    type_of% @R56Audit.local_gain := rfl

-- Its proof. Step 1: `ā`, display (5).
example {n b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n → Fin b) (y : ℝ) :
    childMean ε V side r y = (∑ k : Fin b, childAvg ε V side r k y) / b := rfl

-- `card_mul_osc_avg_le` (Osc)
example {α : Type*} {ι : Type*} : (∀ [Fintype ι] [Nonempty ι] {B : Set α} {f : ι → α → ℝ} (hB :
    B.Nonempty) (hf : ∀ k, ((f k) '' B).Finite),
      (Fintype.card ι : ℝ) * osc B (fun y => (∑ k, f k y) / Fintype.card ι) ≤
        ∑ k, osc B (f k)) =
    type_of% (@R56Audit.card_mul_osc_avg_le α ι) := rfl

-- `display_5` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L :
    ℝ} (hL : 0 < L) (r : Fin n → Fin b),
      ∑ ℓ : Fin b, osc (block s L ℓ) (childMean ε V side r) +
          2 * |mid (block s L (b - 1)) (childMean ε V side r) -
            mid (block s L 0) (childMean ε V side r)| ≤
        ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k)) =
    type_of% @R56Audit.display_5 := rfl

-- `avg_comparison_core` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (J : Set ℝ) (B
    : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J) (hcomp : ∀ f : ℝ → ℝ, (f
    '' J).Finite → ∑ ℓ : Fin b, osc (B ℓ) f + 2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by
    omega⟩) f| ≤ b * osc J f) (r : Fin n → Fin b),
      ∑ ℓ : Fin b, osc (B ℓ) (childMean ε V side r) +
          2 * |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
            mid (B ⟨0, by omega⟩) (childMean ε V side r)| ≤
        ∑ k : Fin b, osc J (childAvg ε V side r k)) =
    type_of% @R56Audit.avg_comparison_core := rfl

-- Step 2: the jump `X_i = χ_i (b + 1 - 2r) / (2b)` for the child `C_r`, `r = d + 1`;
-- displays (6) and (7).
example {n : ℕ} (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) (d : Fin b) :
    jump b ε i d = ε i * (((b : ℝ) - 1 - 2 * (d : ℕ)) / (2 * b)) := rfl

-- `sum_childWeight` (LocalGain)
example : (∀ {b : ℕ} (hb : 0 < b) (sd : Side) (r : Fin b),
      (∑ k : Fin b, childWeight sd r k) / b =
        oldWeight sd + (if sd = Side.inside then ((b : ℝ) - 1 - 2 * (r : ℕ)) / (2 * b) else 0)) =
    type_of% @R56Audit.sum_childWeight := rfl

-- `display_6` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n →
    Fin b) (y : ℝ),
      childMean ε V side r y = endpointAvg ε V side y +
        ∑ i ∈ Finset.univ.filter (fun i => side i = Side.inside ∧ V i ≤ y), jump b ε i (r i)) =
    type_of% @R56Audit.display_6 := rfl

-- `childMean_eq` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n →
    Fin b) (y : ℝ),
      childMean ε V side r y =
        stepFn V (fun i => ε i * oldWeight (side i) +
          (if side i = Side.inside then jump b ε i (r i) else 0)) y) =
    type_of% @R56Audit.childMean_eq := rfl

-- `jump_rev` (LocalGain)
example : (∀ {n : ℕ} (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) (d : Fin b),
      jump b ε i (Fin.revPerm d) = -jump b ε i d) =
    type_of% @R56Audit.jump_rev := rfl

-- `finAvg_jump` (LocalGain)
example : (∀ {n : ℕ} (b : ℕ) (ε : Fin n → ℝ) (i : Fin n),
      finAvg (jump b ε i) = 0) =
    type_of% @R56Audit.finAvg_jump := rfl

-- `finAvg_childMean` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side) (y : ℝ),
      finAvg (fun r : Fin n → Fin b => childMean ε V side r y) = endpointAvg ε V side y) =
    type_of% @R56Audit.finAvg_childMean := rfl

-- Step 3: "The expectation of a maximum is at least the maximum of the expectations, and the
-- expectation of a minimum is at most the minimum of the expectations"; display (8).
-- `maxOn_endpointAvg_le` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side) {B : Set ℝ}
    (hB : B.Nonempty),
      maxOn B (endpointAvg ε V side) ≤
        finAvg (fun r : Fin n → Fin b => maxOn B (childMean ε V side r))) =
    type_of% @R56Audit.maxOn_endpointAvg_le := rfl

-- `finAvg_minOn_childMean_le` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side) {B : Set ℝ}
    (hB : B.Nonempty),
      finAvg (fun r : Fin n → Fin b => minOn B (childMean ε V side r)) ≤
        minOn B (endpointAvg ε V side)) =
    type_of% @R56Audit.finAvg_minOn_childMean_le := rfl

-- `osc_endpointAvg_le` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side) {B : Set ℝ}
    (hB : B.Nonempty),
      osc B (endpointAvg ε V side) ≤
        finAvg (fun r : Fin n → Fin b => osc B (childMean ε V side r))) =
    type_of% @R56Audit.osc_endpointAvg_le := rfl

-- `display_8` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L :
    ℝ} (hL : 0 < L),
      ∑ ℓ : Fin b, osc (block s L ℓ) (endpointAvg ε V side) +
          2 * finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
            mid (block s L 0) (childMean ε V side r)|) ≤
        finAvg (fun r : Fin n → Fin b =>
          ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k))) =
    type_of% @R56Audit.display_8 := rfl

-- `expected_comparison_core` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (J : Set ℝ) (B
    : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J) (hcomp : ∀ f : ℝ → ℝ, (f
    '' J).Finite → ∑ ℓ : Fin b, osc (B ℓ) f + 2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by
    omega⟩) f| ≤ b * osc J f),
      ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) +
          2 * finAvg (fun r : Fin n → Fin b =>
            |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
              mid (B ⟨0, by omega⟩) (childMean ε V side r)|) ≤
        finAvg (fun r : Fin n → Fin b => ∑ k : Fin b, osc J (childAvg ε V side r k))) =
    type_of% @R56Audit.expected_comparison_core := rfl

-- Step 4: `D`, `g`, `θ`.
example {n : ℕ} (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side) (S : Finset (Fin n))
    (r : Fin n → Fin b) (y : ℝ) :
    withoutJumps b ε V side S r y =
      ∑ i, if V i ≤ y then ε i * oldWeight (side i) +
        (if side i = Side.inside ∧ i ∉ S then jump b ε i (r i) else 0) else 0 := rfl

-- `withoutJumps_eq` (LocalGain)
example : (∀ {n : ℕ} (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side) (S : Finset (Fin n)) (r :
    Fin n → Fin b) (y : ℝ),
      withoutJumps b ε V side S r y = endpointAvg ε V side y +
        ∑ i ∈ Finset.univ.filter (fun i => side i = Side.inside ∧ i ∉ S ∧ V i ≤ y),
          jump b ε i (r i)) =
    type_of% @R56Audit.withoutJumps_eq := rfl

-- `innerPoints_between_blocks` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (V : Fin n → ℝ) (side : Fin n → Side) (s L : ℝ),
      ∀ i ∈ innerPoints b V side s L, side i = Side.inside ∧
        (∀ y ∈ block s L 0, y < V i) ∧ (∀ y ∈ block s L (b - 1), V i ≤ y)) =
    type_of% @R56Audit.innerPoints_between_blocks := rfl

-- `offset_eq` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L :
    ℝ} (hL : 0 < L) (r : Fin n → Fin b),
      mid (block s L (b - 1)) (childMean ε V side r) - mid (block s L 0) (childMean ε V side r) =
        (mid (block s L (b - 1)) (withoutJumps b ε V side (innerPoints b V side s L) r) -
          mid (block s L 0) (withoutJumps b ε V side (innerPoints b V side s L) r)) +
        jumpSum (innerPoints b V side s L) (jump b ε) r) =
    type_of% @R56Audit.offset_eq := rfl

-- `offset_core` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (B : Fin b →
    Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside
    ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧ (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y)) (r : Fin n → Fin
    b),
      mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
          mid (B ⟨0, by omega⟩) (childMean ε V side r) =
        (mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r)) +
        jumpSum S (jump b ε) r) =
    type_of% @R56Audit.offset_core := rfl

-- The moments of the jumps: "`X_i² = (r - (b+1)/2)²/b²` \[…\] `r` has mean `(b+1)/2` and
-- second moment `(b+1)(2b+1)/6`, so its variance is \[…\] `(b²-1)/12`. Also
-- `|X_i| ≤ (b-1)/(2b)`. Hence `E X_i² = (b²-1)/(12b²)`", and the chain for `E X_i⁴`.
-- `jump_sq_eq` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n) (d : Fin b),
      jump b ε i d ^ 2 = ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2 / (b : ℝ) ^ 2) =
    type_of% @R56Audit.jump_sq_eq := rfl

-- `finAvg_childIndex` (LocalGain)
example : (∀ {b : ℕ} (hb : 0 < b),
      finAvg (fun d : Fin b => ((d : ℕ) : ℝ) + 1) = ((b : ℝ) + 1) / 2) =
    type_of% @R56Audit.finAvg_childIndex := rfl

-- `finAvg_childIndex_sq` (LocalGain)
example : (∀ {b : ℕ} (hb : 0 < b),
      finAvg (fun d : Fin b => (((d : ℕ) : ℝ) + 1) ^ 2) = ((b : ℝ) + 1) * (2 * b + 1) / 6) =
    type_of% @R56Audit.finAvg_childIndex_sq := rfl

-- `finAvg_childIndex_var` (LocalGain)
example : (∀ {b : ℕ} (hb : 0 < b),
      finAvg (fun d : Fin b => ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2) =
          ((b : ℝ) + 1) * (2 * b + 1) / 6 - ((b : ℝ) + 1) ^ 2 / 4 ∧
        ((b : ℝ) + 1) * (2 * b + 1) / 6 - ((b : ℝ) + 1) ^ 2 / 4 = ((b : ℝ) ^ 2 - 1) / 12) =
    type_of% @R56Audit.finAvg_childIndex_var := rfl

-- `abs_jump_le` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n) (d :
    Fin b),
      |jump b ε i d| ≤ ((b : ℝ) - 1) / (2 * b)) =
    type_of% @R56Audit.abs_jump_le := rfl

-- `finAvg_jump_sq` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n),
      finAvg (fun d : Fin b => jump b ε i d ^ 2) = ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) =
    type_of% @R56Audit.finAvg_jump_sq := rfl

-- `finAvg_jump_fourth_le_sq` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n),
      finAvg (fun d : Fin b => jump b ε i d ^ 4) ≤
        (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2))) =
    type_of% @R56Audit.finAvg_jump_fourth_le_sq := rfl

-- `sq_mul_sigma_sq_le` (LocalGain)
example : (∀ {b : ℕ} (hb : 0 < b),
      (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ≤
          ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ∧
        ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) =
          3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2) =
    type_of% @R56Audit.sq_mul_sigma_sq_le := rfl

-- `finAvg_jump_fourth_le` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n),
      finAvg (fun d : Fin b => jump b ε i d ^ 4) ≤
        3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2) =
    type_of% @R56Audit.finAvg_jump_fourth_le := rfl

-- The last display: `E|…| ≥ σ√(m_R/3) = (√(b²-1)/(6b)) √(m_R) ≥ √(m_R)/8`.
-- `expected_offset_ge_sigma` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (V : Fin n → ℝ)
    (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L),
      Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) *
          Real.sqrt ((innerPoints b V side s L).card / 3) ≤
        finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
          mid (block s L 0) (childMean ε V side r)|)) =
    type_of% @R56Audit.expected_offset_ge_sigma := rfl

-- `expected_offset_core_sigma` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (V : Fin n → ℝ)
    (side : Fin n → Side) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧ (∀ y ∈ B ⟨b - 1, by
    omega⟩, V i ≤ y)),
      Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (S.card / 3) ≤
        finAvg (fun r : Fin n → Fin b =>
          |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
            mid (B ⟨0, by omega⟩) (childMean ε V side r)|)) =
    type_of% @R56Audit.expected_offset_core_sigma := rfl

-- `sigma_mul_sqrt_eq` (LocalGain)
example : (∀ {b : ℕ} (hb : 0 < b) (m : ℕ),
      Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (m / 3) =
        Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m) =
    type_of% @R56Audit.sigma_mul_sqrt_eq := rfl

-- `sqrt_sq_sub_one_div_ge` (LocalGain)
example : (∀ {b : ℕ} (hb : 2 ≤ b) (m : ℕ),
      Real.sqrt m / 8 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m) =
    type_of% @R56Audit.sqrt_sq_sub_one_div_ge := rfl

-- `sqrt_div_eight_le` (LocalGain)
example : (∀ {b : ℕ} (hb : 2 ≤ b) (m : ℕ),
      Real.sqrt m / 8 ≤
        Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (m / 3)) =
    type_of% @R56Audit.sqrt_div_eight_le := rfl

-- `expected_offset_ge` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (V : Fin n → ℝ)
    (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L),
      Real.sqrt (innerPoints b V side s L).card / 8 ≤
        finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
          mid (block s L 0) (childMean ε V side r)|)) =
    type_of% @R56Audit.expected_offset_ge := rfl

-- `expected_offset_core` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (V : Fin n → ℝ)
    (side : Fin n → Side) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧ (∀ y ∈ B ⟨b - 1, by
    omega⟩, V i ≤ y)),
      Real.sqrt S.card / 8 ≤
        finAvg (fun r : Fin n → Fin b =>
          |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
            mid (B ⟨0, by omega⟩) (childMean ε V side r)|)) =
    type_of% @R56Audit.expected_offset_core := rfl

-- Lemma 2.3 for arbitrary sets of heights in place of the blocks.
-- `local_gain_core` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (V : Fin n → ℝ)
    (side : Fin n → Side) (J : Set ℝ) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀
    ℓ, B ℓ ⊆ J) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by
    omega⟩, y < V i) ∧ (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y)) (hcomp : ∀ f : ℝ → ℝ, (f ''
    J).Finite → ∑ ℓ : Fin b, osc (B ℓ) f + 2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by
    omega⟩) f| ≤ b * osc J f),
      ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) + (1 / 4) * Real.sqrt S.card ≤
        finAvg (fun r : Fin n → Fin b => ∑ k : Fin b, osc J (childAvg ε V side r k))) =
    type_of% @R56Audit.local_gain_core := rfl

-- `local_gain_sets` (LocalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (V : Fin n → ℝ)
    (side : Fin n → Side) (J : Set ℝ) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀
    ℓ, B ℓ ⊆ J) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by
    omega⟩, y < V i) ∧ (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y)),
      ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) + (1 / 4) * Real.sqrt S.card ≤
        finAvg (fun r : Fin n → Fin b => ∑ k : Fin b, osc J (childAvg ε V side r k))) =
    type_of% @R56Audit.local_gain_sets := rfl

-- **What one rectangle gives**: `E‖F‖∞ ≥ √(m_R)/(8b)` when the heights are fixed.
example (n : ℕ) : heightSigma n =
    MeasurableSpace.comap (fun (P : Fin n → ℝ × ℝ) (i : Fin n) => (P i).2) inferInstance := rfl

example (b : ℕ) :
    unitInnerRegion b = Set.Icc (0 : ℝ) 1 ×ˢ Set.Ico (1 / (b : ℝ)) (1 - 1 / (b : ℝ)) := rfl

example {n : ℕ} (b : ℕ) (P : Fin n → ℝ × ℝ) :
    unitInnerCount b P = (Finset.univ.filter (fun i => P i ∈ unitInnerRegion b)).card := rfl

-- `one_rectangle` (OneRectangle)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (χ : Fin n → ℤˣ),
      ∀ᵐ P ∂unifPts n, Real.sqrt (unitInnerCount b P) / (8 * (b : ℝ)) ≤
        ((unifPts n)[supNorm χ | heightSigma n]) P) =
    type_of% @R56Audit.one_rectangle := rfl

/-! ## Section 2.4. All scales -/

/-! ### Partitions and potential, displays (1) and (9) -/

-- Stage `j`: horizontal intervals `[c/b^j, (c+1)/b^j]`, vertical intervals
-- `[v b^{j-h}, (v+1) b^{j-h})`, and their products, the cells.
example (b j c : ℕ) :
    hcell b j c = Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) := rfl

example (b h j : ℕ) : vlen b h j = (b : ℝ) ^ j / (b : ℝ) ^ h := rfl

example (b h j v : ℕ) :
    vcell b h j v = Set.Ico (v * ((b : ℝ) ^ j / (b : ℝ) ^ h)) ((v + 1) * ((b : ℝ) ^ j / (b : ℝ) ^ h)) :=
  rfl

example (b h j c v : ℕ) : cell b h j c v = hcell b j c ×ˢ vcell b h j v := rfl

-- `iUnion_hcell` (StageGeometry)
example : (∀ {b : ℕ} (hb : 0 < b) (j : ℕ),
      ⋃ c : Fin (b ^ j), hcell b j c = Set.Icc (0 : ℝ) 1) =
    type_of% @R56Audit.iUnion_hcell := rfl

-- `iUnion_vcell` (StageGeometry)
example : (∀ {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h),
      ⋃ v : Fin (b ^ (h - j)), vcell b h j v = Set.Ico (0 : ℝ) 1) =
    type_of% @R56Audit.iUnion_vcell := rfl

-- `vcell_disjoint` (StageGeometry)
example : (∀ {b : ℕ} (hb : 0 < b) (h j : ℕ) {v v' : ℕ} (hv : v ≠ v'),
      Disjoint (vcell b h j v) (vcell b h j v')) =
    type_of% @R56Audit.vcell_disjoint := rfl

-- `iUnion_cell` (StageGeometry)
example : (∀ {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h),
      ⋃ c : Fin (b ^ j), ⋃ v : Fin (b ^ (h - j)), cell b h j c v =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
    type_of% @R56Audit.iUnion_cell := rfl

-- `card_cells_stage` (StageGeometry)
example : (∀ {b h j : ℕ} (hj : j ≤ h),
      Fintype.card (Fin (b ^ j) × Fin (b ^ (h - j))) = b ^ h) =
    type_of% @R56Audit.card_cells_stage := rfl

-- `volume_cell` (StageGeometry)
example : (∀ {b : ℕ} (hb : 0 < b) (h j c v : ℕ),
      volume (cell b h j c v) = ENNReal.ofReal (1 / (b : ℝ) ^ h)) =
    type_of% @R56Audit.volume_cell := rfl

-- The potential, display (1).
example {n : ℕ} (χ : Fin n → ℤˣ) (b h j : ℕ) (P : Fin n → ℝ × ℝ) :
    Zpot χ b h j P =
      (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
        osc (vcell b h j v)
          (endAvg χ P (((c : ℕ) : ℝ) / (b : ℝ) ^ j) ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j))) /
        (b : ℝ) ^ h := rfl

-- Display (9).
-- `Zpot_nonneg` (Potential)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (h j : ℕ) (P : Fin n → ℝ × ℝ),
      0 ≤ Zpot χ b h j P) =
    type_of% @R56Audit.Zpot_nonneg := rfl

-- `Zpot_le_two_supNorm` (Potential)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ),
      Zpot χ b h j P ≤ 2 * supNorm χ P) =
    type_of% @R56Audit.Zpot_le_two_supNorm := rfl

-- `measurable_Zpot` (Measurability)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (h j : ℕ),
      Measurable (Zpot χ b h j)) =
    type_of% @R56Audit.measurable_Zpot := rfl

/-! ### The σ-fields `𝓕_j` and the next digits -/

-- The `k`-th base-`b` digit of `u` (after the point), and `𝓕_j`: "the σ-field generated by
-- all heights and by the first `j` base-`b` digits of every horizontal coordinate".
example (b k : ℕ) (u : ℝ) : digit b k u = ⌊(b : ℝ) ^ k * u⌋₊ % b := rfl

example (n b j : ℕ) (P : Fin n → ℝ × ℝ) :
    digitInfo n b j P = (fun i => (P i).2, fun i (k : Fin j) => digit b ((k : ℕ) + 1) (P i).1) :=
  rfl

example (n b j : ℕ) : digitSigma n b j = MeasurableSpace.comap (digitInfo n b j) inferInstance :=
  rfl

-- `measurable_digitInfo` (Digits)
example : (∀ (n b j : ℕ),
      Measurable (digitInfo n b j)) =
    type_of% @R56Audit.measurable_digitInfo := rfl

-- The σ-field used in the proofs: generated by all heights and by the index `c` of the
-- stage-`j` interval `(c/b^j, (c+1)/b^j]` that contains each horizontal coordinate.
example (k : ℕ) (u : ℝ) : gridIndex k u = ⌈(k : ℝ) * u⌉ - 1 := rfl

example (n k : ℕ) (P : Fin n → ℝ × ℝ) :
    coarseInfo n k P = (fun i => (P i).2, fun i => gridIndex k (P i).1) := rfl

example (n b j : ℕ) :
    stageSigma n b j = MeasurableSpace.comap (coarseInfo n (b ^ j)) inferInstance := rfl

-- `stageSigma_le` (StageFiltration)
example : (∀ (n b j : ℕ),
      stageSigma n b j ≤ (inferInstance : MeasurableSpace (Fin n → ℝ × ℝ))) =
    type_of% @R56Audit.stageSigma_le := rfl

-- `stageSigma_succ_le` (StageFiltration)
example : (∀ {b : ℕ} (hb : 0 < b) (n j : ℕ),
      stageSigma n b j ≤ stageSigma n b (j + 1)) =
    type_of% @R56Audit.stageSigma_succ_le := rfl

-- "The first `j` digits of `U_i` determine the stage-`j` horizontal interval that contains
-- `U_i`", and conversely; hence conditional expectations given the two σ-fields agree.
example (b j : ℕ) (d : Fin j → ℕ) :
    idxOfDigits b j d = ∑ k : Fin j, (b : ℤ) ^ (j - ((k : ℕ) + 1)) * (d k : ℤ) := rfl

example (b j : ℕ) (g : ℤ) (k : Fin j) :
    digitsOfIdx b j g k = ((g / (b : ℤ) ^ (j - ((k : ℕ) + 1))) % (b : ℤ)).toNat := rfl

example (n b j : ℕ) (p : (Fin n → ℝ) × (Fin n → Fin j → ℕ)) :
    coarseOfDigits n b j p = (p.1, fun i => idxOfDigits b j (p.2 i)) := rfl

example (n b j : ℕ) (p : (Fin n → ℝ) × (Fin n → ℤ)) :
    digitsOfCoarse n b j p = (p.1, fun i => digitsOfIdx b j (p.2 i)) := rfl

-- `gridIndex_eq_idxOfDigits` (Digits)
example : (∀ {b : ℕ} (hb : 0 < b) (j : ℕ) {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) (hgrid : ∀ (m :
    ℤ) (r : ℕ), u ≠ (m : ℝ) / (b : ℝ) ^ r),
      gridIndex (b ^ j) u = idxOfDigits b j (fun k => digit b ((k : ℕ) + 1) u)) =
    type_of% @R56Audit.gridIndex_eq_idxOfDigits := rfl

-- `coarseInfo_ae_eq_digitInfo` (Digits)
example : (∀ {b : ℕ} (hb : 0 < b) (n j : ℕ),
      coarseInfo n (b ^ j) =ᵐ[unifPts n] coarseOfDigits n b j ∘ digitInfo n b j) =
    type_of% @R56Audit.coarseInfo_ae_eq_digitInfo := rfl

-- `digitInfo_ae_eq_coarseInfo` (Digits)
example : (∀ {b : ℕ} (hb : 0 < b) (n j : ℕ),
      digitInfo n b j =ᵐ[unifPts n] digitsOfCoarse n b j ∘ coarseInfo n (b ^ j)) =
    type_of% @R56Audit.digitInfo_ae_eq_coarseInfo := rfl

-- `condExp_digitSigma` (Digits)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (j : ℕ) (f : (Fin n → ℝ × ℝ) → ℝ),
      (unifPts n)[f | digitSigma n b j] =ᵐ[unifPts n] (unifPts n)[f | stageSigma n b j]) =
    type_of% @R56Audit.condExp_digitSigma := rfl

-- "So `Z_j` is `𝓕_j`-measurable."
-- `Zpot_aestronglyMeasurable_digits` (Digits)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (χ : Fin n → ℤˣ),
      AEStronglyMeasurable[digitSigma n b j] (Zpot χ b h j) (unifPts n)) =
    type_of% @R56Audit.Zpot_aestronglyMeasurable_digits := rfl

-- `Zpot_aestronglyMeasurable` (ConditionalGain)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (χ : Fin n → ℤˣ),
      AEStronglyMeasurable[stageSigma n b j] (Zpot χ b h j) (unifPts n)) =
    type_of% @R56Audit.Zpot_aestronglyMeasurable := rfl

-- "The `(j+1)`-st digits \[…\] are independent and uniform conditional on `𝓕_j`."
example {b : ℕ} (hb : 0 < b) (n j : ℕ) (P : Fin n → ℝ × ℝ) (i : Fin n) :
    ((nextDigits hb n j P i : Fin b) : ℕ) = digit b (j + 1) (P i).1 := rfl

-- `measurable_nextDigits` (Digits)
example : (∀ {b : ℕ} (hb : 0 < b) (n j : ℕ),
      Measurable (nextDigits hb n j)) =
    type_of% @R56Audit.measurable_nextDigits := rfl

-- `condExp_nextDigits` (Digits)
example : (∀ {b : ℕ} (hb : 0 < b) (n j : ℕ) (H : (Fin n → ℝ) × (Fin n → Fin j → ℕ) → (Fin n →
    Fin b) → ℝ) (hH : ∀ r, Measurable fun p => H p r) (K : ℝ) (hK : ∀ p r, |H p r| ≤ K),
      (unifPts n)[fun P => H (digitInfo n b j P) (nextDigits hb n j P) | digitSigma n b j]
        =ᵐ[unifPts n] fun P => finAvg (fun r => H (digitInfo n b j P) r)) =
    type_of% @R56Audit.condExp_nextDigits := rfl

-- The form used in the proofs: the next digit is the archive's `freshGridIndex`, the position
-- of the stage-`(j+1)` interval inside the stage-`j` interval; it is the `(j+1)`-st digit off
-- the grid lines. The conditional law is the archive's `Riesz.condExp_freshGrid_with_past`.
example (k m : ℕ) (hm : 0 < m) (u : ℝ) :
    ((freshGridIndex k m hm u : ℕ) : ℤ) = gridIndex (k * m) u % (m : ℤ) := by
  -- for `k > 0` this is the archive's `freshGridIndex_eq_emod`; for `k = 0` both sides are `m - 1`
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
    have h0 : ((0 : ℕ) : ℝ) * u - ((gridIndex 0 u : ℤ) : ℝ) = 1 := by simp [gridIndex]
    have hg : gridIndex m 1 = (m : ℤ) - 1 := by simp [gridIndex]
    have hr : gridIndex (0 * m) u % (m : ℤ) = (m : ℤ) - 1 := by
      have e : gridIndex (0 * m) u = -1 := by simp [gridIndex]
      rw [e, ← Int.add_emod_right (-1) (m : ℤ)]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hr]
    unfold freshGridIndex
    rw [h0]
    unfold Riesz.Occupancy.finiteGridIndex
    rw [dite_eq_left_of_eq_true (eq_true h1)]
    simp only [hg]
    omega
  · exact freshGridIndex_eq_emod k m hk hm u

example (n k m : ℕ) (hm : 0 < m) (P : Fin n → ℝ × ℝ) (i : Fin n) :
    freshInfo n k m hm P i = freshGridIndex k m hm (P i).1 := rfl

-- `fresh_eq_digit` (Digits)
example : (∀ {b : ℕ} (hb : 0 < b) (k : ℕ) {u : ℝ} (hu : 0 < u) (hgrid : ∀ (m : ℤ) (r : ℕ), u ≠
    (m : ℝ) / (b : ℝ) ^ r),
      (freshGridIndex (b ^ k) b hb u : ℕ) = digit b (k + 1) u) =
    type_of% @R56Audit.fresh_eq_digit := rfl

-- `nextDigits_ae_eq_freshInfo` (Digits)
example : (∀ {b : ℕ} (hb : 0 < b) (n j : ℕ),
      nextDigits hb n j =ᵐ[unifPts n] freshInfo n (b ^ j) b hb) =
    type_of% @R56Audit.nextDigits_ae_eq_freshInfo := rfl

-- Some statements that are used inside the proofs are written for the law of the points with
-- the two coordinates separated, the archive's `pointSampleLaw`. It is the law `unifPts`.
example : μI = (volume : Measure ℝ).restrict (Set.Icc 0 1) := rfl

example (n : ℕ) : pointSampleLaw n = Measure.pi fun _ : Fin n => μI.prod μI := rfl

example (n : ℕ) : pointSampleLaw n = unifPts n := pointSampleLaw_eq_unifPts n

-- `condExp_fresh_given_heights` (ConditionalLaw)
example : (∀ (n k m : ℕ) (hk : 0 < k) (hm : 0 < m) (H : (Fin n → ℝ) × (Fin n → ℤ) → (Fin n → Fin
    m) → ℝ) (hH : ∀ r, Measurable (fun p => H p r)) (K : ℝ) (hK : ∀ p r, |H p r| ≤ K),
      (pointSampleLaw n)[fun P => H (coarseInfo n k P) (freshInfo n k m hm P) |
          MeasurableSpace.comap (coarseInfo n k) inferInstance] =ᵐ[pointSampleLaw n]
        fun P => finAvg (fun r => H (coarseInfo n k P) r)) =
    type_of% @R56Audit.condExp_fresh_given_heights := rfl

-- `iIndepFun_fresh` (StageFiltration)
example : (∀ (n k m : ℕ) (hm : 0 < m),
      iIndepFun (fun (i : Fin n) (P : Fin n → ℝ × ℝ) => freshGridIndex k m hm (P i).1)
        (pointSampleLaw n)) =
    type_of% @R56Audit.iIndepFun_fresh := rfl

-- `indepFun_coarse_fresh` (StageFiltration)
example : (∀ (n k m : ℕ) (hk : 0 < k) (hm : 0 < m),
      IndepFun (coarseInfo n k) (freshInfo n k m hm) (pointSampleLaw n)) =
    type_of% @R56Audit.indepFun_coarse_fresh := rfl

/-! ### The plan, display (10) -/

-- The fluctuation term `T`, with `𝓕_j` generated by digits and by interval indices.
example {n : ℕ} (χ : Fin n → ℤˣ) (b h : ℕ) (P : Fin n → ℝ × ℝ) :
    fluctDigits χ b h P = ∑ j ∈ Finset.range h,
      (Zpot χ b h (j + 1) P - ((unifPts n)[Zpot χ b h (j + 1) | digitSigma n b j]) P) := rfl

example {n : ℕ} (χ : Fin n → ℤˣ) (b h : ℕ) (P : Fin n → ℝ × ℝ) :
    fluct χ b h P = ∑ j ∈ Finset.range h,
      (Zpot χ b h (j + 1) P - ((unifPts n)[Zpot χ b h (j + 1) | stageSigma n b j]) P) := rfl

-- `fluctDigits_ae_eq` (Digits)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ),
      fluctDigits χ b h =ᵐ[unifPts n] fluct χ b h) =
    type_of% @R56Audit.fluctDigits_ae_eq := rfl

-- `measurableSet_fluctDigits_le` (Measurability)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (h : ℕ) (lam : ℝ),
      MeasurableSet {P : Fin n → ℝ × ℝ | fluctDigits χ b h P ≤ -lam}) =
    type_of% @R56Audit.measurableSet_fluctDigits_le := rfl

-- `measurableSet_fluct_le` (Measurability)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (h : ℕ) (lam : ℝ),
      MeasurableSet {P : Fin n → ℝ × ℝ | fluct χ b h P ≤ -lam}) =
    type_of% @R56Audit.measurableSet_fluct_le := rfl

-- Display (10).
-- `roadmap_digits` (Digits)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ),
      ∀ᵐ P ∂unifPts n, Zpot χ b h h P = Zpot χ b h 0 P +
        ∑ j ∈ Finset.range h,
          ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | digitSigma n b j]) P +
        fluctDigits χ b h P) =
    type_of% @R56Audit.roadmap_digits := rfl

-- `roadmap` (ConditionalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ),
      ∀ᵐ P ∂unifPts n, Zpot χ b h h P = Zpot χ b h 0 P +
        ∑ j ∈ Finset.range h,
          ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | stageSigma n b j]) P +
        fluct χ b h P) =
    type_of% @R56Audit.roadmap := rfl

/-! ### Transitions, comparison rectangles, Lemma 2.4 -/

-- The comparison rectangle of the transition `j → j+1` with indices `(c, v)`: one old
-- horizontal interval times one new vertical interval.
example (b h j c v : ℕ) : compRect b h j c v = hcell b j c ×ˢ vcell b h (j + 1) v := rfl

-- `hcell_eq_iUnion_children` (StageGeometry)
example : (∀ {b : ℕ} (hb : 0 < b) (j c : ℕ),
      hcell b j c = ⋃ k : Fin b, hcell b (j + 1) (b * c + k)) =
    type_of% @R56Audit.hcell_eq_iUnion_children := rfl

-- `vcell_succ_eq_iUnion` (StageGeometry)
example : (∀ {b : ℕ} (hb : 0 < b) (h j v : ℕ),
      vcell b h (j + 1) v = ⋃ ℓ : Fin b, vcell b h j (b * v + ℓ)) =
    type_of% @R56Audit.vcell_succ_eq_iUnion := rfl

-- `compRect_eq_iUnion_old` (StageGeometry)
example : (∀ {b : ℕ} (hb : 0 < b) (h j c v : ℕ),
      compRect b h j c v = ⋃ ℓ : Fin b, cell b h j c (b * v + ℓ)) =
    type_of% @R56Audit.compRect_eq_iUnion_old := rfl

-- `compRect_eq_iUnion_new` (StageGeometry)
example : (∀ {b : ℕ} (hb : 0 < b) (h j c v : ℕ),
      compRect b h j c v = ⋃ k : Fin b, cell b h (j + 1) (b * c + k) v) =
    type_of% @R56Audit.compRect_eq_iUnion_new := rfl

-- `card_compRect` (Crowding)
example : (∀ {b h j : ℕ} (hj : j < h),
      Fintype.card (Fin (b ^ j) × Fin (b ^ (h - j - 1))) = b ^ (h - 1)) =
    type_of% @R56Audit.card_compRect := rfl

-- `volume_compRect` (StageGeometry)
example : (∀ {b h j : ℕ} (hb : 0 < b) (hj : j < h) (c v : ℕ),
      volume (compRect b h j c v) = ENNReal.ofReal (1 / (b : ℝ) ^ (h - 1))) =
    type_of% @R56Audit.volume_compRect := rfl

-- The inner region: the comparison rectangle without its bottom and top old cells.
example (b h j c v : ℕ) :
    innerRegion b h j c v =
      Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
        Set.Ico (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h)
          ((((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h) := rfl

-- `innerRegion_eq_diff` (StageGeometry)
example : (∀ {b : ℕ} (hb : 0 < b) (h j c v : ℕ),
      innerRegion b h j c v =
        compRect b h j c v \ (cell b h j c (b * v) ∪ cell b h j c (b * v + (b - 1)))) =
    type_of% @R56Audit.innerRegion_eq_diff := rfl

-- `innerRegion_eq_iUnion` (StageGeometry)
example : (∀ {b : ℕ} (hb : 2 ≤ b) (h j c v : ℕ),
      innerRegion b h j c v = ⋃ ℓ ∈ Finset.Ico 1 (b - 1), cell b h j c (b * v + ℓ)) =
    type_of% @R56Audit.innerRegion_eq_iUnion := rfl

-- `m_R` and `δ_j`.
example {n : ℕ} (b h j : ℕ) (P : Fin n → ℝ × ℝ) (c v : ℕ) :
    innerCount b h j P c v = (Finset.univ.filter (fun i => P i ∈ innerRegion b h j c v)).card :=
  rfl

example {n : ℕ} (b h j : ℕ) (P : Fin n → ℝ × ℝ) :
    delta b h j P =
      (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), Real.sqrt (innerCount b h j P c v)) /
        (4 * (b : ℝ) * (b : ℝ) ^ (h - 1)) := rfl

-- **Lemma 2.4**, display (11).
-- `lemma_2_4_digits` (Digits)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) (χ : Fin n → ℤˣ),
      ∀ᵐ P ∂unifPts n, delta b h j P ≤
        ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | digitSigma n b j]) P) =
    type_of% @R56Audit.lemma_2_4_digits := rfl

-- `lemma_2_4` (ConditionalGain)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) (χ : Fin n → ℤˣ),
      ∀ᵐ P ∂unifPts n, delta b h j P ≤
        ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | stageSigma n b j]) P) =
    type_of% @R56Audit.lemma_2_4 := rfl

-- Its proof works with the potential as a function of the heights `V` and of the interval
-- indices `g`, and with `δ_j` as a function of them; refining the indices by the next digits
-- `r` gives the next stage.
example {n : ℕ} (ε : Fin n → ℝ) (b h j : ℕ) (V : Fin n → ℝ) (g : Fin n → ℤ) :
    Zstep ε b h j V g =
      (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
        osc (vcell b h j v) (endpointAvg ε V (fun i => sideIdx (g i) c))) / (b : ℝ) ^ h := rfl

example (g : ℤ) (c : ℕ) :
    sideIdx g c = if g < c then Side.left else if g = c then Side.inside else Side.right := rfl

example {n b : ℕ} (g : Fin n → ℤ) (r : Fin n → Fin b) (i : Fin n) :
    refineIdx g r i = (b : ℤ) * g i + ((r i : ℕ) : ℤ) := rfl

example {n : ℕ} (b h j : ℕ) (V : Fin n → ℝ) (g : Fin n → ℤ) (c v : ℕ) :
    innerSet b h j V g c v =
      innerPoints b V (fun i => sideIdx (g i) c) ((v : ℝ) * vlen b h (j + 1)) (vlen b h j) := rfl

example {n : ℕ} (b h j : ℕ) (V : Fin n → ℝ) (g : Fin n → ℤ) :
    deltaStep b h j V g =
      (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)),
        Real.sqrt ((innerSet b h j V g c v).card)) / (4 * (b : ℝ) * (b : ℝ) ^ (h - 1)) := rfl

-- `Zpot_eq_Zstep` (Potential)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (h j : ℕ) (P : Fin n → ℝ × ℝ) (hP : ∀
    i, 0 ≤ (P i).1 ∧ 0 ≤ (P i).2),
      Zpot χ b h j P =
        Zstep (sgn χ) b h j (fun i => (P i).2) (fun i => gridIndex (b ^ j) (P i).1)) =
    type_of% @R56Audit.Zpot_eq_Zstep := rfl

-- `gridIndex_succ` (Potential)
example : (∀ {b : ℕ} (hb : 0 < b) (j : ℕ) (u : ℝ),
      gridIndex (b ^ (j + 1)) u =
        (b : ℤ) * gridIndex (b ^ j) u + ((freshGridIndex (b ^ j) b hb u : ℕ) : ℤ)) =
    type_of% @R56Audit.gridIndex_succ := rfl

-- `innerCount_eq_card_innerSet` (ConditionalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h j c v : ℕ) (P : Fin n → ℝ × ℝ) (hgrid : NoGrid b
    P),
      innerCount b h j P c v =
        (innerSet b h j (coarseInfo n (b ^ j) P).1 (coarseInfo n (b ^ j) P).2 c v).card) =
    type_of% @R56Audit.innerCount_eq_card_innerSet := rfl

-- `delta_eq_deltaStep` (ConditionalGain)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h j : ℕ) (P : Fin n → ℝ × ℝ) (hgrid : NoGrid b P),
      delta b h j P =
        deltaStep b h j (coarseInfo n (b ^ j) P).1 (coarseInfo n (b ^ j) P).2) =
    type_of% @R56Audit.delta_eq_deltaStep := rfl

-- "Every old cell is a horizontal strip of exactly one comparison rectangle `R = I × J`, and
-- every new cell is a vertical strip of exactly one. So \[…\]
-- `bM (Z_{j+1} - Z_j) = Σ_R (Σ_k osc_J a^{(C_k)} - Σ_ℓ osc_{B_ℓ} a^{(I)})`": the two sums.
-- `Zstep_eq_sum_blocks` (StageGain)
example : (∀ {n : ℕ} {b h j : ℕ} (hj : j < h) (ε V : Fin n → ℝ) (g : Fin n → ℤ),
      Zstep ε b h j V g =
        (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), ∑ ℓ : Fin b,
          osc (block ((v : ℝ) * vlen b h (j + 1)) (vlen b h j) ℓ)
            (endpointAvg ε V (fun i => sideIdx (g i) c))) / (b : ℝ) ^ h) =
    type_of% @R56Audit.Zstep_eq_sum_blocks := rfl

-- `Zstep_succ_eq_sum_children` (StageGain)
example : (∀ {n : ℕ} {b : ℕ} (h j : ℕ) (ε V : Fin n → ℝ) (g : Fin n → ℤ) (r : Fin n → Fin b),
      Zstep ε b h (j + 1) V (refineIdx g r) =
        (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), ∑ k : Fin b,
          osc (Set.Ico ((v : ℝ) * vlen b h (j + 1)) ((v : ℝ) * vlen b h (j + 1) + b * vlen b h j))
            (childAvg ε V (fun i => sideIdx (g i) c) r k)) / (b : ℝ) ^ h) =
    type_of% @R56Audit.Zstep_succ_eq_sum_children := rfl

-- "So Lemma 2.3 bounds the conditional expectation of each term, and dividing by `bM` gives
-- (11)", with the conditional expectation written as the average over the next digits.
-- `Zstep_gain` (StageGain)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (g : Fin n → ℤ),
      Zstep ε b h j V g + deltaStep b h j V g ≤
        finAvg (fun r : Fin n → Fin b => Zstep ε b h (j + 1) V (refineIdx g r))) =
    type_of% @R56Audit.Zstep_gain := rfl

example {n : ℕ} (ε : Fin n → ℝ) (b h j : ℕ) (P : Fin n → ℝ × ℝ) :
    Zproc ε b h j P =
      Zstep ε b h (min j h) (coarseInfo n (b ^ min j h) P).1 (coarseInfo n (b ^ min j h) P).2 :=
  rfl

example {n : ℕ} (ε : Fin n → ℝ) (b h j : ℕ) (P : Fin n → ℝ × ℝ) :
    Zmean ε b h j P = finAvg (fun r : Fin n → Fin b =>
      Zstep ε b h (j + 1) (coarseInfo n (b ^ j) P).1 (refineIdx (coarseInfo n (b ^ j) P).2 r)) :=
  rfl

-- `Zpot_ae_eq_Zproc` (StageFiltration)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (χ : Fin n → ℤˣ),
      Zpot χ b h j =ᵐ[pointSampleLaw n] Zproc (sgn χ) b h j) =
    type_of% @R56Audit.Zpot_ae_eq_Zproc := rfl

-- `condExp_Zproc_succ` (StageFiltration)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤
    1),
      (pointSampleLaw n)[Zproc ε b h (j + 1) | stageSigma n b j] =ᵐ[pointSampleLaw n]
        Zmean ε b h j) =
    type_of% @R56Audit.condExp_Zproc_succ := rfl

-- `condExp_gain` (ConditionalGain)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j < h) (χ : Fin n → ℤˣ),
      (pointSampleLaw n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | stageSigma n b j]
        =ᵐ[pointSampleLaw n]
        fun P => ((pointSampleLaw n)[Zpot χ b h (j + 1) | stageSigma n b j]) P - Zpot χ b h j P) =
    type_of% @R56Audit.condExp_gain := rfl

/-! ### Good transitions, Lemma 2.5 -/

example {n : ℕ} (b h j : ℕ) (P : Fin n → ℝ × ℝ) (c v : ℕ) :
    Heavy b h j P c v ↔ (b : ℝ) * n / (b : ℝ) ^ (h - 1) < innerCount b h j P c v := Iff.rfl

example {n : ℕ} (b h j : ℕ) (P : Fin n → ℝ × ℝ) :
    GoodTransition b h j P ↔
      (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
        P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)).card := Iff.rfl

-- `measurableSet_goodTransition` (GoodTransitions)
example : (∀ {n : ℕ} (b h j : ℕ),
      MeasurableSet {P : Fin n → ℝ × ℝ | GoodTransition b h j P}) =
    type_of% @R56Audit.measurableSet_goodTransition := rfl

-- Display (12).
example (n b h : ℕ) :
    deltaStar n b h = 1 / (8 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1)) := rfl

-- **Lemma 2.5 (i).**
-- `lemma_2_5_i` (GoodTransitions)
example : (∀ {n : ℕ} {b h j : ℕ} (hn : 0 < n) (hb : 0 < b) (P : Fin n → ℝ × ℝ) (hG :
    GoodTransition b h j P),
      deltaStar n b h ≤ delta b h j P) =
    type_of% @R56Audit.lemma_2_5_i := rfl

-- **Lemma 2.5 (ii).**
-- `lemma_2_5_ii` (Crowding)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n) (hj : j < h),
      (unifPts n).real {P | ¬ GoodTransition b h j P} ≤ (48 / (b : ℝ)) ^ ((n : ℝ) / 2)) =
    type_of% @R56Audit.lemma_2_5_ii := rfl

-- `lemma_2_5_ii_all` (Crowding)
example : (∀ {n : ℕ} {b h : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n),
      (unifPts n).real {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} ≤
        h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2)) =
    type_of% @R56Audit.lemma_2_5_ii_all := rfl

-- Its proof: boundary strips, `W_𝒮`, `E_𝒮`.
example (b h j c v : ℕ) :
    bottomStrip b h j c v =
      Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
        Set.Ico ((v : ℝ) * (b : ℝ) ^ (j + 1) / (b : ℝ) ^ h)
          (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h) := rfl

example (b h j c v : ℕ) :
    topStrip b h j c v =
      Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
        Set.Ico ((((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h)
          (((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) / (b : ℝ) ^ h) := rfl

-- `bottomStrip_eq_cell` (StageGeometry)
example : (∀ (b h j c v : ℕ),
      bottomStrip b h j c v = cell b h j c (b * v)) =
    type_of% @R56Audit.bottomStrip_eq_cell := rfl

-- `topStrip_eq_cell` (StageGeometry)
example : (∀ {b : ℕ} (hb : 0 < b) (h j c v : ℕ),
      topStrip b h j c v = cell b h j c (b * v + (b - 1))) =
    type_of% @R56Audit.topStrip_eq_cell := rfl

example (b h j : ℕ) :
    boundaryStrips b h j = ⋃ p : Fin (b ^ j) × Fin (b ^ (h - j - 1)),
      bottomStrip b h j p.1 p.2 ∪ topStrip b h j p.1 p.2 := rfl

example (b h j : ℕ) (𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) :
    Wset b h j 𝒮 = boundaryStrips b h j ∪ ⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2 := rfl

example {n : ℕ} (b h j : ℕ) (P : Fin n → ℝ × ℝ) :
    heavySet b h j P = Finset.univ.filter (fun p => Heavy b h j P p.1 p.2) := rfl

example {n : ℕ} (b h j : ℕ) (𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) :
    (crowdEvent b h j 𝒮 : Set (Fin n → ℝ × ℝ)) =
      {P | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ Wset b h j 𝒮)).card} := rfl

example (b h j : ℕ) :
    smallCollections b h j =
      Finset.univ.filter (fun 𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1))) =>
        (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) := rfl

-- `mem_boundaryStrips_or_innerRegion` (Crowding)
example : (∀ {b h j : ℕ} (hb : 0 < b) (hj : j < h) {z : ℝ × ℝ} (hz1 : z.1 ∈ Set.Icc (0 : ℝ) 1)
    (hz2 : z.2 ∈ Set.Ico (0 : ℝ) 1),
      z ∈ boundaryStrips b h j ∨
        ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)), z ∈ innerRegion b h j c v) =
    type_of% @R56Audit.mem_boundaryStrips_or_innerRegion := rfl

-- `half_lt_card_Wset` (Crowding)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Fin n → ℝ × ℝ} (hP : ∀ i, (P
    i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ico (0 : ℝ) 1) (hbad : ¬ GoodTransition b h j P),
      (n : ℝ) / 2 <
        (Finset.univ.filter (fun i => P i ∈ Wset b h j (heavySet b h j P))).card) =
    type_of% @R56Audit.half_lt_card_Wset := rfl

-- `innerRegion_inj` (Crowding)
example : (∀ {b h j : ℕ} (hb : 0 < b) {z : ℝ × ℝ} (hz : ∀ k : ℕ, z.1 ≠ (k : ℝ) / (b : ℝ) ^ j) {c
    c' v v' : ℕ} (h1 : z ∈ innerRegion b h j c v) (h2 : z ∈ innerRegion b h j c' v'),
      c = c' ∧ v = v') =
    type_of% @R56Audit.innerRegion_inj := rfl

-- `card_heavySet_lt` (Crowding)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) {P : Fin n → ℝ × ℝ} (hgrid : NoGrid b P),
      ((heavySet b h j P).card : ℝ) < (b : ℝ) ^ (h - 1) / b) =
    type_of% @R56Audit.card_heavySet_lt := rfl

-- `mem_crowdEvent_heavySet` (Crowding)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Fin n → ℝ × ℝ} (hP : ∀ i, (P
    i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ico (0 : ℝ) 1) (hbad : ¬ GoodTransition b h j P),
      P ∈ crowdEvent b h j (heavySet b h j P)) =
    type_of% @R56Audit.mem_crowdEvent_heavySet := rfl

-- `bad_ae_le_iUnion_crowdEvent` (Crowding)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j < h),
      {P : Fin n → ℝ × ℝ | ¬ GoodTransition b h j P} ≤ᵐ[unifPts n]
        ⋃ 𝒮 ∈ smallCollections b h j, crowdEvent b h j 𝒮) =
    type_of% @R56Audit.bad_ae_le_iUnion_crowdEvent := rfl

-- "so they cover an area of `2/b`"; "area less than `1/M` each, so they cover an area of less
-- than `1/b`"; "Hence `W_𝒮` is a fixed set of area at most `3/b`".
-- `volume_boundaryStrips` (Crowding)
example : (∀ {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h),
      volume (boundaryStrips b h j) = ENNReal.ofReal (2 / (b : ℝ))) =
    type_of% @R56Audit.volume_boundaryStrips := rfl

-- `volume_boundaryStrips_le` (Crowding)
example : (∀ {b h j : ℕ} (hb : 0 < b) (hj : j < h),
      volume (boundaryStrips b h j) ≤ ENNReal.ofReal (2 / (b : ℝ))) =
    type_of% @R56Audit.volume_boundaryStrips_le := rfl

-- `volume_innerRegion_lt` (Crowding)
example : (∀ {b h : ℕ} (hb : 0 < b) (hh : 0 < h) (j c v : ℕ),
      volume (innerRegion b h j c v) < ENNReal.ofReal (1 / (b : ℝ) ^ (h - 1))) =
    type_of% @R56Audit.volume_innerRegion_lt := rfl

-- `volume_innerRegions_lt` (Crowding)
example : (∀ {b h j : ℕ} (hb : 0 < b) (hj : j < h) {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j -
    1)))} (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b),
      volume (⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2) < ENNReal.ofReal (1 / (b : ℝ))) =
    type_of% @R56Audit.volume_innerRegions_lt := rfl

-- `volume_innerRegions_le` (Crowding)
example : (∀ {b h j : ℕ} (hb : 0 < b) (hj : j < h) {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j -
    1)))} (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b),
      volume (⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2) ≤ ENNReal.ofReal (1 / (b : ℝ))) =
    type_of% @R56Audit.volume_innerRegions_le := rfl

-- `volume_Wset_le` (Crowding)
example : (∀ {b h j : ℕ} (hb : 0 < b) (hj : j < h) {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j -
    1)))} (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b),
      volume (Wset b h j 𝒮) ≤ ENNReal.ofReal (3 / (b : ℝ))) =
    type_of% @R56Audit.volume_Wset_le := rfl

-- `exists_card_eq_ceil_half` (Crowding)
example : (∀ {n : ℕ} {W : Set (ℝ × ℝ)} {P : Fin n → ℝ × ℝ} (hE : (n : ℝ) / 2 ≤
    (Finset.univ.filter (fun i => P i ∈ W)).card),
      ∃ T : Finset (Fin n), T.card = ⌈(n : ℝ) / 2⌉₊ ∧ ∀ i ∈ T, P i ∈ W) =
    type_of% @R56Audit.exists_card_eq_ceil_half := rfl

-- `unifPts_forall_mem` (Crowding)
example : (∀ {n : ℕ} (T : Finset (Fin n)) (W : Set (ℝ × ℝ)),
      unifPts n {P | ∀ i ∈ T, P i ∈ W} =
        (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ^ T.card) =
    type_of% @R56Audit.unifPts_forall_mem := rfl

-- `unifPts_forall_mem_le` (Crowding)
example : (∀ {n : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {W : Set (ℝ × ℝ)} (hW :
    (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ≤ ENNReal.ofReal q) {T : Finset (Fin n)} (hT :
    (n : ℝ) / 2 ≤ T.card),
      unifPts n {P | ∀ i ∈ T, P i ∈ W} ≤ ENNReal.ofReal (q ^ ((n : ℝ) / 2))) =
    type_of% @R56Audit.unifPts_forall_mem_le := rfl

-- `unifPts_half_mem_le` (Crowding)
example : (∀ {n : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {W : Set (ℝ × ℝ)} (hW :
    (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ≤ ENNReal.ofReal q),
      unifPts n {P | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ W)).card} ≤
        ENNReal.ofReal (2 ^ n * q ^ ((n : ℝ) / 2))) =
    type_of% @R56Audit.unifPts_half_mem_le := rfl

-- `unifPts_crowdEvent_le` (Crowding)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 3 ≤ b) (hj : j < h) {𝒮 : Finset (Fin (b ^ j) × Fin (b ^
    (h - j - 1)))} (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b),
      unifPts n (crowdEvent b h j 𝒮) ≤
        ENNReal.ofReal (2 ^ n * (3 / (b : ℝ)) ^ ((n : ℝ) / 2))) =
    type_of% @R56Audit.unifPts_crowdEvent_le := rfl

-- `card_smallCollections_le` (Crowding)
example : (∀ {b h j : ℕ} (hj : j < h),
      (smallCollections b h j).card ≤ 2 ^ b ^ (h - 1)) =
    type_of% @R56Audit.card_smallCollections_le := rfl

-- `unifPts_bad_le` (Crowding)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 3 ≤ b) (hj : j < h),
      unifPts n {P | ¬ GoodTransition b h j P} ≤
        ENNReal.ofReal (2 ^ (b ^ (h - 1) + n) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2))) =
    type_of% @R56Audit.unifPts_bad_le := rfl

-- `two_pow_mul_rpow_le` (Crowding)
example : (∀ {n : ℕ} {b M : ℕ} (hb : 0 < b) (hMn : M ≤ n),
      (2 : ℝ) ^ (M + n) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2) ≤ (48 / (b : ℝ)) ^ ((n : ℝ) / 2)) =
    type_of% @R56Audit.two_pow_mul_rpow_le := rfl

/-! ### Fluctuations, Lemma 2.6 -/

-- **Lemma 2.6**, display (13).
-- `lemma_2_6_digits` (Digits)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) {lam : ℝ} (hlam : 0 < lam),
      (unifPts n).real {P | fluctDigits χ b h P ≤ -lam} ≤
        Real.exp (-(lam ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (2 * h * n)))) =
    type_of% @R56Audit.lemma_2_6_digits := rfl

-- `lemma_2_6` (Fluctuations)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) {lam : ℝ} (hlam : 0 < lam),
      (unifPts n).real {P | fluct χ b h P ≤ -lam} ≤
        Real.exp (-(lam ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (2 * h * n)))) =
    type_of% @R56Audit.lemma_2_6 := rfl

-- Its proof. Step 1: one digit. "If `V_i ∉ B`, the added function is constant on `B` \[…\]
-- If `V_i ∈ B`, the added function has oscillation at most `1` on `B`"; one cell; all cells.
-- `stepFn_single_eq_of_notMem` (StepOsc)
example : (∀ {n : ℕ} (V d : Fin n → ℝ) (i : Fin n) (hd : ∀ k, k ≠ i → d k = 0) {s t : ℝ} (hi : V
    i ∉ Set.Ico s t) {y : ℝ} (hy : y ∈ Set.Ico s t),
      stepFn V d y = if V i < s then d i else 0) =
    type_of% @R56Audit.stepFn_single_eq_of_notMem := rfl

-- `osc_stepFn_single_le` (StepOsc)
example : (∀ {n : ℕ} (V d : Fin n → ℝ) (i : Fin n) (hd : ∀ k, k ≠ i → d k = 0) {s t : ℝ} (hst :
    s < t),
      osc (Set.Ico s t) (stepFn V d) ≤ if V i ∈ Set.Ico s t then |d i| else 0) =
    type_of% @R56Audit.osc_stepFn_single_le := rfl

-- `abs_osc_endpointAvg_sub_le` (Influence)
example : (∀ {n : ℕ} (ε V : Fin n → ℝ) {side side' : Fin n → Side} (i : Fin n) (hside : ∀ k, k ≠
    i → side' k = side k) {s t : ℝ} (hst : s < t),
      |osc (Set.Ico s t) (endpointAvg ε V side') - osc (Set.Ico s t) (endpointAvg ε V side)| ≤
        if V i ∈ Set.Ico s t then |ε i * (oldWeight (side' i) - oldWeight (side i))| else 0) =
    type_of% @R56Audit.abs_osc_endpointAvg_sub_le := rfl

-- `Zstep_update_le` (Influence)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (V : Fin n → ℝ) (g : Fin n → ℤ) (r : Fin n → Fin b) (i : Fin n) (a : Fin b),
      |Zstep ε b h (j + 1) V (refineIdx g (Function.update r i a)) -
          Zstep ε b h (j + 1) V (refineIdx g r)| ≤ 1 / (b : ℝ) ^ (h - 1)) =
    type_of% @R56Audit.Zstep_update_le := rfl

-- Step 2: one transition, by Fact A.1. In the proof `Z_{j+1}` is read from the heights and
-- the indices (`Zproc`) and `E[Z_{j+1} | 𝓕_j]` is the average over the next digits (`Zmean`).
example {n : ℕ} (ε : Fin n → ℝ) (b h : ℕ) (P : Fin n → ℝ × ℝ) :
    fluctStep ε b h P = ∑ j ∈ Finset.range h, (Zproc ε b h (j + 1) P - Zmean ε b h j P) := rfl

-- `condExp_exp_step` (Fluctuations)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (t : ℝ),
      ∀ᵐ P ∂pointSampleLaw n,
        ((pointSampleLaw n)[fun P => Real.exp (t * (Zproc ε b h (j + 1) P - Zmean ε b h j P)) |
            stageSigma n b j]) P ≤
          Real.exp (n * t ^ 2 * (1 / (b : ℝ) ^ (h - 1)) ^ 2 / 2)) =
    type_of% @R56Audit.condExp_exp_step := rfl

-- `fluctTerm_ae_eq` (Fluctuations)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j < h) (χ : Fin n → ℤˣ),
      (fun P => Zpot χ b h (j + 1) P - ((unifPts n)[Zpot χ b h (j + 1) | stageSigma n b j]) P)
        =ᵐ[unifPts n] fun P => Zproc (sgn χ) b h (j + 1) P - Zmean (sgn χ) b h j P) =
    type_of% @R56Audit.fluctTerm_ae_eq := rfl

-- `lemma_2_6_step2` (Fluctuations)
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 0 < b) (hj : j < h) (χ : Fin n → ℤˣ) (t : ℝ),
      ∀ᵐ P ∂unifPts n,
        ((unifPts n)[fun P => Real.exp (-t * (Zpot χ b h (j + 1) P -
            ((unifPts n)[Zpot χ b h (j + 1) | stageSigma n b j]) P)) | stageSigma n b j]) P ≤
          Real.exp (n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2))) =
    type_of% @R56Audit.lemma_2_6_step2 := rfl

-- Step 3: all transitions. "the earlier terms `T_0, …, T_{j-1}` are `𝓕_j`-measurable. So we
-- can condition successively \[…\] Multiplying the `h` bounds gives \[…\] By Markov's
-- inequality".
-- `fluctTerm_measurable_of_lt` (Fluctuations)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h : ℕ) {k j : ℕ} (hkj : k < j),
      Measurable[stageSigma n b j] (fun P => Zproc ε b h (k + 1) P - Zmean ε b h k P)) =
    type_of% @R56Audit.fluctTerm_measurable_of_lt := rfl

-- `integral_prod_le_of_condExp_le` (SuccessiveConditioning)
example {Ω : Type*} : (∀ {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (ℱ :
    Filtration ℕ mΩ) (W : ℕ → Ω → ℝ) (c : ℕ → ℝ) (B : ℝ) (h : ℕ) (hW : ∀ j < h,
    StronglyMeasurable[ℱ (j + 1)] (W j)) (hbound : ∀ j < h, ∀ ω, 0 ≤ W j ω ∧ W j ω ≤ B) (hc : ∀
    j < h, 0 ≤ c j) (hcond : ∀ j < h, ∀ᵐ ω ∂μ, (μ[W j | ℱ j]) ω ≤ c j),
      ∫ ω, ∏ j ∈ Finset.range h, W j ω ∂μ ≤ ∏ j ∈ Finset.range h, c j) =
    type_of% (@R56Audit.integral_prod_le_of_condExp_le Ω) := rfl

-- `integral_exp_neg_sum_le` (Fluctuations)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1) (h : ℕ) (t : ℝ),
      ∫ P, Real.exp (-t * fluctStep ε b h P) ∂pointSampleLaw n ≤
        Real.exp (h * (n * t ^ 2 * (1 / (b : ℝ) ^ (h - 1)) ^ 2 / 2))) =
    type_of% @R56Audit.integral_exp_neg_sum_le := rfl

-- `fluct_ae_eq` (Fluctuations)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ),
      fluct χ b h =ᵐ[pointSampleLaw n] fluctStep (sgn χ) b h) =
    type_of% @R56Audit.fluct_ae_eq := rfl

-- `lemma_2_6_step3` (Fluctuations)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (t : ℝ),
      ∫ P, Real.exp (-t * fluct χ b h P) ∂unifPts n ≤
        Real.exp (h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2))) =
    type_of% @R56Audit.lemma_2_6_step3 := rfl

-- `measureReal_le_exp_mul_integral_exp_neg` (SuccessiveConditioning)
example {Ω : Type*} : (∀ {mΩ : MeasurableSpace Ω} {μ : Measure Ω} (Z : Ω → ℝ) {t : ℝ} (ht : 0 <
    t) (hint : Integrable (fun ω => Real.exp (-t * Z ω)) μ) (a : ℝ),
      μ.real {ω | Z ω ≤ a} ≤ Real.exp (t * a) * ∫ ω, Real.exp (-t * Z ω) ∂μ) =
    type_of% (@R56Audit.measureReal_le_exp_mul_integral_exp_neg Ω) := rfl

-- `lemma_2_6_markov` (Fluctuations)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (lam : ℝ) {t : ℝ} (ht : 0 <
    t),
      (unifPts n).real {P | fluct χ b h P ≤ -lam} ≤
        Real.exp (-t * lam + h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2))) =
    type_of% @R56Audit.lemma_2_6_markov := rfl

/-! ### Proposition 2.7 -/

-- Its proof, sentence by sentence, with `𝓕_j = digitSigma` and `T = fluctDigits`.
-- `condGain_ge_deltaStar` (Simultaneous)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (h : ℕ) (hn : 0 < n) (χ : Fin n → ℤˣ),
      ∀ᵐ P ∂unifPts n, ∀ j < h, GoodTransition b h j P → deltaStar n b h ≤
        ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | digitSigma n b j]) P) =
    type_of% @R56Audit.condGain_ge_deltaStar := rfl

-- `Zpot_ge_of_good` (Simultaneous)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (h : ℕ) (hn : 0 < n) (χ : Fin n → ℤˣ),
      ∀ᵐ P ∂unifPts n, (∀ j < h, GoodTransition b h j P) →
        h * deltaStar n b h + fluctDigits χ b h P ≤ Zpot χ b h h P) =
    type_of% @R56Audit.Zpot_ge_of_good := rfl

-- `Zpot_le_of_small` (Simultaneous)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (hsmall :
    supNorm χ P ≤ h * deltaStar n b h / 8),
      Zpot χ b h h P ≤ h * deltaStar n b h / 4) =
    type_of% @R56Audit.Zpot_le_of_small := rfl

-- `fluct_le_of_good` (Simultaneous)
example : (∀ {n : ℕ} {b : ℕ} (hb : 2 ≤ b) (h : ℕ) (hn : 0 < n) (χ : Fin n → ℤˣ),
      ∀ᵐ P ∂unifPts n, (∀ j < h, GoodTransition b h j P) →
        supNorm χ P ≤ h * deltaStar n b h / 8 →
        fluctDigits χ b h P ≤ -(3 * h * deltaStar n b h / 4)) =
    type_of% @R56Audit.fluct_le_of_good := rfl

-- `deltaStar_sq` (Simultaneous)
example : (∀ {b : ℕ} (hb : 0 < b) (n h : ℕ),
      deltaStar n b h ^ 2 = n / (64 * (b : ℝ) ^ 3 * (b : ℝ) ^ (h - 1))) =
    type_of% @R56Audit.deltaStar_sq := rfl

-- `exponent_eq` (Simultaneous)
example : (∀ {n : ℕ} {b : ℕ} (hb : 0 < b) {h : ℕ} (hh : 0 < h) (hn : 0 < n),
      (h * deltaStar n b h / 4) ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (2 * h * n) =
          h * deltaStar n b h ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (32 * n) ∧
        h * deltaStar n b h ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (32 * n) =
          h * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3)) =
    type_of% @R56Audit.exponent_eq := rfl

-- `good_inter_small_le` (Simultaneous)
example : (∀ {n : ℕ} {b h : ℕ} (hb : 2 ≤ b) (hh : 1 ≤ h) (hn : 0 < n) (χ : Fin n → ℤˣ),
      (unifPts n).real ({P | ∀ j < h, GoodTransition b h j P} ∩
          {P | supNorm χ P ≤ h * deltaStar n b h / 8}) ≤
        Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3)))) =
    type_of% @R56Audit.good_inter_small_le := rfl

-- `prob_exists_small_le` (Simultaneous)
example : (∀ {n : ℕ} {b h : ℕ},
      (unifPts n).real {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ h * deltaStar n b h / 8} ≤
        (unifPts n).real {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} +
          ∑ χ : Fin n → ℤˣ, (unifPts n).real ({P | ∀ j < h, GoodTransition b h j P} ∩
            {P | supNorm χ P ≤ h * deltaStar n b h / 8})) =
    type_of% @R56Audit.prob_exists_small_le := rfl

-- `threshold_eq` (Simultaneous)
example : (∀ (n b h : ℕ),
      h * deltaStar n b h / 8 =
        (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))) =
    type_of% @R56Audit.threshold_eq := rfl

-- `card_colorings` (Simultaneous)
example : (∀ (n : ℕ),
      Fintype.card (Fin n → ℤˣ) = 2 ^ n) =
    type_of% @R56Audit.card_colorings := rfl

-- **Proposition 2.7**, display (14).
-- `proposition_2_7` (Simultaneous)
example : (∀ {n b h : ℕ} (hb : 3 ≤ b) (hh : 1 ≤ h) (hMn : b ^ (h - 1) ≤ n),
      (unifPts n).real {P | ∃ χ : Fin n → ℤˣ,
          supNorm χ P ≤ (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))} ≤
        h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
          2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3)))) =
    type_of% @R56Audit.proposition_2_7 := rfl

/-! ## Section 2.5. Parameters -/

-- Display (15) can be satisfied; "it forces `b > 48`, so that `64 ≤ b⁴`".
-- `exists_base_of_15` (Parameters)
example : (∀ (A : ℝ),
      ∃ b : ℕ, A + 2 ≤ Real.log ((b : ℝ) / 48) / 2 ∧ A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) =
    type_of% @R56Audit.exists_base_of_15 := rfl

-- `base_ge_49` (Parameters)
example : (∀ {A : ℝ} (hA : 0 < A) {b : ℕ} (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2),
      49 ≤ b) =
    type_of% @R56Audit.base_ge_49 := rfl

-- `sixty_four_le_pow_four` (Parameters)
example : (∀ {b : ℕ} (hb : 3 ≤ b),
      (64 : ℝ) ≤ (b : ℝ) ^ 4) =
    type_of% @R56Audit.sixty_four_le_pow_four := rfl

-- `cA_pos` (Parameters)
example : (∀ {b : ℕ} (hb : 2 ≤ b),
      0 < cA b) =
    type_of% @R56Audit.cA_pos := rfl

-- "Let `h ≥ 1` be the largest integer with `b⁻⁵ h b^{h-1} ≤ n`"
example (b n h : ℕ) : ScaleOK b n h ↔ (h : ℝ) * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 5 ≤ n := Iff.rfl

example (b n h : ℕ) :
    IsScale b n h ↔ 1 ≤ h ∧ (h : ℝ) * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 5 ≤ n ∧
      ∀ h' : ℕ, (h' : ℝ) * (b : ℝ) ^ (h' - 1) / (b : ℝ) ^ 5 ≤ n → h' ≤ h := Iff.rfl

-- `scaleOK_one` (Parameters)
example : (∀ {b n : ℕ} (hb : 1 ≤ b) (hn : 1 ≤ n),
      ScaleOK b n 1) =
    type_of% @R56Audit.scaleOK_one := rfl

-- `le_of_scaleOK` (Parameters)
example : (∀ {b n h : ℕ} (hb : 1 ≤ b) (hs : ScaleOK b n h),
      h ≤ b ^ 5 * n) =
    type_of% @R56Audit.le_of_scaleOK := rfl

-- `exists_isScale` (Parameters)
example : (∀ {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n),
      ∃ h, IsScale b n h) =
    type_of% @R56Audit.exists_isScale := rfl

-- "By maximality, `n < b⁻⁵ (h+1) b^h`. With `h+1 ≤ 2h` and `b^h = bM` this gives" (16), "and
-- with `h+1 ≤ 2^h` and `b⁻⁵ ≤ 1` it gives `n < (2b)^h`, that is," (17); then (18).
-- `lt_of_isScale` (Parameters)
example : (∀ {b n h : ℕ} (hs : IsScale b n h),
      (n : ℝ) < ((h : ℝ) + 1) * (b : ℝ) ^ h / (b : ℝ) ^ 5) =
    type_of% @R56Audit.lt_of_isScale := rfl

-- `scale_succ_le_two_mul` (Parameters)
example : (∀ {h : ℕ} (hh : 1 ≤ h),
      (h : ℝ) + 1 ≤ 2 * h) =
    type_of% @R56Audit.scale_succ_le_two_mul := rfl

-- `base_pow_eq_mul_pow` (Parameters)
example : (∀ (b : ℕ) {h : ℕ} (hh : 1 ≤ h),
      (b : ℝ) ^ h = b * (b : ℝ) ^ (h - 1)) =
    type_of% @R56Audit.base_pow_eq_mul_pow := rfl

-- `display_16` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h),
      (h : ℝ) * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 5 ≤ n ∧
        (n : ℝ) < 2 * h * (b : ℝ) ^ (h - 1) / (b : ℝ) ^ 4) =
    type_of% @R56Audit.display_16 := rfl

-- `scale_succ_le_two_pow` (Parameters)
example : (∀ (h : ℕ),
      (h : ℝ) + 1 ≤ 2 ^ h) =
    type_of% @R56Audit.scale_succ_le_two_pow := rfl

-- `inv_pow_five_le_one` (Parameters)
example : (∀ {b : ℕ} (hb : 1 ≤ b),
      ((b : ℝ) ^ 5)⁻¹ ≤ 1) =
    type_of% @R56Audit.inv_pow_five_le_one := rfl

-- `lt_two_mul_pow_of_isScale` (Parameters)
example : (∀ {b n h : ℕ} (hb : 1 ≤ b) (hs : IsScale b n h),
      (n : ℝ) < (2 * (b : ℝ)) ^ h) =
    type_of% @R56Audit.lt_two_mul_pow_of_isScale := rfl

-- `display_17` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h),
      Real.logb 2 n < (1 + Real.logb 2 b) * h) =
    type_of% @R56Audit.display_17 := rfl

-- `display_18` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h),
      cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < ((b : ℝ) ^ 8)⁻¹ * (h : ℝ) ^ (3 / 2 : ℝ)) =
    type_of% @R56Audit.display_18 := rfl

-- The case `M > n`: "(16) gives `b⁻⁵ h < 1`, that is, `h < b⁵`, and (18) gives
-- `c_A (log₂ n)^{3/2} < b⁻⁸ b^{15/2} < 1`"; the rectangle `[0,1] × [0, min_i V_i]`; "So in this
-- case the claim of the theorem holds with probability one."
-- `scale_div_pow_five_lt_one` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h) (hMn : n < b ^ (h - 1)),
      (h : ℝ) / (b : ℝ) ^ 5 < 1) =
    type_of% @R56Audit.scale_div_pow_five_lt_one := rfl

-- `scale_lt_pow_five` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h) (hMn : n < b ^ (h - 1)),
      (h : ℝ) < (b : ℝ) ^ 5) =
    type_of% @R56Audit.scale_lt_pow_five := rfl

-- `cA_mul_lt_of_lt` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h) (hMn : n < b ^ (h - 1)),
      cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < ((b : ℝ) ^ 8)⁻¹ * (b : ℝ) ^ (15 / 2 : ℝ)) =
    type_of% @R56Audit.cA_mul_lt_of_lt := rfl

-- `inv_pow_eight_mul_rpow_lt_one` (Parameters)
example : (∀ {b : ℕ} (hb : 2 ≤ b),
      ((b : ℝ) ^ 8)⁻¹ * (b : ℝ) ^ (15 / 2 : ℝ) < 1) =
    type_of% @R56Audit.inv_pow_eight_mul_rpow_lt_one := rfl

-- `cA_mul_lt_one` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h) (hMn : n < b ^ (h - 1)),
      cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < 1) =
    type_of% @R56Audit.cA_mul_lt_one := rfl

-- `one_le_supNorm` (SupNorm)
example : (∀ {n : ℕ} (hn : 1 ≤ n) (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (hP : ∀ i, (P i).1 ∈
    Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Icc (0 : ℝ) 1) (hinj : Function.Injective fun i => (P
    i).2),
      1 ≤ supNorm χ P) =
    type_of% @R56Audit.one_le_supNorm := rfl

-- `ae_one_le_supNorm` (Parameters)
example : (∀ {n : ℕ} (hn : 1 ≤ n),
      ∀ᵐ P ∂unifPts n, ∀ χ : Fin n → ℤˣ, 1 ≤ supNorm χ P) =
    type_of% @R56Audit.ae_one_le_supNorm := rfl

-- `ae_cA_mul_lt_supNorm` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h) (hMn : n < b ^ (h - 1)),
      ∀ᵐ P ∂unifPts n, ∀ χ : Fin n → ℤˣ, cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P) =
    type_of% @R56Audit.ae_cA_mul_lt_supNorm := rfl

-- The case `M ≤ n`: "Also `h ≤ 2^{h-1} ≤ M ≤ n`"; the first term; the second term; their sum;
-- the threshold chain.
-- `scale_le_two_pow` (Parameters)
example : (∀ (h : ℕ),
      h ≤ 2 ^ (h - 1)) =
    type_of% @R56Audit.scale_le_two_pow := rfl

-- `two_pow_le_base_pow` (Parameters)
example : (∀ {b : ℕ} (hb : 2 ≤ b) (h : ℕ),
      2 ^ (h - 1) ≤ b ^ (h - 1)) =
    type_of% @R56Audit.two_pow_le_base_pow := rfl

-- `scale_le_of_pow_le` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hMn : b ^ (h - 1) ≤ n),
      h ≤ n) =
    type_of% @R56Audit.scale_le_of_pow_le := rfl

-- `first_term_le` (Parameters)
example : (∀ {A : ℝ} {b : ℕ} (hb : 0 < b) (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (n : ℕ),
      (48 / (b : ℝ)) ^ ((n : ℝ) / 2) ≤ Real.exp (-(A + 2) * n)) =
    type_of% @R56Audit.first_term_le := rfl

-- `first_term_le_mul` (Parameters)
example : (∀ {A : ℝ} {b n h : ℕ} (hb : 2 ≤ b) (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hMn :
    b ^ (h - 1) ≤ n),
      (h : ℝ) * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) ≤ h * Real.exp (-(A + 2) * n) ∧
        (h : ℝ) * Real.exp (-(A + 2) * n) ≤ n * Real.exp (-(A + 2) * n)) =
    type_of% @R56Audit.first_term_le_mul := rfl

-- `exponent_gt` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h),
      (b : ℝ) * n / 4096 < (h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3)) =
    type_of% @R56Audit.exponent_gt := rfl

-- `exponent_ge` (Parameters)
example : (∀ {A : ℝ} {b : ℕ} (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) (n : ℕ),
      (A + 2 + Real.log 2) * n ≤ (b : ℝ) * n / 4096) =
    type_of% @R56Audit.exponent_ge := rfl

-- `second_term_le_two_pow_mul` (Parameters)
example : (∀ {A : ℝ} {b n h : ℕ} (hb : 2 ≤ b) (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) (hs :
    IsScale b n h),
      2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) ≤
        2 ^ n * Real.exp (-(A + 2 + Real.log 2) * n)) =
    type_of% @R56Audit.second_term_le_two_pow_mul := rfl

-- `two_pow_mul_exp_eq` (Parameters)
example : (∀ (A : ℝ) (n : ℕ),
      2 ^ n * Real.exp (-(A + 2 + Real.log 2) * n) = Real.exp (-(A + 2) * n)) =
    type_of% @R56Audit.two_pow_mul_exp_eq := rfl

-- `second_term_le` (Parameters)
example : (∀ {A : ℝ} {b n h : ℕ} (hb : 2 ≤ b) (hb2 : A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) (hs :
    IsScale b n h),
      2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) ≤
        Real.exp (-(A + 2) * n)) =
    type_of% @R56Audit.second_term_le := rfl

-- `sum_terms_le` (Parameters)
example : (∀ {A : ℝ} {b n h : ℕ} (hb : 2 ≤ b) (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 :
    A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) (hs : IsScale b n h) (hMn : b ^ (h - 1) ≤ n),
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
          2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) ≤
        ((n : ℝ) + 1) * Real.exp (-(A + 2) * n)) =
    type_of% @R56Audit.sum_terms_le := rfl

-- `add_one_le_exp_two_mul` (Parameters)
example : (∀ {x : ℝ} (hx : 0 ≤ x),
      x + 1 ≤ Real.exp (2 * x)) =
    type_of% @R56Audit.add_one_le_exp_two_mul := rfl

-- `add_one_mul_exp_le` (Parameters)
example : (∀ (A : ℝ) {x : ℝ} (hx : 0 ≤ x),
      (x + 1) * Real.exp (-(A + 2) * x) ≤ Real.exp (-A * x)) =
    type_of% @R56Audit.add_one_mul_exp_le := rfl

-- `failure_le` (Parameters)
example : (∀ {A : ℝ} (hA : 0 < A) {b n h : ℕ} (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 :
    A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) (hn : 1 ≤ n) (hs : IsScale b n h) (hMn : b ^ (h - 1) ≤
    n),
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
          2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) ≤
        Real.exp (-A * n)) =
    type_of% @R56Audit.failure_le := rfl

-- `threshold_ge_sqrt` (Parameters)
example : (∀ {b n h : ℕ} (hb : 2 ≤ b) (hs : IsScale b n h),
      (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (h / (b : ℝ) ^ 5) ≤
        (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))) =
    type_of% @R56Audit.threshold_ge_sqrt := rfl

-- `threshold_sqrt_eq` (Parameters)
example : (∀ (b h : ℕ),
      (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (h / (b : ℝ) ^ 5) =
        (h : ℝ) ^ (3 / 2 : ℝ) / (64 * (b : ℝ) ^ 4)) =
    type_of% @R56Audit.threshold_sqrt_eq := rfl

-- `rpow_div_ge` (Parameters)
example : (∀ {b : ℕ} (hb : 3 ≤ b) (h : ℕ),
      ((b : ℝ) ^ 8)⁻¹ * (h : ℝ) ^ (3 / 2 : ℝ) ≤ (h : ℝ) ^ (3 / 2 : ℝ) / (64 * (b : ℝ) ^ 4)) =
    type_of% @R56Audit.rpow_div_ge := rfl

-- `threshold_gt` (Parameters)
example : (∀ {b n h : ℕ} (hb : 3 ≤ b) (hn : 1 ≤ n) (hs : IsScale b n h),
      cA b * Real.logb 2 n ^ (3 / 2 : ℝ) <
        (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))) =
    type_of% @R56Audit.threshold_gt := rfl

-- `prob_exists_supNorm_le_of_pow_le` (Parameters)
example : (∀ {A : ℝ} (hA : 0 < A) {b n h : ℕ} (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 :
    A + 2 + Real.log 2 ≤ (b : ℝ) / 4096) (hn : 1 ≤ n) (hs : IsScale b n h) (hMn : b ^ (h - 1) ≤
    n),
      (unifPts n).real {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ cA b * Real.logb 2 n ^ (3 / 2 : ℝ)} ≤
        Real.exp (-A * n)) =
    type_of% @R56Audit.prob_exists_supNorm_le_of_pow_le := rfl

-- Both cases.
-- `prob_exists_supNorm_le` (Parameters)
example : (∀ {A : ℝ} (hA : 0 < A) {b : ℕ} (hb1 : A + 2 ≤ Real.log ((b : ℝ) / 48) / 2) (hb2 : A +
    2 + Real.log 2 ≤ (b : ℝ) / 4096) {n : ℕ} (hn : 1 ≤ n),
      (unifPts n).real {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ cA b * Real.logb 2 n ^ (3 / 2 : ℝ)} ≤
        Real.exp (-A * n)) =
    type_of% @R56Audit.prob_exists_supNorm_le := rfl

/-! ## Appendix A -/

-- The proof of Fact 2.2. "The shift does not hurt."
-- `identDistrib_sum_neg` (SymmetricSumsGeneral)
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ι : Type*} : (∀ [Fintype ι] (X : ι → Ω
    → ℝ) (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ),
      IdentDistrib (fun ω => ∑ i, X i ω) (fun ω => -∑ i, X i ω) μ μ) =
    type_of% (@R56Audit.identDistrib_sum_neg Ω _ μ ι) := rfl

-- `integral_abs_add_eq_integral_abs_sub` (SymmetricSumsGeneral)
example {Ω : Type*} : (∀ [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} (hsymm : IdentDistrib X
    (fun ω => -X ω) μ μ) (θ : ℝ),
      ∫ ω, |θ + X ω| ∂μ = ∫ ω, |θ - X ω| ∂μ) =
    type_of% (@R56Audit.integral_abs_add_eq_integral_abs_sub Ω) := rfl

-- `integral_abs_le_integral_abs_add_of_symm` (SymmetricSumsGeneral)
example {Ω : Type*} : (∀ [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hsymm : IdentDistrib X (fun ω => -X ω) μ μ) (hX : Integrable X μ) (θ : ℝ),
      ∫ ω, |X ω| ∂μ ≤ ∫ ω, |θ + X ω| ∂μ) =
    type_of% (@R56Audit.integral_abs_le_integral_abs_add_of_symm Ω) := rfl

-- "Two moments." (The Lean proof adds one variable at a time; the manuscript expands `X⁴`
-- and counts the surviving terms. `6 Σ_{i<j} E X_i² E X_j²` appears as `3m(m-1)σ⁴`.)
-- `integral_pow_eq_zero_of_symm` (SymmetricSumsGeneral)
example {Ω : Type*} : (∀ [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ} (h : IdentDistrib Y
    (fun ω => -Y ω) μ μ) {k : ℕ} (hk : Odd k),
      ∫ ω, Y ω ^ k ∂μ = 0) =
    type_of% (@R56Audit.integral_pow_eq_zero_of_symm Ω) := rfl

-- `sum_moments` (SymmetricSumsGeneral)
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} :
    (∀ (X : ι → Ω → ℝ) (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i
    ω) μ μ) {σ : ℝ} (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2) (h4i : ∀ i, Integrable (fun ω => X i ω
    ^ 4) μ) (s : Finset ι),
      Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 4) μ ∧
        ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ = s.card * σ ^ 2 ∧
        ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ =
          ∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂μ + 3 * s.card * (s.card - 1) * σ ^ 4) =
    type_of% (@R56Audit.sum_moments Ω _ μ _ ι) := rfl

-- `sum_fourth_moment_le` (SymmetricSumsGeneral)
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} :
    (∀ (X : ι → Ω → ℝ) (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i
    ω) μ μ) {σ : ℝ} (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2) (h4i : ∀ i, Integrable (fun ω => X i ω
    ^ 4) μ) (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ 3 * σ ^ 4) (s : Finset ι),
      ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ ≤ 3 * (s.card * σ ^ 2) ^ 2) =
    type_of% (@R56Audit.sum_fourth_moment_le Ω _ μ _ ι) := rfl

-- "From moments to the absolute value."
-- `integral_sq_le_rpow_mul_rpow` (SymmetricSumsGeneral)
example {Ω : Type*} : (∀ [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY
    : AEMeasurable Y μ) (h4 : Integrable (fun ω => Y ω ^ 4) μ),
      ∫ ω, Y ω ^ 2 ∂μ ≤ (∫ ω, |Y ω| ∂μ) ^ (2 / 3 : ℝ) * (∫ ω, Y ω ^ 4 ∂μ) ^ (1 / 3 : ℝ)) =
    type_of% (@R56Audit.integral_sq_le_rpow_mul_rpow Ω) := rfl

-- `mul_sqrt_le_of_moments` (SymmetricSumsGeneral)
example : (∀ {m σ A Q : ℝ} (hm : 0 ≤ m) (hσ : 0 < σ) (hA : 0 ≤ A) (h2 : (m * σ ^ 2) ^ 3 ≤ A ^ 2
    * Q) (h4 : Q ≤ 3 * (m * σ ^ 2) ^ 2),
      σ * Real.sqrt (m / 3) ≤ A) =
    type_of% @R56Audit.mul_sqrt_le_of_moments := rfl

-- **Fact A.1.**
-- `fact_A_1` (BoundedDifferencesGeneral)
example {Ω G E : Type*} : (∀ [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace E] {μ :
    Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (Γ : Ω → G) (ξ : Fin n → Ω → E) (hΓ : Measurable
    Γ) (hξ : ∀ i, Measurable (ξ i)) (hξindep : iIndepFun ξ μ) (hΓindep : IndepFun Γ (fun ω i =>
    ξ i ω) μ) (φ : G × (Fin n → E) → ℝ) (hφ : Measurable φ) {c : ℝ} (hc : 0 < c) (hdiff : ∀ γ x
    i a, |φ (γ, Function.update x i a) - φ (γ, x)| ≤ c) (hint : Integrable (fun ω => φ (Γ ω, fun
    i => ξ i ω)) μ) (t : ℝ),
      ∀ᵐ ω ∂μ,
        (μ[fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
              (μ[fun ω => φ (Γ ω, fun i => ξ i ω) |
                MeasurableSpace.comap Γ inferInstance]) ω)) |
            MeasurableSpace.comap Γ inferInstance]) ω ≤
          Real.exp (n * t ^ 2 * c ^ 2 / 2)) =
    type_of% (@R56Audit.fact_A_1 Ω G E) := rfl

-- `fact_A_1_integrable` (BoundedDifferencesGeneral)
example {Ω G E : Type*} : (∀ [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace E] {μ :
    Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (Γ : Ω → G) (ξ : Fin n → Ω → E) (hΓ : Measurable
    Γ) (hξ : ∀ i, Measurable (ξ i)) (hξindep : iIndepFun ξ μ) (hΓindep : IndepFun Γ (fun ω i =>
    ξ i ω) μ) (φ : G × (Fin n → E) → ℝ) (hφ : Measurable φ) {c : ℝ} (hdiff : ∀ γ x i a, |φ (γ,
    Function.update x i a) - φ (γ, x)| ≤ c) (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i
    ω)) μ) (t : ℝ),
      Integrable (fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
          (μ[fun ω => φ (Γ ω, fun i => ξ i ω) | MeasurableSpace.comap Γ inferInstance]) ω))) μ) =
    type_of% (@R56Audit.fact_A_1_integrable Ω G E) := rfl

-- Its proof: "conditioning on `Γ = γ` amounts to fixing the first argument of `φ`"; the
-- unconditional bound; one difference; `cosh x ≤ exp(x²/2)`.
-- `condExp_comap_eq_integral_of_indepFun` (BoundedDifferencesGeneral)
example {Ω G H : Type*} : (∀ [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace H] {μ :
    Measure Ω} [IsProbabilityMeasure μ] {Γ : Ω → G} {X : Ω → H} (hΓ : Measurable Γ) (hX :
    Measurable X) (hindep : IndepFun Γ X μ) {F : G × H → ℝ} (hF : Measurable F) (hint :
    Integrable (fun ω => F (Γ ω, X ω)) μ),
      μ[fun ω => F (Γ ω, X ω) | MeasurableSpace.comap Γ inferInstance] =ᵐ[μ]
        fun ω => ∫ x, F (Γ ω, x) ∂μ.map X) =
    type_of% (@R56Audit.condExp_comap_eq_integral_of_indepFun Ω G H) := rfl

-- `fact_A_1_freeze` (BoundedDifferencesGeneral)
example {Ω G E : Type*} : (∀ [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace E] {μ :
    Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (Γ : Ω → G) (ξ : Fin n → Ω → E) (hΓ : Measurable
    Γ) (hξ : ∀ i, Measurable (ξ i)) (hξindep : iIndepFun ξ μ) (hΓindep : IndepFun Γ (fun ω i =>
    ξ i ω) μ) (φ : G × (Fin n → E) → ℝ) (hφ : Measurable φ) {c : ℝ} (hdiff : ∀ γ x i a, |φ (γ,
    Function.update x i a) - φ (γ, x)| ≤ c) (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i
    ω)) μ) (t : ℝ),
      Integrable (fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
          (μ[fun ω => φ (Γ ω, fun i => ξ i ω) | MeasurableSpace.comap Γ inferInstance]) ω))) μ ∧
        μ[fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
              (μ[fun ω => φ (Γ ω, fun i => ξ i ω) |
                MeasurableSpace.comap Γ inferInstance]) ω)) |
            MeasurableSpace.comap Γ inferInstance] =ᵐ[μ]
          fun ω => ∫ x, Real.exp (t * (φ (Γ ω, x) -
            ∫ y, φ (Γ ω, y) ∂Measure.pi fun i => μ.map (ξ i))) ∂Measure.pi fun i => μ.map (ξ i)) =
    type_of% (@R56Audit.fact_A_1_freeze Ω G E) := rfl

-- `abs_sub_le_of_bounded_differences` (BoundedDifferencesGeneral)
example {E : Type*} : (∀ {n : ℕ} (g : (Fin n → E) → ℝ) {c : ℝ} (hdiff : ∀ x i a, |g
    (Function.update x i a) - g x| ≤ c) (x y : Fin n → E),
      |g x - g y| ≤ n * c) =
    type_of% (@R56Audit.abs_sub_le_of_bounded_differences E) := rfl

-- `bounded_differences_pi` (BoundedDifferencesGeneral)
example {E : Type*} : (∀ [MeasurableSpace E] {n : ℕ} (ν : Fin n → Measure E) [∀ i,
    IsProbabilityMeasure (ν i)] (g : (Fin n → E) → ℝ) (hg : Measurable g) {c : ℝ} (hc : 0 ≤ c)
    (hdiff : ∀ x i a, |g (Function.update x i a) - g x| ≤ c) (t : ℝ),
      ∫ x, Real.exp (t * (g x - ∫ y, g y ∂Measure.pi ν)) ∂Measure.pi ν ≤
        Real.exp (n * t ^ 2 * c ^ 2 / 2)) =
    type_of% (@R56Audit.bounded_differences_pi E) := rfl

-- `exp_mul_le_chord` (BoundedDifferencesGeneral)
example : (∀ {c : ℝ} (hc : 0 < c) (t : ℝ) {y : ℝ} (hy : |y| ≤ c),
      Real.exp (t * y) ≤
        (c + y) / (2 * c) * Real.exp (t * c) + (c - y) / (2 * c) * Real.exp (-(t * c))) =
    type_of% @R56Audit.exp_mul_le_chord := rfl

-- `integral_exp_le_cosh` (BoundedDifferencesGeneral)
example {α : Type*} : (∀ [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {Y : α →
    ℝ} (hY : Measurable Y) {c : ℝ} (hc : 0 < c) (hbd : ∀ x, |Y x| ≤ c) (hmean : ∫ x, Y x ∂μ = 0)
    (t : ℝ),
      ∫ x, Real.exp (t * Y x) ∂μ ≤ Real.cosh (t * c)) =
    type_of% (@R56Audit.integral_exp_le_cosh α) := rfl

-- `cosh_le_exp_sq_half` (BoundedDifferencesGeneral)
example : (∀ (x : ℝ),
      Real.cosh x ≤ Real.exp (x ^ 2 / 2)) =
    type_of% @R56Audit.cosh_le_exp_sq_half := rfl

-- `integral_exp_le_of_centered` (BoundedDifferencesGeneral)
example {α : Type*} : (∀ [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {Y : α →
    ℝ} (hY : Measurable Y) {c : ℝ} (hc : 0 < c) (hbd : ∀ x, |Y x| ≤ c) (hmean : ∫ x, Y x ∂μ = 0)
    (t : ℝ),
      ∫ x, Real.exp (t * Y x) ∂μ ≤ Real.exp (t ^ 2 * c ^ 2 / 2)) =
    type_of% (@R56Audit.integral_exp_le_of_centered α) := rfl

-- `integral_exp_centered_le` (BoundedDifferencesGeneral)
example {α : Type*} : (∀ [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {f : α →
    ℝ} (hf : Measurable f) {c : ℝ} (hc : 0 ≤ c) (hosc : ∀ x y, |f x - f y| ≤ c) (t : ℝ),
      ∫ x, Real.exp (t * (f x - ∫ y, f y ∂μ)) ∂μ ≤ Real.exp (t ^ 2 * c ^ 2 / 2)) =
    type_of% (@R56Audit.integral_exp_centered_le α) := rfl

-- "One difference" as the manuscript states it, for a σ-field `𝓗` (a restatement: the proof
-- of `fact_A_1` uses the forms above, for product measures).
-- `condExp_exp_le_cosh` (BoundedDifferencesGeneral)
example {Ω : Type*} : (∀ {m m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (hm
    : m ≤ m0) {Y : Ω → ℝ} (hY : Measurable Y) {c : ℝ} (hc : 0 < c) (hbd : ∀ ω, |Y ω| ≤ c) (hmean
    : μ[Y | m] =ᵐ[μ] 0) (t : ℝ),
      ∀ᵐ ω ∂μ, (μ[fun ω => Real.exp (t * Y ω) | m]) ω ≤ Real.cosh (t * c)) =
    type_of% (@R56Audit.condExp_exp_le_cosh Ω) := rfl

-- `condExp_exp_le_exp_sq` (BoundedDifferencesGeneral)
example {Ω : Type*} : (∀ {m m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (hm
    : m ≤ m0) {Y : Ω → ℝ} (hY : Measurable Y) {c : ℝ} (hc : 0 < c) (hbd : ∀ ω, |Y ω| ≤ c) (hmean
    : μ[Y | m] =ᵐ[μ] 0) (t : ℝ),
      ∀ᵐ ω ∂μ, (μ[fun ω => Real.exp (t * Y ω) | m]) ω ≤ Real.exp (t ^ 2 * c ^ 2 / 2)) =
    type_of% (@R56Audit.condExp_exp_le_exp_sq Ω) := rfl

/-! ## Statements about the archive's routes (not used by the results above) -/

-- The archive's theorems, restated with `F_χ` and `‖F_χ‖∞`: the same statements.
example : type_of% @R56Audit.theorem_1_1_archive = type_of% @R56Audit.theorem_1_1 := rfl

example :
    type_of% @R56Audit.corollary_1_2_lower_archive = type_of% @R56Audit.corollary_1_2_lower :=
  rfl

-- `theorem_1_1_event_archive` (ArchiveRoute)
example : (
      ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        ∃ G : Set (Fin n → ℝ × ℝ), MeasurableSet G ∧
          ENNReal.ofReal (1 - Real.exp (-A * n)) ≤ unifPts n G ∧
          ∀ P ∈ G, Function.Injective P ∧
            ∀ χ : Fin n → ℤˣ, c * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P) =
    type_of% @R56Audit.theorem_1_1_event_archive := rfl

-- `exists_points_anchored_archive` (ArchiveRoute)
example : (
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        ∃ P : Fin n → ℝ × ℝ, Function.Injective P ∧
          ∀ χ : Fin n → ℤˣ, c * Real.logb 2 n ^ (3 / 2 : ℝ) < supNorm χ P) =
    type_of% @R56Audit.exists_points_anchored_archive := rfl

-- Lemma 2.5(ii) and Proposition 2.7 by the archive's estimates: the same statements.
example {n : ℕ} : type_of% (@R56Audit.lemma_2_5_ii_archive n) = type_of% (@R56Audit.lemma_2_5_ii n) :=
  rfl

example : type_of% @R56Audit.proposition_2_7_probe = type_of% @R56Audit.proposition_2_7 := rfl

-- `proposition_2_7_archive` (ArchiveRoute)
example : (∀ {n b h : ℕ} (hb : 3 ≤ b) (hpar : Even b ∨ b ≤ 48) (hh : 1 ≤ h) (hMn : b ^ (h - 1) ≤
    n),
      (unifPts n).real {P | ∃ χ : Fin n → ℤˣ,
          supNorm χ P ≤ (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))} ≤
        h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
          2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3)))) =
    type_of% @R56Audit.proposition_2_7_archive := rfl

-- The archive's good-transition event is the event `G_j`, on the probability-one event.
example (b h j c v : ℕ) :
    innerRegionIoc b h j c v =
      Set.Ioc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
        Set.Ioc (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h)
          ((((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h) := rfl

-- `mem_innerRegion_iff_Ioc` (GoodTransitionsArchive)
example : (∀ (b h j c v : ℕ) (z : ℝ × ℝ) (hx : z.1 ≠ (c : ℝ) / (b : ℝ) ^ j) (hy1 : z.2 ≠ ((v :
    ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h) (hy2 : z.2 ≠ (((v : ℝ) + 1) * (b : ℝ) ^
    (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h),
      z ∈ innerRegion b h j c v ↔ z ∈ innerRegionIoc b h j c v) =
    type_of% @R56Audit.mem_innerRegion_iff_Ioc := rfl

-- `mem_paperGoodTransition_iff` (GoodTransitionsArchive)
open Oscillation.Direct in
example : (∀ {n : ℕ} {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) (P : Fin n → ℝ × ℝ) (hP : InUnit P)
    (hgrid : NoGrid b P),
      P ∈ paperGoodTransition b h (by omega) j ↔ GoodTransition b h j P) =
    type_of% @R56Audit.mem_paperGoodTransition_iff := rfl

-- The archive's conditional gain, `Oscillation.gridPotential_drift_even`, without `Even b`.
-- `gridPotential_drift_all` (GridDrift)
example : (∀ {n : ℕ} {K V b m : ℕ} (hK : 0 < K) (hV : 0 < V) (hb : 2 ≤ b) (hm : 0 < m) (χ : Fin
    n → ℝ) (hχ : ∀ i, |χ i| = 1) (p Y : Fin n → ℕ),
      interiorMass K V b m p Y / (4 * (b : ℝ) * (K * V : ℕ)) ≤
        finAvg (fun r : Fin n → Fin b =>
          gridPotential (K * b) V (b * m) (Nat.mul_pos (by omega : 0 < b) hm) χ
            (refinedPositions p r) Y) -
        gridPotential K (V * b) m hm χ p Y) =
    type_of% @R56Audit.gridPotential_drift_all := rfl

example {n K V b m : ℕ} (hK : 0 < K) (hV : 0 < V) (hb : 0 < b) (heven : Even b) (hm : 0 < m)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (p Y : Fin n → ℕ) :
    interiorMass K V b m p Y / (4 * (b : ℝ) * (K * V : ℕ)) ≤
      finAvg (fun r : Fin n → Fin b =>
        gridPotential (K * b) V (b * m) (Nat.mul_pos hb hm) χ (refinedPositions p r) Y) -
      gridPotential K (V * b) m hm χ p Y :=
  Oscillation.gridPotential_drift_even hK hV hb heven hm χ hχ p Y

/-! ## Axioms of every declaration of the supplement -/

-- As `#print axioms` reports them. (`SupplementAudit.lean` checks the same by walking the
-- proof terms, and checks the kinds of all constants.)
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  let mut mods := 0
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if (`R56Audit).isPrefixOf m then
      mods := mods + 1
      for n in env.header.moduleData[i]!.constNames do
        let some ci := env.find? n | throwError "constant {n} not found"
        match ci with
        | .axiomInfo _ => throwError "axiom in the supplement: {n}"
        | .opaqueInfo _ => throwError "opaque in the supplement: {n}"
        | _ => pure ()
        if ci.isUnsafe || ci.isPartial then throwError "unsafe or partial: {n}"
        let axioms ← collectAxioms n
        for ax in axioms do
          unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
            throwError "unexpected axiom {ax} in {n}"
        count := count + 1
  IO.println s!"SUPPLEMENT: {mods} modules, {count} constants, all within propext / Classical.choice / Quot.sound"

#print axioms R56Audit.theorem_1_1
#print axioms R56Audit.theorem_1_1_unfolded
#print axioms R56Audit.corollary_1_2_lower
#print axioms R56Audit.proposition_2_7
#print axioms R56Audit.vertical_comparison
#print axioms R56Audit.fact_2_2_general
#print axioms R56Audit.local_gain
#print axioms R56Audit.lemma_2_4_digits
#print axioms R56Audit.lemma_2_5_ii_all
#print axioms R56Audit.lemma_2_6_digits
#print axioms R56Audit.fact_A_1
#print axioms R56Audit.one_rectangle

/-! ## The route of the proof -/

-- Theorem 1.1 and its companions go through the statements listed in `must`: the numbered
-- statements of the manuscript and steps of their proofs, and the bridge `condExp_digitSigma`
-- between the two descriptions of `𝓕_j`. They use none of the declarations of the archive's
-- own proof listed in `mustNot` and nothing from the namespaces `Oscillation.Direct` and
-- `Oscillation.R65`; and everything they use of the archive lies in the eight modules listed
-- in `archiveModules` (the law of the points, finite averages, the index of an interval, and
-- the conditional law of the next digit).
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleOf : Name → Option Name := fun n =>
    (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
  let inArchive : Name → Bool := fun n =>
    match moduleOf n with
    | some m => (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m
    | none => false
  let isLocal : Name → Bool := fun n =>
    match moduleOf n with
    | some m => (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m || (`R56Audit).isPrefixOf m
    | none => false
  -- all local constants that occur in the statement or in the proof of `root`, transitively
  let reach : Name → CommandElabM NameSet := fun root => do
    let mut todo : Array Name := #[root]
    let mut seen : NameSet := {}
    while todo.size > 0 do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n || !isLocal n then continue
      seen := seen.insert n
      let some ci := env.find? n | throwError "constant {n} not found"
      for m in ci.getUsedConstantsAsSet do
        unless seen.contains m do todo := todo.push m
    return seen
  let must : List Name := [`R56Audit.proposition_2_7, `R56Audit.roadmap_digits,
    `R56Audit.lemma_2_4_digits, `R56Audit.local_gain, `R56Audit.vertical_comparison,
    `R56Audit.fact_2_2_general, `R56Audit.display_8, `R56Audit.expected_offset_ge_sigma,
    `R56Audit.lemma_2_5_i, `R56Audit.lemma_2_5_ii, `R56Audit.lemma_2_5_ii_all,
    `R56Audit.lemma_2_6_digits,
    `R56Audit.Zstep_update_le, `R56Audit.fact_A_1, `R56Audit.integral_prod_le_of_condExp_le,
    `R56Audit.measureReal_le_exp_mul_integral_exp_neg, `R56Audit.condExp_digitSigma,
    `R56Audit.Zpot_le_two_supNorm, `R56Audit.Zpot_nonneg, `R56Audit.fluct_le_of_good,
    `R56Audit.exponent_eq, `R56Audit.prob_exists_small_le, `R56Audit.display_16,
    `R56Audit.display_17, `R56Audit.display_18, `R56Audit.ae_cA_mul_lt_supNorm,
    `R56Audit.failure_le, `R56Audit.threshold_gt]
  let mustNot : List Name := [`Oscillation.gridPotential, `Oscillation.gridPotential_drift_even,
    `Oscillation.local_gridMax_gain, `Oscillation.midpoint_range_comparison,
    `Oscillation.abs_mean_of_fourth_three, `Oscillation.shifted_rademacher_abs,
    `Oscillation.finAvg_exp_boundedDifferences, `Oscillation.stage_centered_lower_tail,
    `Oscillation.integral_prefixProduct_le_of_cond, `Oscillation.small_event_of_laplace,
    `Oscillation.paper_lower_bound, `Oscillation.planar_tusnady_lower_bound,
    `Oscillation.Direct.proposition_2_7, `Oscillation.Direct.union_simultaneous_bound,
    `Oscillation.Direct.allGood_compl_bound, `Oscillation.Direct.paper_bad_transition_bound,
    `Oscillation.Direct.paperGoodTransition, `Oscillation.Direct.point_exp_loss,
    `Oscillation.Direct.loss_tail, `Oscillation.R65.simultaneous_bound,
    `Oscillation.R65.all_good_compl_bound, `Oscillation.R65.bad_transition_bound,
    `Riesz.PointSets.badSet, `Riesz.PointSets.GoodEvent, `Riesz.PaperLowerBound,
    `R56Audit.gridPotential_drift_all, `R56Audit.union_simultaneous_bound_all,
    `R56Audit.proposition_2_7_probe, `R56Audit.proposition_2_7_archive,
    `R56Audit.theorem_1_1_archive, `R56Audit.theorem_1_1_event_archive,
    `R56Audit.lemma_2_5_ii_archive, `R56Audit.lemma_2_5_ii_all_archive]
  let archiveModules : List Name := [`Oscillation.CoordinateProduct, `Oscillation.FiniteAverage,
    `Riesz.CellAverages, `Riesz.ConditionalGridProduct, `Riesz.GridRefinement, `Riesz.Occupancy,
    `Riesz.PointSets, `Riesz.UniformGrid]
  for n in must ++ mustNot do
    unless env.contains n do throwError "unknown constant {n}"
  for root in [`R56Audit.theorem_1_1, `R56Audit.theorem_1_1_unfolded,
      `R56Audit.theorem_1_1_constant, `R56Audit.theorem_1_1_constant_event,
      `R56Audit.exists_points, `R56Audit.corollary_1_2_lower] do
    let used ← reach root
    for n in must do
      unless used.contains n do throwError "{root} does not use {n}"
    for n in mustNot do
      if used.contains n then throwError "{root} uses {n}"
    let mut archive : NameSet := {}
    for n in used.toList do
      if (`Oscillation.Direct).isPrefixOf n || (`Oscillation.R65).isPrefixOf n then
        throwError "{root} uses {n}"
      if inArchive n then
        let some m := moduleOf n | continue
        unless archiveModules.contains m do throwError "{root} uses {n} of the module {m}"
        archive := archive.insert m
    unless archive.size == archiveModules.length do
      throwError "{root} uses only the archive modules {archive.toList}"
    IO.println s!"ROUTE {root}: {used.size} local constants; uses the {must.length} listed statements, none of the {mustNot.length} excluded declarations, and of the archive only the {archiveModules.length} listed modules"
  -- which of the statement gates above are on the route of Theorem 1.1 and Corollary 1.2
  let pinned : List Name := [`R56Audit.F_eq_filter, `R56Audit.Zpot_ae_eq_Zproc,
    `R56Audit.Zpot_aestronglyMeasurable, `R56Audit.Zpot_aestronglyMeasurable_digits,
    `R56Audit.Zpot_eq_Zstep, `R56Audit.Zpot_ge_of_good, `R56Audit.Zpot_le_of_small,
    `R56Audit.Zpot_le_two_supNorm, `R56Audit.Zpot_nonneg, `R56Audit.Zstep_eq_sum_blocks,
    `R56Audit.Zstep_gain, `R56Audit.Zstep_succ_eq_sum_children, `R56Audit.Zstep_update_le,
    `R56Audit.abs_jump_le, `R56Audit.abs_osc_add_sub_le, `R56Audit.abs_osc_endpointAvg_sub_le,
    `R56Audit.abs_sub_le_of_bounded_differences, `R56Audit.add_minOn_le,
    `R56Audit.add_one_le_exp_two_mul, `R56Audit.add_one_mul_exp_le,
    `R56Audit.ae_cA_mul_lt_supNorm, `R56Audit.ae_heights_injective, `R56Audit.ae_inUnit,
    `R56Audit.ae_noGrid, `R56Audit.ae_one_le_supNorm, `R56Audit.ae_setupEvent,
    `R56Audit.avg_comparison_core, `R56Audit.bad_ae_le_iUnion_crowdEvent, `R56Audit.base_ge_49,
    `R56Audit.base_pow_eq_mul_pow, `R56Audit.block_disjoint, `R56Audit.bottomStrip_eq_cell,
    `R56Audit.bounded_differences_pi, `R56Audit.cA_mul_lt_of_lt, `R56Audit.cA_mul_lt_one,
    `R56Audit.cA_pos, `R56Audit.card_cells_stage, `R56Audit.card_colorings,
    `R56Audit.card_compRect, `R56Audit.card_heavySet_lt, `R56Audit.card_mul_osc_avg_le,
    `R56Audit.card_smallCollections_le, `R56Audit.childAvg_eq_F, `R56Audit.childMean_eq,
    `R56Audit.coarseInfo_ae_eq_digitInfo, `R56Audit.compRect_eq_iUnion_new,
    `R56Audit.compRect_eq_iUnion_old, `R56Audit.condExp_Zproc_succ,
    `R56Audit.condExp_comap_eq_integral_of_indepFun, `R56Audit.condExp_digitSigma,
    `R56Audit.condExp_exp_le_cosh, `R56Audit.condExp_exp_le_exp_sq, `R56Audit.condExp_exp_step,
    `R56Audit.condExp_fresh_given_heights, `R56Audit.condExp_gain, `R56Audit.condExp_nextDigits,
    `R56Audit.condGain_ge_deltaStar, `R56Audit.corollary_1_2_lower,
    `R56Audit.cosh_le_exp_sq_half, `R56Audit.deltaStar_sq, `R56Audit.delta_eq_deltaStep,
    `R56Audit.digitInfo_ae_eq_coarseInfo, `R56Audit.display_16, `R56Audit.display_17,
    `R56Audit.display_18, `R56Audit.display_5, `R56Audit.display_6, `R56Audit.display_8,
    `R56Audit.endAvg_image_finite, `R56Audit.endpointAvg_eq_F, `R56Audit.exists_base_of_15,
    `R56Audit.exists_card_eq_ceil_half, `R56Audit.exists_childIndex,
    `R56Audit.exists_eq_supNorm, `R56Audit.exists_isScale, `R56Audit.exists_points,
    `R56Audit.exists_points_anchored_archive, `R56Audit.exists_symm_perm_iff,
    `R56Audit.exp_mul_le_chord, `R56Audit.expected_comparison_core,
    `R56Audit.expected_offset_core, `R56Audit.expected_offset_core_sigma,
    `R56Audit.expected_offset_ge, `R56Audit.expected_offset_ge_sigma, `R56Audit.exponent_eq,
    `R56Audit.exponent_ge, `R56Audit.exponent_gt, `R56Audit.fact_2_2_general,
    `R56Audit.fact_2_2_uniform, `R56Audit.fact_A_1, `R56Audit.fact_A_1_freeze,
    `R56Audit.fact_A_1_integrable, `R56Audit.failure_le, `R56Audit.finAvg_childIndex,
    `R56Audit.finAvg_childIndex_sq, `R56Audit.finAvg_childIndex_var, `R56Audit.finAvg_childMean,
    `R56Audit.finAvg_jump, `R56Audit.finAvg_jump_fourth_le, `R56Audit.finAvg_jump_fourth_le_sq,
    `R56Audit.finAvg_jump_sq, `R56Audit.finAvg_minOn_childMean_le, `R56Audit.first_term_le,
    `R56Audit.first_term_le_mul, `R56Audit.fluctDigits_ae_eq, `R56Audit.fluctTerm_ae_eq,
    `R56Audit.fluctTerm_measurable_of_lt, `R56Audit.fluct_ae_eq, `R56Audit.fluct_le_of_good,
    `R56Audit.fresh_eq_digit, `R56Audit.good_inter_small_le, `R56Audit.gridIndex_eq_idxOfDigits,
    `R56Audit.gridIndex_succ, `R56Audit.gridPotential_drift_all, `R56Audit.half_lt_card_Wset,
    `R56Audit.half_osc_add_abs_mid_sub_le, `R56Audit.hcell_eq_iUnion_children,
    `R56Audit.iIndepFun_fresh, `R56Audit.iUnion_block, `R56Audit.iUnion_cell,
    `R56Audit.iUnion_hcell, `R56Audit.iUnion_inner_blocks, `R56Audit.iUnion_vcell,
    `R56Audit.identDistrib_sum_neg, `R56Audit.inUnit_of_noGrid, `R56Audit.indepFun_coarse_fresh,
    `R56Audit.innerCount_eq_card_innerSet, `R56Audit.innerPoints_between_blocks,
    `R56Audit.innerRegion_eq_diff, `R56Audit.innerRegion_eq_iUnion, `R56Audit.innerRegion_inj,
    `R56Audit.inner_blocks_nonempty, `R56Audit.integral_abs_add_eq_integral_abs_sub,
    `R56Audit.integral_abs_le_integral_abs_add_of_symm, `R56Audit.integral_exp_centered_le,
    `R56Audit.integral_exp_le_cosh, `R56Audit.integral_exp_le_of_centered,
    `R56Audit.integral_exp_neg_sum_le, `R56Audit.integral_pow_eq_zero_of_symm,
    `R56Audit.integral_prod_le_of_condExp_le, `R56Audit.integral_sq_le_rpow_mul_rpow,
    `R56Audit.inv_pow_eight_mul_rpow_lt_one, `R56Audit.inv_pow_five_le_one, `R56Audit.jump_rev,
    `R56Audit.jump_sq_eq, `R56Audit.le_maxOn, `R56Audit.le_of_scaleOK, `R56Audit.lemma_2_4,
    `R56Audit.lemma_2_4_digits, `R56Audit.lemma_2_5_i, `R56Audit.lemma_2_5_ii,
    `R56Audit.lemma_2_5_ii_all, `R56Audit.lemma_2_6, `R56Audit.lemma_2_6_digits,
    `R56Audit.lemma_2_6_markov, `R56Audit.lemma_2_6_step2, `R56Audit.lemma_2_6_step3,
    `R56Audit.local_gain, `R56Audit.local_gain_core, `R56Audit.local_gain_sets,
    `R56Audit.lt_of_isScale, `R56Audit.lt_two_mul_pow_of_isScale, `R56Audit.lt_Δ₂_of_supNorm,
    `R56Audit.maxOn_add_le, `R56Audit.maxOn_endpointAvg_le, `R56Audit.maxOn_eq_mid_add,
    `R56Audit.maxOn_mem, `R56Audit.maxOn_sub_minOn_eq, `R56Audit.maxOn_sub_minOn_le_osc,
    `R56Audit.measurableSet_exists_supNorm_le, `R56Audit.measurableSet_fluctDigits_le,
    `R56Audit.measurableSet_fluct_le, `R56Audit.measurableSet_forall_le_supNorm,
    `R56Audit.measurableSet_goodTransition, `R56Audit.measurable_Zpot,
    `R56Audit.measurable_digitInfo, `R56Audit.measurable_nextDigits,
    `R56Audit.measurable_supNorm, `R56Audit.measureReal_le_exp_mul_integral_exp_neg,
    `R56Audit.mem_boundaryStrips_or_innerRegion, `R56Audit.mem_crowdEvent_heavySet,
    `R56Audit.mem_innerPoints_iff, `R56Audit.mem_innerRegion_iff_Ioc,
    `R56Audit.mem_paperGoodTransition_iff, `R56Audit.mid_add_const, `R56Audit.minOn_eq_mid_sub,
    `R56Audit.minOn_le, `R56Audit.minOn_mem, `R56Audit.mul_sqrt_le_of_moments,
    `R56Audit.nextDigits_ae_eq_freshInfo, `R56Audit.offset_core, `R56Audit.offset_eq,
    `R56Audit.one_le_supNorm, `R56Audit.one_rectangle, `R56Audit.osc_add_const,
    `R56Audit.osc_add_le, `R56Audit.osc_const_mul, `R56Audit.osc_endpointAvg_le,
    `R56Audit.osc_le_osc_add_add, `R56Audit.osc_mono, `R56Audit.osc_neg,
    `R56Audit.osc_stepFn_single_le, `R56Audit.osc_sum_le, `R56Audit.prob_exists_small_le,
    `R56Audit.prob_exists_supNorm_le, `R56Audit.prob_exists_supNorm_le_of_pow_le,
    `R56Audit.proposition_2_7, `R56Audit.proposition_2_7_archive, `R56Audit.roadmap,
    `R56Audit.roadmap_digits, `R56Audit.rpow_div_ge, `R56Audit.scaleOK_one,
    `R56Audit.scale_div_pow_five_lt_one, `R56Audit.scale_le_of_pow_le,
    `R56Audit.scale_le_two_pow, `R56Audit.scale_lt_pow_five, `R56Audit.scale_succ_le_two_mul,
    `R56Audit.scale_succ_le_two_pow, `R56Audit.second_term_le,
    `R56Audit.second_term_le_two_pow_mul, `R56Audit.sigma_mul_sqrt_eq,
    `R56Audit.sixty_four_le_pow_four, `R56Audit.sq_mul_sigma_sq_le, `R56Audit.sqrt_div_eight_le,
    `R56Audit.sqrt_sq_sub_one_div_ge, `R56Audit.stageSigma_le, `R56Audit.stageSigma_succ_le,
    `R56Audit.stepFn_image_finite, `R56Audit.stepFn_single_eq_of_notMem,
    `R56Audit.sum_childWeight, `R56Audit.sum_fourth_moment_le, `R56Audit.sum_moments,
    `R56Audit.sum_terms_le, `R56Audit.supNorm_le_iff, `R56Audit.symmetric_sum_abs,
    `R56Audit.theorem_1_1, `R56Audit.theorem_1_1_constant, `R56Audit.theorem_1_1_constant_event,
    `R56Audit.theorem_1_1_event_archive, `R56Audit.theorem_1_1_unfolded, `R56Audit.threshold_eq,
    `R56Audit.threshold_ge_sqrt, `R56Audit.threshold_gt, `R56Audit.threshold_sqrt_eq,
    `R56Audit.topStrip_eq_cell, `R56Audit.two_pow_le_base_pow, `R56Audit.two_pow_mul_exp_eq,
    `R56Audit.two_pow_mul_rpow_le, `R56Audit.unifPts_bad_le, `R56Audit.unifPts_crowdEvent_le,
    `R56Audit.unifPts_forall_mem, `R56Audit.unifPts_forall_mem_le,
    `R56Audit.unifPts_half_mem_le, `R56Audit.vcell_disjoint, `R56Audit.vcell_succ_eq_iUnion,
    `R56Audit.vertical_comparison, `R56Audit.vertical_comparison_sets, `R56Audit.volume_Wset_le,
    `R56Audit.volume_boundaryStrips, `R56Audit.volume_boundaryStrips_le, `R56Audit.volume_cell,
    `R56Audit.volume_compRect, `R56Audit.volume_innerRegion_lt,
    `R56Audit.volume_innerRegions_le, `R56Audit.volume_innerRegions_lt,
    `R56Audit.withoutJumps_eq]
  let used := (← reach `R56Audit.theorem_1_1) ++ (← reach `R56Audit.corollary_1_2_lower)
  let off := pinned.filter fun n => !used.contains n
  IO.println s!"PINNED {pinned.length} statements: {pinned.length - off.length} are used by Theorem 1.1 or Corollary 1.2; the other {off.length} are not: {off.map fun n => n.replacePrefix `R56Audit .anonymous}"
  -- the statements that use Mathlib only
  for root in [`R56Audit.vertical_comparison, `R56Audit.fact_2_2_general, `R56Audit.lemma_2_5_i,
      `R56Audit.fact_A_1, `R56Audit.integral_prod_le_of_condExp_le,
      `R56Audit.measureReal_le_exp_mul_integral_exp_neg] do
    let used ← reach root
    for n in used.toList do
      if inArchive n then throwError "{root} uses the archive: {n}"
    IO.println s!"MATHLIB ONLY {root}: {used.size} supplement constants, no archive constant"

/-! ## The reading list -/

-- Every definition that one has to read in order to understand a statement gate above has a
-- definition gate above. Here "has to read" means: the definitions of the supplement and of
-- the archive that occur in the statement, and recursively in the types and in the bodies of
-- those definitions. (`freshGridIndex` is read through the equation proved above and not
-- through its body: the walk continues with the statement of the archive's theorem
-- `freshGridIndex_eq_emod`, which mentions the same definitions.) The statements of the last
-- section, about the archive's own routes, are not included: they speak about the archive's
-- definitions. The statement of `theorem_1_1_unfolded` contains no definition of the
-- supplement or of the archive at all.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let isLocal : Name → Bool := fun n =>
    match (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]! with
    | some m => (`Oscillation).isPrefixOf m || (`Riesz).isPrefixOf m || (`R56Audit).isPrefixOf m
    | none => false
  let gated : List Name := [`Riesz.PointSets.unifPts, `R56Audit.F, `R56Audit.supNorm,
    `R56Audit.cA, `Riesz.PointSets.Δ₂, `Riesz.PointSets.rectDisc, `Riesz.PointSets.colorSum,
    `R56Audit.SetupEvent, `R56Audit.NoGrid, `R56Audit.InUnit, `R56Audit.endAvg,
    `R56Audit.sideOf, `R56Audit.Side, `R56Audit.Side.left, `R56Audit.Side.inside,
    `R56Audit.Side.right, `R56Audit.oldWeight, `R56Audit.sgn, `R56Audit.stepFn,
    `R56Audit.endpointAvg, `R56Audit.maxOn, `R56Audit.minOn, `R56Audit.osc, `R56Audit.mid,
    `R56Audit.block, `Oscillation.finAvg, `R56Audit.childWeight, `R56Audit.childAvg,
    `R56Audit.innerPoints, `R56Audit.jumpSum, `R56Audit.childMean, `R56Audit.jump,
    `R56Audit.withoutJumps, `R56Audit.heightSigma, `R56Audit.unitInnerRegion,
    `R56Audit.unitInnerCount, `R56Audit.hcell, `R56Audit.vlen, `R56Audit.vcell, `R56Audit.cell,
    `R56Audit.Zpot, `R56Audit.digit, `R56Audit.digitInfo, `R56Audit.digitSigma,
    `Riesz.gridIndex, `R56Audit.coarseInfo, `R56Audit.stageSigma, `R56Audit.idxOfDigits,
    `R56Audit.digitsOfIdx, `R56Audit.coarseOfDigits, `R56Audit.digitsOfCoarse,
    `R56Audit.nextDigits, `Riesz.freshGridIndex, `R56Audit.freshInfo, `Riesz.PointSets.μI,
    `Oscillation.pointSampleLaw, `R56Audit.fluctDigits, `R56Audit.fluct, `R56Audit.compRect,
    `R56Audit.innerRegion, `R56Audit.innerCount, `R56Audit.delta, `R56Audit.Zstep,
    `R56Audit.sideIdx, `R56Audit.refineIdx, `R56Audit.innerSet, `R56Audit.deltaStep,
    `R56Audit.Zproc, `R56Audit.Zmean, `R56Audit.Heavy, `R56Audit.GoodTransition,
    `R56Audit.deltaStar, `R56Audit.bottomStrip, `R56Audit.topStrip, `R56Audit.boundaryStrips,
    `R56Audit.Wset, `R56Audit.heavySet, `R56Audit.crowdEvent, `R56Audit.smallCollections,
    `R56Audit.fluctStep, `R56Audit.ScaleOK, `R56Audit.IsScale, `R56Audit.innerRegionIoc]
  let toRead : List Name := [`R56Audit.F_eq_filter, `R56Audit.Zpot_ae_eq_Zproc,
    `R56Audit.Zpot_aestronglyMeasurable, `R56Audit.Zpot_aestronglyMeasurable_digits,
    `R56Audit.Zpot_eq_Zstep, `R56Audit.Zpot_ge_of_good, `R56Audit.Zpot_le_of_small,
    `R56Audit.Zpot_le_two_supNorm, `R56Audit.Zpot_nonneg, `R56Audit.Zstep_eq_sum_blocks,
    `R56Audit.Zstep_gain, `R56Audit.Zstep_succ_eq_sum_children, `R56Audit.Zstep_update_le,
    `R56Audit.abs_jump_le, `R56Audit.abs_osc_add_sub_le, `R56Audit.abs_osc_endpointAvg_sub_le,
    `R56Audit.abs_sub_le_of_bounded_differences, `R56Audit.add_minOn_le,
    `R56Audit.add_one_le_exp_two_mul, `R56Audit.add_one_mul_exp_le,
    `R56Audit.ae_cA_mul_lt_supNorm, `R56Audit.ae_heights_injective, `R56Audit.ae_inUnit,
    `R56Audit.ae_noGrid, `R56Audit.ae_one_le_supNorm, `R56Audit.ae_setupEvent,
    `R56Audit.avg_comparison_core, `R56Audit.bad_ae_le_iUnion_crowdEvent, `R56Audit.base_ge_49,
    `R56Audit.base_pow_eq_mul_pow, `R56Audit.block_disjoint, `R56Audit.bottomStrip_eq_cell,
    `R56Audit.bounded_differences_pi, `R56Audit.cA_mul_lt_of_lt, `R56Audit.cA_mul_lt_one,
    `R56Audit.cA_pos, `R56Audit.card_cells_stage, `R56Audit.card_colorings,
    `R56Audit.card_compRect, `R56Audit.card_heavySet_lt, `R56Audit.card_mul_osc_avg_le,
    `R56Audit.card_smallCollections_le, `R56Audit.childAvg_eq_F, `R56Audit.childMean_eq,
    `R56Audit.coarseInfo_ae_eq_digitInfo, `R56Audit.compRect_eq_iUnion_new,
    `R56Audit.compRect_eq_iUnion_old, `R56Audit.condExp_Zproc_succ,
    `R56Audit.condExp_comap_eq_integral_of_indepFun, `R56Audit.condExp_digitSigma,
    `R56Audit.condExp_exp_le_cosh, `R56Audit.condExp_exp_le_exp_sq, `R56Audit.condExp_exp_step,
    `R56Audit.condExp_fresh_given_heights, `R56Audit.condExp_gain, `R56Audit.condExp_nextDigits,
    `R56Audit.condGain_ge_deltaStar, `R56Audit.corollary_1_2_lower,
    `R56Audit.cosh_le_exp_sq_half, `R56Audit.deltaStar_sq, `R56Audit.delta_eq_deltaStep,
    `R56Audit.digitInfo_ae_eq_coarseInfo, `R56Audit.display_16, `R56Audit.display_17,
    `R56Audit.display_18, `R56Audit.display_5, `R56Audit.display_6, `R56Audit.display_8,
    `R56Audit.endAvg_image_finite, `R56Audit.endpointAvg_eq_F, `R56Audit.exists_base_of_15,
    `R56Audit.exists_card_eq_ceil_half, `R56Audit.exists_childIndex,
    `R56Audit.exists_eq_supNorm, `R56Audit.exists_isScale, `R56Audit.exists_points,
    `R56Audit.exists_symm_perm_iff, `R56Audit.exp_mul_le_chord,
    `R56Audit.expected_comparison_core, `R56Audit.expected_offset_core,
    `R56Audit.expected_offset_core_sigma, `R56Audit.expected_offset_ge,
    `R56Audit.expected_offset_ge_sigma, `R56Audit.exponent_eq, `R56Audit.exponent_ge,
    `R56Audit.exponent_gt, `R56Audit.fact_2_2_general, `R56Audit.fact_2_2_uniform,
    `R56Audit.fact_A_1, `R56Audit.fact_A_1_freeze, `R56Audit.fact_A_1_integrable,
    `R56Audit.failure_le, `R56Audit.finAvg_childIndex, `R56Audit.finAvg_childIndex_sq,
    `R56Audit.finAvg_childIndex_var, `R56Audit.finAvg_childMean, `R56Audit.finAvg_jump,
    `R56Audit.finAvg_jump_fourth_le, `R56Audit.finAvg_jump_fourth_le_sq,
    `R56Audit.finAvg_jump_sq, `R56Audit.finAvg_minOn_childMean_le, `R56Audit.first_term_le,
    `R56Audit.first_term_le_mul, `R56Audit.fluctDigits_ae_eq, `R56Audit.fluctTerm_ae_eq,
    `R56Audit.fluctTerm_measurable_of_lt, `R56Audit.fluct_ae_eq, `R56Audit.fluct_le_of_good,
    `R56Audit.fresh_eq_digit, `R56Audit.good_inter_small_le, `R56Audit.gridIndex_eq_idxOfDigits,
    `R56Audit.gridIndex_succ, `R56Audit.half_lt_card_Wset,
    `R56Audit.half_osc_add_abs_mid_sub_le, `R56Audit.hcell_eq_iUnion_children,
    `R56Audit.iIndepFun_fresh, `R56Audit.iUnion_block, `R56Audit.iUnion_cell,
    `R56Audit.iUnion_hcell, `R56Audit.iUnion_inner_blocks, `R56Audit.iUnion_vcell,
    `R56Audit.identDistrib_sum_neg, `R56Audit.inUnit_of_noGrid, `R56Audit.indepFun_coarse_fresh,
    `R56Audit.innerCount_eq_card_innerSet, `R56Audit.innerPoints_between_blocks,
    `R56Audit.innerRegion_eq_diff, `R56Audit.innerRegion_eq_iUnion, `R56Audit.innerRegion_inj,
    `R56Audit.inner_blocks_nonempty, `R56Audit.integral_abs_add_eq_integral_abs_sub,
    `R56Audit.integral_abs_le_integral_abs_add_of_symm, `R56Audit.integral_exp_centered_le,
    `R56Audit.integral_exp_le_cosh, `R56Audit.integral_exp_le_of_centered,
    `R56Audit.integral_exp_neg_sum_le, `R56Audit.integral_pow_eq_zero_of_symm,
    `R56Audit.integral_prod_le_of_condExp_le, `R56Audit.integral_sq_le_rpow_mul_rpow,
    `R56Audit.inv_pow_eight_mul_rpow_lt_one, `R56Audit.inv_pow_five_le_one, `R56Audit.jump_rev,
    `R56Audit.jump_sq_eq, `R56Audit.le_maxOn, `R56Audit.le_of_scaleOK, `R56Audit.lemma_2_4,
    `R56Audit.lemma_2_4_digits, `R56Audit.lemma_2_5_i, `R56Audit.lemma_2_5_ii,
    `R56Audit.lemma_2_5_ii_all, `R56Audit.lemma_2_6, `R56Audit.lemma_2_6_digits,
    `R56Audit.lemma_2_6_markov, `R56Audit.lemma_2_6_step2, `R56Audit.lemma_2_6_step3,
    `R56Audit.local_gain, `R56Audit.local_gain_core, `R56Audit.local_gain_sets,
    `R56Audit.lt_of_isScale, `R56Audit.lt_two_mul_pow_of_isScale, `R56Audit.lt_Δ₂_of_supNorm,
    `R56Audit.maxOn_add_le, `R56Audit.maxOn_endpointAvg_le, `R56Audit.maxOn_eq_mid_add,
    `R56Audit.maxOn_mem, `R56Audit.maxOn_sub_minOn_eq, `R56Audit.maxOn_sub_minOn_le_osc,
    `R56Audit.measurableSet_exists_supNorm_le, `R56Audit.measurableSet_fluctDigits_le,
    `R56Audit.measurableSet_fluct_le, `R56Audit.measurableSet_forall_le_supNorm,
    `R56Audit.measurableSet_goodTransition, `R56Audit.measurable_Zpot,
    `R56Audit.measurable_digitInfo, `R56Audit.measurable_nextDigits,
    `R56Audit.measurable_supNorm, `R56Audit.measureReal_le_exp_mul_integral_exp_neg,
    `R56Audit.mem_boundaryStrips_or_innerRegion, `R56Audit.mem_crowdEvent_heavySet,
    `R56Audit.mem_innerPoints_iff, `R56Audit.mid_add_const, `R56Audit.minOn_eq_mid_sub,
    `R56Audit.minOn_le, `R56Audit.minOn_mem, `R56Audit.mul_sqrt_le_of_moments,
    `R56Audit.nextDigits_ae_eq_freshInfo, `R56Audit.offset_core, `R56Audit.offset_eq,
    `R56Audit.one_le_supNorm, `R56Audit.one_rectangle, `R56Audit.osc_add_const,
    `R56Audit.osc_add_le, `R56Audit.osc_const_mul, `R56Audit.osc_endpointAvg_le,
    `R56Audit.osc_le_osc_add_add, `R56Audit.osc_mono, `R56Audit.osc_neg,
    `R56Audit.osc_stepFn_single_le, `R56Audit.osc_sum_le, `R56Audit.prob_exists_small_le,
    `R56Audit.prob_exists_supNorm_le, `R56Audit.prob_exists_supNorm_le_of_pow_le,
    `R56Audit.proposition_2_7, `R56Audit.roadmap, `R56Audit.roadmap_digits,
    `R56Audit.rpow_div_ge, `R56Audit.scaleOK_one, `R56Audit.scale_div_pow_five_lt_one,
    `R56Audit.scale_le_of_pow_le, `R56Audit.scale_le_two_pow, `R56Audit.scale_lt_pow_five,
    `R56Audit.scale_succ_le_two_mul, `R56Audit.scale_succ_le_two_pow, `R56Audit.second_term_le,
    `R56Audit.second_term_le_two_pow_mul, `R56Audit.sigma_mul_sqrt_eq,
    `R56Audit.sixty_four_le_pow_four, `R56Audit.sq_mul_sigma_sq_le, `R56Audit.sqrt_div_eight_le,
    `R56Audit.sqrt_sq_sub_one_div_ge, `R56Audit.stageSigma_le, `R56Audit.stageSigma_succ_le,
    `R56Audit.stepFn_image_finite, `R56Audit.stepFn_single_eq_of_notMem,
    `R56Audit.sum_childWeight, `R56Audit.sum_fourth_moment_le, `R56Audit.sum_moments,
    `R56Audit.sum_terms_le, `R56Audit.supNorm_le_iff, `R56Audit.symmetric_sum_abs,
    `R56Audit.theorem_1_1, `R56Audit.theorem_1_1_constant, `R56Audit.theorem_1_1_constant_event,
    `R56Audit.theorem_1_1_unfolded, `R56Audit.threshold_eq, `R56Audit.threshold_ge_sqrt,
    `R56Audit.threshold_gt, `R56Audit.threshold_sqrt_eq, `R56Audit.topStrip_eq_cell,
    `R56Audit.two_pow_le_base_pow, `R56Audit.two_pow_mul_exp_eq, `R56Audit.two_pow_mul_rpow_le,
    `R56Audit.unifPts_bad_le, `R56Audit.unifPts_crowdEvent_le, `R56Audit.unifPts_forall_mem,
    `R56Audit.unifPts_forall_mem_le, `R56Audit.unifPts_half_mem_le, `R56Audit.vcell_disjoint,
    `R56Audit.vcell_succ_eq_iUnion, `R56Audit.vertical_comparison,
    `R56Audit.vertical_comparison_sets, `R56Audit.volume_Wset_le,
    `R56Audit.volume_boundaryStrips, `R56Audit.volume_boundaryStrips_le, `R56Audit.volume_cell,
    `R56Audit.volume_compRect, `R56Audit.volume_innerRegion_lt,
    `R56Audit.volume_innerRegions_le, `R56Audit.volume_innerRegions_lt,
    `R56Audit.withoutJumps_eq]
  let characterized : List (Name × Name) :=
    [(`Riesz.freshGridIndex, `Riesz.freshGridIndex_eq_emod)]
  -- constants generated for the inductive type `Side`
  let generated : List Name := [`R56Audit.instDecidableEqSide, `R56Audit.Side.rec,
    `R56Audit.Side.casesOn, `R56Audit.Side.ctorIdx]
  for n in gated ++ toRead ++ characterized.map (·.2) do
    unless env.contains n do throwError "unknown constant {n}"
  let some unfolded := env.find? `R56Audit.theorem_1_1_unfolded
    | throwError "theorem_1_1_unfolded not found"
  let locals := unfolded.type.getUsedConstantsAsSet.toList.filter isLocal
  unless locals.isEmpty do throwError "theorem_1_1_unfolded mentions {locals}"
  let mut todo : Array Name := #[]
  for t in toRead do
    let some ci := env.find? t | throwError "unknown statement {t}"
    todo := todo ++ ci.type.getUsedConstantsAsSet.toArray
  let mut seen : NameSet := {}
  let mut read : Array Name := #[]
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c || !isLocal c then continue
    seen := seen.insert c
    let some ci := env.find? c | throwError "constant {c} not found"
    match characterized.lookup c, ci with
    | _, .thmInfo _ => continue                 -- a proof inside a statement
    | some thm, _ =>
      let some ti := env.find? thm | throwError "constant {thm} not found"
      todo := todo ++ ti.type.getUsedConstantsAsSet.toArray
    | none, .defnInfo v =>
      todo := todo ++ v.type.getUsedConstantsAsSet.toArray ++ v.value.getUsedConstantsAsSet.toArray
    | none, _ => todo := todo ++ ci.type.getUsedConstantsAsSet.toArray
    -- auxiliary constants (proofs inside definitions, matchers) need no reading
    if c.isInternal || (← findDeclarationRanges? c).isNone || generated.contains c then continue
    unless gated.contains c do
      throwError "{c} occurs in a statement gate and has no definition gate"
    read := read.push c
  let unused := gated.filter fun n => !read.contains n
  IO.println s!"READING LIST the statement of theorem_1_1_unfolded contains no constant of the supplement or of the archive; the {toRead.length} statement gates outside the section on the archive's routes involve {read.size} definitions of the supplement and of the archive, each with a definition gate ({gated.length} names have one; not needed for these statements: {unused.map fun n => n.replacePrefix `R56Audit .anonymous})"
