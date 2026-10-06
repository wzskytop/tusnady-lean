import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push

/-!
# Point sets and probability interfaces for the direct Riesz proof

The basic point-set definitions and measure-theoretic proofs are extracted from
`Tusnady/Random.lean` and `Tusnady/PaperBasics.lean` in the audited v8 project
`review/tusnady-v8-verify-20261002-r_n7w581/Tusnady`.
This module imports only Mathlib; no random-walk, spectral-gap, or discrepancy
lower-bound result from the old development is used.
-/

open MeasureTheory Function Finset

namespace Riesz.PointSets

noncomputable abbrev μI : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure μI := ⟨by simp [μI, Real.volume_Icc]⟩

lemma unitSq_eq :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1) = μI.prod μI := by
  rw [Set.Icc_prod_eq, Measure.volume_eq_prod, μI, Measure.prod_restrict]
  simp

lemma μI_cell (m k : ℕ) (hm : 1 ≤ m) (hk : k < m) :
    μI (Set.Ioc ((k : ℝ) / m) (((k : ℝ) + 1) / m)) = ENNReal.ofReal (1 / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsub : Set.Ioc ((k : ℝ) / m) (((k : ℝ) + 1) / m) ⊆ Set.Icc 0 1 := by
    rintro x ⟨h1, h2⟩
    have hk' : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
    constructor
    · exact le_trans (by positivity) h1.le
    · exact le_trans h2 (by rw [div_le_one hm0]; exact hk')
  rw [μI, Measure.restrict_eq_self _ hsub, Real.volume_Ioc]
  congr 1; ring

lemma μI_compl_Ioc : μI (Set.Ioc 0 1)ᶜ = 0 := by
  rw [μI, Measure.restrict_apply measurableSet_Ioc.compl]
  refine measure_mono_null (t := {0}) ?_ (measure_singleton 0)
  rintro x ⟨h1, h2⟩
  simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and, not_le] at h1
  simp only [Set.mem_Icc] at h2
  simp only [Set.mem_singleton_iff]
  by_contra hx
  have := h1 (lt_of_le_of_ne h2.1 (Ne.symm hx))
  linarith [h2.2]

lemma μI_compl_Icc : μI (Set.Icc 0 1)ᶜ = 0 := by
  rw [μI, Measure.restrict_apply measurableSet_Icc.compl]
  refine measure_mono_null (t := ∅) ?_ measure_empty
  rintro x ⟨h1, h2⟩
  exact h1 h2

lemma μI_singleton (a : ℝ) : μI {a} = 0 := by
  rw [μI, Measure.restrict_apply (measurableSet_singleton a)]
  exact measure_mono_null Set.inter_subset_left (measure_singleton a)

/-- Ties have probability zero. -/
lemma diag_null {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Measure.pi (fun _ : Fin n => μI) {y | y i = y j} = 0 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := i.pos; omega⟩
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hij.symm
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n' + 1) => μI) i
  have hset : {y : Fin (n' + 1) → ℝ | y i = y (i.succAbove j')}
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n' + 1) => ℝ) i) ⁻¹'
          {p | p.1 = p.2 j'} := by
    ext y; simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.removeNth_apply]
  rw [hset, hmp.measure_preimage_equiv]
  have hmeas : MeasurableSet {p : ℝ × (Fin n' → ℝ) | p.1 = p.2 j'} :=
    measurableSet_eq_fun (f := fun p : ℝ × (Fin n' → ℝ) => p.1) (g := fun p => p.2 j')
      measurable_fst (by fun_prop)
  refine (Measure.measure_prod_null hmeas).mpr (Filter.Eventually.of_forall fun a => ?_)
  have : Prod.mk a ⁻¹' {p : ℝ × (Fin n' → ℝ) | p.1 = p.2 j'} = Function.eval j' ⁻¹' ({a} : Set ℝ) := by
    ext z; simp [eq_comm]
  simp only [Pi.zero_apply]
  rw [this]
  exact Measure.pi_eval_preimage_null _ (μI_singleton a)

open Classical in
/-- `χ(X ∩ R) = Σ_{p ∈ X ∩ R} χ(p)` for a coloring `χ : X → {±1}` (we write `{±1} = ℤˣ`). -/
noncomputable def colorSum (X : Finset (ℝ × ℝ)) (χ : X → ℤˣ) (R : Set (ℝ × ℝ)) : ℤ :=
  ∑ p : X, if (p : ℝ × ℝ) ∈ R then ((χ p : ℤˣ) : ℤ) else 0

/-- The discrepancy of `X` w.r.t. closed axis-parallel rectangles `[a₁,b₁] × [a₂,b₂]`,
`min_χ max_R |χ(X ∩ R)|`. -/
noncomputable def rectDisc (X : Finset (ℝ × ℝ)) : ℕ :=
  ⨅ χ : X → ℤˣ, ⨆ ab : (ℝ × ℝ) × (ℝ × ℝ), (colorSum X χ (Set.Icc ab.1 ab.2)).natAbs

/-- `Δ₂(n)`: the largest discrepancy of an `n`-point set in the plane. -/
noncomputable def Δ₂ (n : ℕ) : ℕ :=
  ⨆ X : {X : Finset (ℝ × ℝ) // X.card = n}, rectDisc X.1

lemma units_abs (u : ℤˣ) : |(u : ℤ)| = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

lemma units_pm (u : ℤˣ) : (u : ℤ) = 1 ∨ (u : ℤ) = -1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

lemma abs_colorSum_le (X : Finset (ℝ × ℝ)) (χ : X → ℤˣ) (R : Set (ℝ × ℝ)) :
    |colorSum X χ R| ≤ X.card := by
  classical
  unfold colorSum
  calc |∑ p : X, (if (p : ℝ × ℝ) ∈ R then ((χ p : ℤˣ) : ℤ) else 0)|
      ≤ ∑ p : X, |if (p : ℝ × ℝ) ∈ R then ((χ p : ℤˣ) : ℤ) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : X, (1 : ℤ) := Finset.sum_le_sum fun p _ => by
        split_ifs <;> simp [units_abs]
    _ = X.card := by simp

lemma natAbs_colorSum_le (X : Finset (ℝ × ℝ)) (χ : X → ℤˣ) (R : Set (ℝ × ℝ)) :
    (colorSum X χ R).natAbs ≤ X.card := by
  have h : ((colorSum X χ R).natAbs : ℤ) ≤ X.card := by
    rw [Int.natCast_natAbs]; exact abs_colorSum_le X χ R
  exact_mod_cast h

lemma bdd_rect (X : Finset (ℝ × ℝ)) (χ : X → ℤˣ) :
    BddAbove (Set.range fun ab : (ℝ × ℝ) × (ℝ × ℝ) =>
      (colorSum X χ (Set.Icc ab.1 ab.2)).natAbs) :=
  ⟨X.card, by rintro _ ⟨ab, rfl⟩; exact natAbs_colorSum_le _ _ _⟩

lemma rectDisc_le_card (X : Finset (ℝ × ℝ)) : rectDisc X ≤ X.card := by
  unfold rectDisc
  exact (ciInf_le (OrderBot.bddBelow _) (fun _ => 1)).trans
    (ciSup_le fun ab => natAbs_colorSum_le _ _ _)

/-- If every coloring has a rectangle with `|χ(X ∩ R)| > k`, then `disc(X) > k`. -/
lemma lt_rectDisc {X : Finset (ℝ × ℝ)} {k : ℝ}
    (h : ∀ χ : X → ℤˣ, ∃ a b : ℝ × ℝ, k < |(colorSum X χ (Set.Icc a b) : ℝ)|) :
    k < rectDisc X := by
  unfold rectDisc
  obtain ⟨χ, hχ⟩ := ciInf_mem (fun χ : X → ℤˣ =>
    ⨆ ab : (ℝ × ℝ) × (ℝ × ℝ), (colorSum X χ (Set.Icc ab.1 ab.2)).natAbs)
  rw [← hχ]
  obtain ⟨a, b, hab⟩ := h χ
  have h1 : (colorSum X χ (Set.Icc a b)).natAbs ≤
      ⨆ ab : (ℝ × ℝ) × (ℝ × ℝ), (colorSum X χ (Set.Icc ab.1 ab.2)).natAbs :=
    le_ciSup (bdd_rect X χ) (a, b)
  have e : |(colorSum X χ (Set.Icc a b) : ℝ)| = ((colorSum X χ (Set.Icc a b)).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [e] at hab
  exact lt_of_lt_of_le hab (by exact_mod_cast h1)

lemma bdd_Δ₂ (n : ℕ) :
    BddAbove (Set.range fun X : {X : Finset (ℝ × ℝ) // X.card = n} => rectDisc X.1) :=
  ⟨n, by rintro _ ⟨Y, rfl⟩; exact (rectDisc_le_card Y.1).trans Y.2.le⟩

lemma rectDisc_le_Δ₂ {X : Finset (ℝ × ℝ)} {n : ℕ} (hX : X.card = n) : rectDisc X ≤ Δ₂ n :=
  le_ciSup (f := fun X : {X : Finset (ℝ × ℝ) // X.card = n} => rectDisc X.1) (bdd_Δ₂ n) ⟨X, hX⟩

/-- `Δ₂(n) ≤ n`. -/
lemma Δ₂_le (n : ℕ) : Δ₂ n ≤ n := by
  unfold Δ₂
  rcases isEmpty_or_nonempty {X : Finset (ℝ × ℝ) // X.card = n} with h | h
  · simp
  · exact ciSup_le fun X => (rectDisc_le_card X.1).trans X.2.le

/-! ### From colorings of the plane and anchored rectangles to colorings of `X` -/

/-- Extend a coloring of `X` to the plane (by `1` outside `X`). -/
noncomputable def extend (X : Finset (ℝ × ℝ)) (χ : X → ℤˣ) : ℝ × ℝ → ℤ := fun p =>
  if h : p ∈ X then ((χ ⟨p, h⟩ : ℤˣ) : ℤ) else 1

lemma extend_pm (X : Finset (ℝ × ℝ)) (χ : X → ℤˣ) :
    ∀ p ∈ X, extend X χ p = 1 ∨ extend X χ p = -1 := by
  intro p hp
  simp only [extend, hp, ↓reduceDIte]
  exact units_pm _

lemma sum_filter_extend (X : Finset (ℝ × ℝ)) (χ : X → ℤˣ) (q : ℝ × ℝ → Prop)
    [DecidablePred q] :
    ∑ p ∈ X.filter q, (extend X χ p : ℝ) = (colorSum X χ {p | q p} : ℝ) := by
  classical
  unfold colorSum
  push_cast
  rw [Finset.sum_filter, ← Finset.sum_coe_sort X]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hq : q p
  · simp [hq, extend]
  · simp [hq]

/-- The anchored rectangle `[0,x] × [0,y]`. -/
lemma Icc_zero_eq (x y : ℝ) :
    Set.Icc (0 : ℝ × ℝ) (x, y) = {p | 0 ≤ p.1 ∧ p.1 ≤ x ∧ 0 ≤ p.2 ∧ p.2 ≤ y} := by
  ext p
  simp only [Set.mem_Icc, Prod.le_def, Prod.fst_zero, Prod.snd_zero, Set.mem_ofPred_eq]
  tauto

/-! ### Theorem 1.1 -/

/-- A point set whose colorings of the plane all have a large anchored rectangle sum has
`Δ₂(n)` larger than that bound. -/
lemma lt_Δ₂_of {n : ℕ} {k : ℝ} (P : Finset (ℝ × ℝ)) (hP : P.card = n)
    (h : ∀ χ : ℝ × ℝ → ℤ, (∀ p ∈ P, χ p = 1 ∨ χ p = -1) →
      ∃ x y : ℝ, k <
        |∑ p ∈ P.filter (fun p => 0 ≤ p.1 ∧ p.1 ≤ x ∧ 0 ≤ p.2 ∧ p.2 ≤ y), (χ p : ℝ)|) :
    k < Δ₂ n := by
  refine lt_of_lt_of_le ?_ (Nat.cast_le.mpr (rectDisc_le_Δ₂ hP))
  apply lt_rectDisc
  intro χ
  obtain ⟨x, y, hxy⟩ := h (extend P χ) (extend_pm P χ)
  refine ⟨0, (x, y), ?_⟩
  rw [sum_filter_extend] at hxy
  rwa [Icc_zero_eq]

/-! ### Random points -/


/-- The law of one uniform point of `[0,1]²` is a probability measure. -/
instance : IsProbabilityMeasure ((volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1)) := by
  rw [unitSq_eq]; infer_instance

/-- Almost surely the `n` sample points are distinct. -/
lemma ties_null (n : ℕ) :
    Measure.pi (fun _ : Fin n => (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))
      {ω | ¬ Injective ω} = 0 := by
  rw [unitSq_eq]
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => μI) (fun _ => μI)
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  let N : Set (Fin n → ℝ) := ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {y | y i = y j}
  have hN : Measure.pi (fun _ : Fin n => μI) N = 0 :=
    measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => diag_null i j hij
  refine measure_mono_null (t := e ⁻¹' (Set.univ ×ˢ N)) ?_ ?_
  · intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    unfold Injective at hω
    push Not at hω
    obtain ⟨i, j, hij, hne⟩ := hω
    refine ⟨Set.mem_univ _, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j,
      Set.mem_iUnion.mpr ⟨hne, ?_⟩⟩⟩⟩
    show (ω i).2 = (ω j).2
    rw [hij]
  · rw [hmp.measure_preimage_equiv, Measure.prod_prod, hN, mul_zero]

/-- For distinct sample points, the sum over the point set `X = {ω t}` equals the sum over
the indices `t`. -/
lemma colorSum_image {n : ℕ} (ω : Fin n → ℝ × ℝ) (hω : Injective ω)
    (χ : ↥(univ.image ω) → ℤˣ) (q : ℝ × ℝ → Prop) [DecidablePred q] :
    (colorSum (univ.image ω) χ {p | q p} : ℝ) =
      ∑ t ∈ univ.filter (fun t => q (ω t)),
        (((χ ⟨ω t, mem_image_of_mem ω (mem_univ t)⟩ : ℤˣ) : ℤ) : ℝ) := by
  classical
  rw [← sum_filter_extend, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_image (fun a _ b _ h => hω h)]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hq : q (ω t)
  · simp [hq, extend, mem_image_of_mem ω (mem_univ t)]
  · simp [hq]

/-- Packaging: a bound on the (outer) probability of the index-form bad event gives a measurable
good event, on which the points are distinct and every coloring of the point set has a large
anchored rectangle. -/
theorem good_event_of_bad (n : ℕ) (b ε : ℝ) (hε : 0 ≤ ε)
    (hB : Measure.pi (fun _ : Fin n => (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))
      {X : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤ, (∀ t, χ t = 1 ∨ χ t = -1) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |∑ t ∈ Finset.univ.filter
          (fun t => 0 ≤ (X t).1 ∧ (X t).1 ≤ x ∧ 0 ≤ (X t).2 ∧ (X t).2 ≤ y), (χ t : ℝ)| ≤ b}
        ≤ ENNReal.ofReal ε) :
    ∃ G : Set (Fin n → ℝ × ℝ), MeasurableSet G ∧
      ENNReal.ofReal (1 - ε) ≤
        Measure.pi (fun _ : Fin n => (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1)) G ∧
      ∀ ω ∈ G, (Finset.univ.image ω).card = n ∧
        ∀ χ : ↥(Finset.univ.image ω) → ℤˣ,
          ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1,
            b < |(colorSum (Finset.univ.image ω) χ (Set.Icc 0 (x, y)) : ℝ)| := by
  classical
  set P := Measure.pi (fun _ : Fin n => (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))
  set B := {X : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤ, (∀ t, χ t = 1 ∨ χ t = -1) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |∑ t ∈ Finset.univ.filter
          (fun t => 0 ≤ (X t).1 ∧ (X t).1 ≤ x ∧ 0 ≤ (X t).2 ∧ (X t).2 ≤ y), (χ t : ℝ)| ≤ b}
    with hBdef
  set T := {ω : Fin n → ℝ × ℝ | ¬ Injective ω}
  set B' := toMeasurable P (B ∪ T)
  refine ⟨B'ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · have h1 : P B' ≤ ENNReal.ofReal ε := by
      rw [measure_toMeasurable]
      refine (measure_union_le _ _).trans ?_
      rw [ties_null, add_zero]
      exact hB
    rw [measure_compl (measurableSet_toMeasurable _ _) (measure_ne_top _ _), measure_univ,
      ENNReal.ofReal_sub _ hε, ENNReal.ofReal_one]
    exact tsub_le_tsub_left h1 1
  · intro ω hω
    have hω' : ω ∉ B ∪ T := fun h => hω (subset_toMeasurable _ _ h)
    simp only [Set.mem_union, not_or] at hω'
    obtain ⟨hnB, hnT⟩ := hω'
    have hinj : Injective ω := by
      by_contra h; exact hnT h
    refine ⟨by rw [Finset.card_image_of_injective _ hinj]; simp, fun χ => ?_⟩
    by_contra hcon
    push Not at hcon
    apply hnB
    refine ⟨fun t => ((χ ⟨ω t, mem_image_of_mem ω (mem_univ t)⟩ : ℤˣ) : ℤ),
      fun t => units_pm _, fun x hx y hy => ?_⟩
    have h := hcon x hx y hy
    rw [Icc_zero_eq, colorSum_image ω hinj χ] at h
    exact h

/-- The lowest point. If all points lie in `[0,1]²` and their `y`-coordinates are distinct
(which holds almost surely), then the lowest point `p` is the only point of `P` in
`[0, x(p)] × [0, y(p)]`, so every coloring has an anchored rectangle with `|χ(P ∩ R)| = 1`.
Hence for `b < 1` the bad event is a null set. -/
theorem bad_lowest (n : ℕ) (hn : 1 ≤ n) (b : ℝ) (hb : b < 1) :
    Measure.pi (fun _ : Fin n => (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))
      {X : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤ, (∀ t, χ t = 1 ∨ χ t = -1) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |∑ t ∈ univ.filter
          (fun t => 0 ≤ (X t).1 ∧ (X t).1 ≤ x ∧ 0 ≤ (X t).2 ∧ (X t).2 ≤ y), (χ t : ℝ)| ≤ b}
      = 0 := by
  classical
  rw [unitSq_eq]
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => μI) (fun _ => μI)
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  set Q := Measure.pi (fun _ : Fin n => μI)
  let N1 : Set (Fin n → ℝ) := ⋃ i, Function.eval i ⁻¹' (Set.Icc 0 1)ᶜ
  let N2 : Set (Fin n → ℝ) := (⋃ i, Function.eval i ⁻¹' (Set.Icc 0 1)ᶜ) ∪
    ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {y | y i = y j}
  have hN1 : Q N1 = 0 :=
    measure_iUnion_null fun i => Measure.pi_eval_preimage_null _ μI_compl_Icc
  have hN2 : Q N2 = 0 :=
    measure_union_null (measure_iUnion_null fun i => Measure.pi_eval_preimage_null _ μI_compl_Icc)
      (measure_iUnion_null fun i => measure_iUnion_null fun j =>
        measure_iUnion_null fun hij => diag_null i j hij)
  have hcover : {X : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤ, (∀ t, χ t = 1 ∨ χ t = -1) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |∑ t ∈ univ.filter
          (fun t => 0 ≤ (X t).1 ∧ (X t).1 ≤ x ∧ 0 ≤ (X t).2 ∧ (X t).2 ≤ y), (χ t : ℝ)| ≤ b}
      ⊆ e ⁻¹' (N1 ×ˢ Set.univ) ∪ e ⁻¹' (Set.univ ×ˢ N2) := by
    intro X hX
    obtain ⟨χ, hχ, hsmall⟩ := hX
    by_cases hx : ∀ i, (X i).1 ∈ Set.Icc (0 : ℝ) 1
    swap
    · left
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      exact ⟨Set.mem_iUnion.mpr ⟨i, hi⟩, Set.mem_univ _⟩
    by_cases hy : (∀ i, (X i).2 ∈ Set.Icc (0 : ℝ) 1) ∧ Injective (fun i => (X i).2)
    swap
    · right
      refine ⟨Set.mem_univ _, ?_⟩
      rw [not_and_or] at hy
      rcases hy with hy | hy
      · push Not at hy
        obtain ⟨i, hi⟩ := hy
        exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
      · unfold Injective at hy
        push Not at hy
        obtain ⟨i, j, hij, hne⟩ := hy
        refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j,
          Set.mem_iUnion.mpr ⟨hne, hij⟩⟩⟩)
    exfalso
    obtain ⟨hy0, hyinj⟩ := hy
    -- the lowest point `p = X t₀`
    obtain ⟨t₀, -, hmin⟩ := Finset.exists_min_image (univ : Finset (Fin n))
      (fun i => (X i).2) ⟨⟨0, hn⟩, mem_univ _⟩
    have hfilter : univ.filter (fun t => 0 ≤ (X t).1 ∧ (X t).1 ≤ (X t₀).1 ∧
        0 ≤ (X t).2 ∧ (X t).2 ≤ (X t₀).2) = {t₀} := by
      ext t
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨-, -, -, h4⟩
        exact hyinj (le_antisymm h4 (hmin t (mem_univ t)))
      · rintro rfl
        exact ⟨(hx t).1, le_rfl, (hy0 t).1, le_rfl⟩
    have h := hsmall (X t₀).1 (hx t₀) (X t₀).2 (hy0 t₀)
    rw [hfilter, Finset.sum_singleton] at h
    have h1 : |(χ t₀ : ℝ)| = 1 := by
      rcases hχ t₀ with h' | h' <;> simp [h']
    rw [h1] at h
    linarith
  refine measure_mono_null hcover (measure_union_null ?_ ?_)
  · rw [hmp.measure_preimage_equiv, Measure.prod_prod, hN1, zero_mul]
  · rw [hmp.measure_preimage_equiv, Measure.prod_prod, hN2, mul_zero]


/-- Law of independent uniform points in the unit square. -/
noncomputable abbrev unifPts (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin n => (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))

/-- Index-coloring interface: some signed coloring keeps every anchored count at most `b`. -/
def badSet (n : ℕ) (b : ℝ) : Set (Fin n → ℝ × ℝ) :=
  {X | ∃ χ : Fin n → ℤ, (∀ t, χ t = 1 ∨ χ t = -1) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |∑ t ∈ univ.filter
        (fun t => 0 ≤ (X t).1 ∧ (X t).1 ≤ x ∧ 0 ≤ (X t).2 ∧ (X t).2 ≤ y),
        (χ t : ℝ)| ≤ b}

/-- For thresholds below one, the index-coloring bad event has probability zero. -/
theorem badSet_measure_zero (n : ℕ) (hn : 1 ≤ n) (b : ℝ) (hb : b < 1) :
    unifPts n (badSet n b) = 0 := bad_lowest n hn b hb

/-- A measurable event with failure probability at most `ε`, on which all point-set
colorings have an anchored rectangle whose imbalance is strictly larger than `b`.
The failure probability is a parameter, unlike the fixed-exponent wrapper in v8. -/
def GoodEvent (n : ℕ) (b ε : ℝ) : Prop :=
  ∃ G : Set (Fin n → ℝ × ℝ), MeasurableSet G ∧
    ENNReal.ofReal (1 - ε) ≤ unifPts n G ∧
    ∀ ω ∈ G, (Finset.univ.image ω).card = n ∧
      ∀ χ : ↥(Finset.univ.image ω) → ℤˣ,
        ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1,
          b < |(colorSum (Finset.univ.image ω) χ (Set.Icc 0 (x, y)) : ℝ)|

/-- The index-coloring probability bound is the only hypothesis needed to package
an arbitrary failure probability as a measurable point-set event. -/
theorem goodEvent_of_bad (n : ℕ) (b ε : ℝ) (hε : 0 ≤ ε)
    (hB : unifPts n (badSet n b) ≤ ENNReal.ofReal ε) : GoodEvent n b ε :=
  good_event_of_bad n b ε hε hB

/-- A good event of positive probability yields a worst-case discrepancy lower bound. -/
theorem lt_Δ₂_of_goodEvent {n : ℕ} {b ε : ℝ} (hε : ε < 1)
    (h : GoodEvent n b ε) : b < Δ₂ n := by
  obtain ⟨G, -, hP, hG⟩ := h
  have hpos : 0 < unifPts n G := by
    refine lt_of_lt_of_le ?_ hP
    rw [ENNReal.ofReal_pos]
    linarith
  obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hpos.ne'
  obtain ⟨hcard, hχ⟩ := hG ω hω
  refine lt_of_lt_of_le ?_ (Nat.cast_le.mpr (rectDisc_le_Δ₂ hcard))
  apply lt_rectDisc
  intro χ
  obtain ⟨x, -, y, -, hxy⟩ := hχ χ
  exact ⟨0, (x, y), hxy⟩

end Riesz.PointSets
