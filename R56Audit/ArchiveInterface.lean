import Oscillation
import R56Audit.SupNorm

/-!
# Bridges between `F_χ`, `‖F_χ‖∞` and the archive's point-set interface

Auditor's supplement (not part of the audited archive).

The archive states its results with the point-set interface of `Riesz.PointSets` and
`Riesz.Colorings`: the event `badSet`, the packaged event `GoodEvent`, the signed counts
`colorSum` of a coloring of the point set, and the worst-case discrepancy `Δ₂`. This file
relates these objects to the manuscript's `F_χ` and `‖F_χ‖∞` of `R56Audit.Notation`. Nothing
is proved here about the lower bound itself.

* `exists_pointColoring`: on a sample of distinct points, a coloring `χ ∈ {±1}ⁿ` of the
  indices is a coloring of the point set, and `colorSum` on anchored rectangles is `F_χ`.
* `goodEvent_supNorm`: from the archive's `GoodEvent` to index colorings and `‖F_χ‖∞`.
* `lt_Δ₂_of_supNorm`: "Anchored rectangles are a subfamily of all rectangles", so a lower
  bound for `‖F_χ‖∞` over all colorings of `n` distinct points is a lower bound for `Δ₂(n)`.
* `supNorm_le_eq_fixedColorBad`, `exists_supNorm_le_eq_badSet`: the events `{‖F_χ‖∞ ≤ B}` and
  `{∃ χ, ‖F_χ‖∞ ≤ B}` are the archive's `fixedColorBad` and `badSet`.

The manuscript route (`Simultaneous.lean`, `Parameters.lean`) uses this file only for
Corollary 1.2, through `lt_Δ₂_of_supNorm`, because `Δ₂` is the archive's definition. All
other statements are used by the archive-route modules `ArchiveRoute.lean` and `AllBases.lean`
only.
-/

namespace R56Audit

open Riesz Riesz.PointSets

noncomputable section

variable {n : ℕ}

/-! ### Colorings: `{±1}ⁿ` as `Fin n → ℤˣ`, as `Fin n → Bool`, and as colorings of the point set -/

/-- The Boolean encoding of a coloring used by the archive's union bound. -/
def colorBool (χ : Fin n → ℤˣ) : Fin n → Bool := fun i => decide (χ i = 1)

/-- The archive's sign of the Boolean encoding of `χ` is `χ`. -/
lemma boolSign_colorBool (χ : Fin n → ℤˣ) (i : Fin n) :
    PointSets.boolSign (colorBool χ i) = ((χ i : ℤˣ) : ℤ) := by
  rcases Int.units_eq_one_or (χ i) with h | h <;> simp [colorBool, PointSets.boolSign, h]

/-- Every Boolean coloring is the encoding of a coloring `χ ∈ {±1}ⁿ`. -/
lemma colorBool_surjective : Function.Surjective (colorBool (n := n)) := by
  intro c
  refine ⟨fun i => if c i then 1 else -1, ?_⟩
  funext i
  cases hc : c i <;> simp [colorBool, hc]

/-- On a sample of distinct points, a coloring `χ ∈ {±1}ⁿ` of the indices is a coloring of
the point set, and the anchored sums of the point set are `F_χ`. -/
lemma exists_pointColoring (P : Fin n → ℝ × ℝ) (hP : Function.Injective P)
    (χ : Fin n → ℤˣ) :
    ∃ χ' : ↥(Finset.univ.image P) → ℤˣ,
      ∀ x y : ℝ, (colorSum (Finset.univ.image P) χ' (Set.Icc 0 (x, y)) : ℝ) = F χ P x y := by
  classical
  have hmem : ∀ p : ↥(Finset.univ.image P), ∃ t, P t = p := fun p => by
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp p.2
    exact ⟨t, ht⟩
  refine ⟨fun p => χ (hmem p).choose, fun x y => ?_⟩
  have hkey : ∀ t,
      (hmem ⟨P t, Finset.mem_image_of_mem P (Finset.mem_univ t)⟩).choose = t := fun t =>
    hP (hmem ⟨P t, Finset.mem_image_of_mem P (Finset.mem_univ t)⟩).choose_spec
  have h := colorSum_image P hP (fun p => χ (hmem p).choose)
    (fun p => 0 ≤ p.1 ∧ p.1 ≤ x ∧ 0 ≤ p.2 ∧ p.2 ≤ y)
  rw [Icc_zero_eq, h, F_eq_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hkey t]

/-- From the event of `Riesz.PointSets.GoodEvent` (colorings of the point set, an explicit
rectangle) to index colorings `χ ∈ {±1}ⁿ` and the supremum norm of `F_χ`. -/
lemma goodEvent_supNorm {b ε : ℝ} (h : GoodEvent n b ε) :
    ∃ G : Set (Fin n → ℝ × ℝ), MeasurableSet G ∧ ENNReal.ofReal (1 - ε) ≤ unifPts n G ∧
      ∀ P ∈ G, Function.Injective P ∧ ∀ χ : Fin n → ℤˣ, b < supNorm χ P := by
  obtain ⟨G, hG, hmeas, hgood⟩ := h
  refine ⟨G, hG, hmeas, fun P hP => ?_⟩
  obtain ⟨hcard, hχ⟩ := hgood P hP
  have hinj : Function.Injective P := by
    have hc' : (Finset.univ.image P).card = (Finset.univ : Finset (Fin n)).card := by
      rw [hcard]; simp
    have := Finset.card_image_iff.mp hc'
    intro i j hij
    exact this (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij
  refine ⟨hinj, fun χ => ?_⟩
  obtain ⟨χ', hχ'⟩ := exists_pointColoring P hinj χ
  obtain ⟨x, hx, y, hy, hxy⟩ := hχ χ'
  rw [hχ' x y] at hxy
  exact lt_of_lt_of_le hxy (le_supNorm χ P hx hy)

/-- "Anchored rectangles are a subfamily of all rectangles": if `n` distinct points have
`‖F_χ‖∞ > t` for every coloring `χ ∈ {±1}ⁿ`, then their discrepancy, and hence `Δ₂(n)`, is
greater than `t`. -/
theorem lt_Δ₂_of_supNorm {t : ℝ} (P : Fin n → ℝ × ℝ) (hP : Function.Injective P)
    (h : ∀ χ : Fin n → ℤˣ, t < supNorm χ P) : t < Δ₂ n := by
  classical
  have hcard : (Finset.univ.image P).card = n := by
    rw [Finset.card_image_of_injective _ hP]
    simp
  refine lt_of_lt_of_le ?_ (Nat.cast_le.mpr (rectDisc_le_Δ₂ hcard))
  apply lt_rectDisc
  intro χ'
  have hF : ∀ x y : ℝ, (colorSum (Finset.univ.image P) χ' (Set.Icc 0 (x, y)) : ℝ) =
      F (fun i => χ' ⟨P i, Finset.mem_image_of_mem P (Finset.mem_univ i)⟩) P x y := by
    intro x y
    rw [Icc_zero_eq, colorSum_image P hP χ'
      (fun p => 0 ≤ p.1 ∧ p.1 ≤ x ∧ 0 ≤ p.2 ∧ p.2 ≤ y), F_eq_filter]
  have : Nonempty (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) :=
    ⟨(⟨0, by simp⟩, ⟨0, by simp⟩)⟩
  obtain ⟨z, hz⟩ := exists_lt_of_lt_ciSup
    (h fun i => χ' ⟨P i, Finset.mem_image_of_mem P (Finset.mem_univ i)⟩)
  exact ⟨0, ((z.1 : ℝ), (z.2 : ℝ)), by rw [hF]; exact hz⟩

/-- The event `{‖F_χ‖∞ ≤ B}` is the archive's fixed-coloring bad event. -/
lemma supNorm_le_eq_fixedColorBad (χ : Fin n → ℤˣ) (B : ℝ) :
    {P : Fin n → ℝ × ℝ | supNorm χ P ≤ B} = fixedColorBad n B (colorBool χ) := by
  ext P
  simp only [Set.mem_ofPred_eq, supNorm_le_iff, fixedColorBad]
  constructor
  · intro h x hx y hy
    have := h x hx y hy
    rw [F_eq_filter] at this
    simpa only [boolSign_colorBool] using this
  · intro h x hx y hy
    rw [F_eq_filter]
    have := h x hx y hy
    simpa only [boolSign_colorBool] using this

/-- The event of Proposition 2.7, that some `χ ∈ {±1}ⁿ` has `‖F_χ‖∞ ≤ B`, is exactly the
archive's `badSet n B`. -/
theorem exists_supNorm_le_eq_badSet (n : ℕ) (B : ℝ) :
    {P : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ B} = badSet n B := by
  rw [badSet_eq_iUnion_fixedColorBad]
  ext P
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨χ, hχ⟩
    refine ⟨colorBool χ, ?_⟩
    rw [← supNorm_le_eq_fixedColorBad]
    exact hχ
  · rintro ⟨c, hc⟩
    obtain ⟨χ, rfl⟩ := colorBool_surjective c
    refine ⟨χ, ?_⟩
    rw [← supNorm_le_eq_fixedColorBad] at hc
    exact hc

end

end R56Audit
