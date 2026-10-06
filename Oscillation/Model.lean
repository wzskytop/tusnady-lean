import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! The genuine finite endpoint-counting model and its oscillation potential. -/

namespace Oscillation

noncomputable section
open Finset

def endpointWeight (p c : ℕ) : ℝ :=
  (if p < c then 1 else 0) + (if p = c then (1 / 2 : ℝ) else 0)

def endpointValue {n : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ)
    (c y : ℕ) : ℝ :=
  ∑ i, χ i * (if Y i < y then 1 else 0) * endpointWeight (p i) c

def gridMax {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, mem_univ _⟩ f

def gridOsc {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) : ℝ :=
  gridMax hm f + gridMax hm (fun t => -f t)

def blockValues {n m : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ)
    (c v : ℕ) (t : Fin m) : ℝ :=
  endpointValue χ p Y c (v * m + t.val + 1)

def gridPotential {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) : ℝ :=
  (∑ c : Fin K, ∑ v : Fin V, gridOsc hm (blockValues χ p Y c.val v.val)) /
    (K * V : ℕ)

def gridMaxPotential {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) : ℝ :=
  (∑ c : Fin K, ∑ v : Fin V, gridMax hm (blockValues χ p Y c.val v.val)) /
    (K * V : ℕ)

def refinedPositions {n b : ℕ} (p : Fin n → ℕ) (r : Fin n → Fin b) : Fin n → ℕ :=
  fun i => b * p i + (r i).val

lemma endpointWeight_nonneg (p c : ℕ) : 0 ≤ endpointWeight p c := by
  unfold endpointWeight
  split_ifs <;> norm_num

lemma endpointWeight_le_one (p c : ℕ) : endpointWeight p c ≤ 1 := by
  unfold endpointWeight
  split_ifs <;> norm_num at * <;> omega

lemma abs_endpointWeight_sub_le (p q c : ℕ) :
    |endpointWeight p c - endpointWeight q c| ≤ 1 := by
  have hp := endpointWeight_nonneg p c
  have hq := endpointWeight_nonneg p q
  have hp' := endpointWeight_le_one p c
  have hq' := endpointWeight_le_one q c
  have hq := endpointWeight_nonneg q c
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma le_gridMax {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) (t : Fin m) :
    f t ≤ gridMax hm f := by
  exact Finset.le_sup' (f := f) (mem_univ t)

lemma gridMax_le {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) {a : ℝ}
    (h : ∀ t, f t ≤ a) : gridMax hm f ≤ a := by
  exact (Finset.sup'_le_iff _ f).mpr (fun t _ => h t)

lemma gridMax_mono {m : ℕ} (hm : 0 < m) {f g : Fin m → ℝ}
    (h : ∀ t, f t ≤ g t) : gridMax hm f ≤ gridMax hm g := by
  exact gridMax_le hm f (fun t => (h t).trans (le_gridMax hm g t))

lemma gridMax_const {m : ℕ} (hm : 0 < m) (a : ℝ) :
    gridMax hm (fun _ => a) = a := by
  exact Finset.sup'_const _ a

lemma gridMax_congr {m : ℕ} (hm : 0 < m) {f g : Fin m → ℝ}
    (h : ∀ t, f t = g t) : gridMax hm f = gridMax hm g := by
  congr 1
  funext t
  exact h t

lemma gridMax_add_const {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) (a : ℝ) :
    gridMax hm (fun t => f t + a) = gridMax hm f + a := by
  apply le_antisymm
  · exact gridMax_le hm _ (fun t => by have := le_gridMax hm f t; linarith)
  · have h : gridMax hm f ≤ gridMax hm (fun t => f t + a) - a := by
      apply gridMax_le hm
      intro t
      have := le_gridMax hm (fun t => f t + a) t
      linarith
    linarith

lemma gridMax_exists {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) :
    ∃ t, gridMax hm f = f t := by
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_sup' ⟨⟨0, hm⟩, mem_univ _⟩ f
  exact ⟨t, ht⟩

lemma gridOsc_nonneg {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) :
    0 ≤ gridOsc hm f := by
  have h₁ := le_gridMax hm f ⟨0, hm⟩
  have h₂ := le_gridMax hm (fun t => -f t) ⟨0, hm⟩
  unfold gridOsc
  linarith

lemma gridOsc_add_const {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) (a : ℝ) :
    gridOsc hm (fun t => f t + a) = gridOsc hm f := by
  unfold gridOsc
  rw [gridMax_add_const]
  have hn : gridMax hm (fun t => -(f t + a)) = gridMax hm (fun t => -f t) - a := by
    calc
      _ = gridMax hm (fun t => -f t + -a) := gridMax_congr hm (by intro t; ring)
      _ = _ := by rw [gridMax_add_const]; ring
  rw [hn]
  ring

lemma gridOsc_le {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) {B : ℝ}
    (h : ∀ t, |f t| ≤ B) : gridOsc hm f ≤ 2 * B := by
  have h₁ := gridMax_le hm f (fun t => (abs_le.mp (h t)).2)
  have h₂ := gridMax_le hm (fun t => -f t) (fun t => neg_le.mpr (abs_le.mp (h t)).1)
  unfold gridOsc
  linarith

lemma gridOsc_singleton (f : Fin 1 → ℝ) : gridOsc (by decide) f = 0 := by
  have h : ∀ t : Fin 1, t = 0 := by intro t; exact Fin.eq_zero t
  have h₁ : gridMax (by decide) f = f 0 :=
    (gridMax_congr (by decide) (fun t => by rw [h t])).trans (gridMax_const _ _)
  have h₂ : gridMax (by decide) (fun t => -f t) = -f 0 :=
    (gridMax_congr (by decide) (fun t => by rw [h t])).trans (gridMax_const _ _)
  unfold gridOsc
  rw [h₁, h₂]
  ring

lemma gridPotential_nonneg {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) : 0 ≤ gridPotential K V m hm χ p Y := by
  apply div_nonneg
  · exact sum_nonneg fun c _ => sum_nonneg fun v _ => gridOsc_nonneg hm _
  · positivity

lemma gridPotential_one {n : ℕ} (K V : ℕ) (χ : Fin n → ℝ) (p Y : Fin n → ℕ) :
    gridPotential K V 1 (by decide) χ p Y = 0 := by
  simp only [gridPotential, gridOsc_singleton, sum_const_zero, zero_div]

lemma endpointValue_neg {n : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (c y : ℕ) :
    endpointValue (fun i => -χ i) p Y c y = -endpointValue χ p Y c y := by
  unfold endpointValue
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  ring

lemma gridPotential_eq_max_add_neg {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) :
    gridPotential K V m hm χ p Y = gridMaxPotential K V m hm χ p Y +
      gridMaxPotential K V m hm (fun i => -χ i) p Y := by
  have he : ∀ c v : ℕ, blockValues (fun i => -χ i) p Y c v =
      (fun t : Fin m => -blockValues χ p Y c v t) := by
    intro c v
    funext t
    exact endpointValue_neg χ p Y c _
  unfold gridPotential gridMaxPotential gridOsc
  simp_rw [he]
  rw [← add_div]
  congr 1
  simp only [sum_add_distrib]

lemma gridPotential_le_of_values {n K V m : ℕ} (hK : 0 < K) (hV : 0 < V)
    (hm : 0 < m) (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (B : ℝ)
    (h : ∀ (c : Fin K) (v : Fin V) (t : Fin m),
      |blockValues χ p Y c.val v.val t| ≤ B) :
    gridPotential K V m hm χ p Y ≤ 2 * B := by
  have hh : (∑ c : Fin K, ∑ v : Fin V,
      gridOsc hm (blockValues χ p Y c.val v.val)) ≤ (K * V : ℕ) * (2 * B) := by
    calc
      _ ≤ ∑ _c : Fin K, ∑ _v : Fin V, (2 * B) := by
        apply sum_le_sum
        intro c _
        exact sum_le_sum fun v _ => gridOsc_le hm _ (h c v)
      _ = _ := by simp; ring
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (K * V : ℕ))).mpr (by
    simpa [gridPotential, mul_comm] using hh)

end
end Oscillation
