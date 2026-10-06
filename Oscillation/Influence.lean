import Oscillation.Model
import Mathlib.Algebra.BigOperators.Fin

namespace Oscillation
noncomputable section
open Finset

lemma gridOsc_perturb {m : ℕ} (hm : 0 < m) (f g : Fin m → ℝ)
    (a b : ℝ) (h : ∀ t, a ≤ g t - f t ∧ g t - f t ≤ b) :
    |gridOsc hm g - gridOsc hm f| ≤ b - a := by
  have hg : gridMax hm g ≤ gridMax hm f + b := by
    apply gridMax_le hm
    intro t
    have := le_gridMax hm f t
    have := (h t).2
    linarith
  have hf : gridMax hm f ≤ gridMax hm g - a := by
    apply gridMax_le hm
    intro t
    have := le_gridMax hm g t
    have := (h t).1
    linarith
  have hng : gridMax hm (fun t => -g t) ≤ gridMax hm (fun t => -f t) - a := by
    apply gridMax_le hm
    intro t
    have := le_gridMax hm (fun t => -f t) t
    have := (h t).1
    linarith
  have hnf : gridMax hm (fun t => -f t) ≤ gridMax hm (fun t => -g t) + b := by
    apply gridMax_le hm
    intro t
    have := le_gridMax hm (fun t => -g t) t
    have := (h t).2
    linarith
  unfold gridOsc
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma gridOsc_step_perturb {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ)
    (e : ℝ) (Q : Fin m → Prop) [DecidablePred Q] :
    |gridOsc hm (fun t => f t + e * (if Q t then 1 else 0)) - gridOsc hm f| ≤ |e| := by
  by_cases he : 0 ≤ e
  · rw [abs_of_nonneg he]
    have h := gridOsc_perturb hm f
      (fun t => f t + e * (if Q t then 1 else 0)) 0 e (by
        intro t; split_ifs <;> constructor <;> linarith)
    simpa using h
  · rw [abs_of_nonpos (le_of_not_ge he)]
    have h := gridOsc_perturb hm f
      (fun t => f t + e * (if Q t then 1 else 0)) e 0 (by
        intro t; split_ifs <;> constructor <;> linarith)
    simpa using h

lemma sum_sub_single {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ) (i : ι)
    (h : ∀ k, k ≠ i → f k = g k) :
    (∑ k, f k) - (∑ k, g k) = f i - g i := by
  rw [← sum_sub_distrib]
  exact sum_eq_single i (fun k _ hki => by rw [h k hki]; ring) (by simp)

lemma endpointValue_update {n : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ)
    (i : Fin n) (z c y : ℕ) :
    endpointValue χ (Function.update p i z) Y c y = endpointValue χ p Y c y +
      (χ i * (endpointWeight z c - endpointWeight (p i) c)) *
        (if Y i < y then 1 else 0) := by
  have he := sum_sub_single
    (fun k => χ k * (if Y k < y then (1 : ℝ) else 0) *
      endpointWeight (Function.update p i z k) c)
    (fun k => χ k * (if Y k < y then (1 : ℝ) else 0) * endpointWeight (p k) c) i
    (by intro k hki; simp [Function.update_of_ne hki])
  simp only [Function.update_self] at he
  unfold endpointValue
  linarith [he]

lemma endpointWeight_refine {b : ℕ} (hb : 0 < b) (p c : ℕ) (r k : Fin b) :
    endpointWeight (b * p + r.val) (b * c + k.val) =
      if p < c then 1 else if p = c then endpointWeight r.val k.val else 0 := by
  by_cases hpc : p < c
  · have hlt : b * p + r.val < b * c + k.val := by
      have hm := Nat.mul_le_mul_left b hpc
      nlinarith [r.isLt]
    simp [endpointWeight, hpc, hlt, ne_of_lt hlt]
  · by_cases he : p = c
    · subst c
      simp [endpointWeight, Nat.add_lt_add_iff_left]
    · have hcp : c < p := by omega
      have hlt : b * c + k.val < b * p + r.val := by
        have hm := Nat.mul_le_mul_left b hcp
        nlinarith [k.isLt]
      simp [endpointWeight, hpc, he, not_lt.mpr (le_of_lt hlt), ne_of_gt hlt]

lemma sum_fin_mul {K b : ℕ} (f : ℕ → ℝ) :
    (∑ c : Fin (K * b), f c.val) = ∑ c : Fin K, ∑ k : Fin b, f (b * c.val + k.val) := by
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin K × Fin b ≃ Fin (K * b))]
  simp [Fintype.sum_prod_type, finProdFinEquiv, Nat.add_comm]

lemma gridOsc_step_outside {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ)
    (e : ℝ) (Y v : ℕ) (hv : v ≠ Y / m) :
    gridOsc hm (fun t => f t + e * (if Y < v * m + t.val + 1 then 1 else 0)) =
      gridOsc hm f := by
  by_cases hlt : v < Y / m
  · have hh : ∀ t : Fin m, ¬Y < v * m + t.val + 1 := by
      intro t
      have hdiv := Nat.div_mul_le_self Y m
      have hmul := Nat.mul_le_mul_right m hlt
      nlinarith [t.isLt]
    simpa only [hh, ite_false, mul_zero, add_zero]
  · have hgt : Y / m < v := by omega
    have hh : ∀ t : Fin m, Y < v * m + t.val + 1 := by
      intro t
      have hd := Nat.mod_lt Y hm
      have hdecomp := Nat.mod_add_div Y m
      have hmul := Nat.mul_le_mul_right m hgt
      nlinarith
    simpa only [hh, ite_true, mul_one] using gridOsc_add_const hm f e

lemma sum_gridOsc_step {m V : ℕ} (hm : 0 < m) (f : Fin V → Fin m → ℝ)
    (e : ℝ) (Y : ℕ) :
    |(∑ v : Fin V, gridOsc hm (fun t => f v t +
        e * (if Y < v.val * m + t.val + 1 then 1 else 0))) -
      ∑ v : Fin V, gridOsc hm (f v)| ≤ |e| := by
  by_cases hY : Y / m < V
  · let v₀ : Fin V := ⟨Y / m, hY⟩
    rw [sum_sub_single _ _ v₀ (by
      intro v hv
      apply gridOsc_step_outside hm
      intro he
      apply hv
      exact Fin.ext he)]
    exact gridOsc_step_perturb hm (f v₀) e _
  · have hh : ∀ v : Fin V, v.val ≠ Y / m := by
      intro v he
      have := v.isLt
      omega
    have he : ∀ v : Fin V, gridOsc hm (fun t => f v t +
        e * (if Y < v.val * m + t.val + 1 then 1 else 0)) = gridOsc hm (f v) :=
      fun v => gridOsc_step_outside hm (f v) e Y v.val (hh v)
    simp only [he, sub_self, abs_zero]
    exact abs_nonneg e

lemma sum_fin_indicator (K p : ℕ) (a : ℝ) :
    (∑ c : Fin K, if c.val = p then a else 0) = if p < K then a else 0 := by
  by_cases hp : p < K
  · let c₀ : Fin K := ⟨p, hp⟩
    have he : ∀ c : Fin K, c.val = p ↔ c = c₀ := by
      intro c
      change c.val = c₀.val ↔ c = c₀
      exact Fin.ext_iff.symm
    simp [he, hp]
  · have he : ∀ c : Fin K, c.val ≠ p := by
      intro c hc
      have := c.isLt
      omega
    simp [he, hp]

lemma sum_refined_weight_change_le {K b : ℕ} (hb : 0 < b) (p : ℕ)
    (r r' : Fin b) (a : ℝ) (ha : |a| ≤ 1) :
    (∑ c : Fin (K * b), |a * (endpointWeight (b * p + r'.val) c.val -
      endpointWeight (b * p + r.val) c.val)|) ≤ b := by
  rw [sum_fin_mul (fun c => |a * (endpointWeight (b * p + r'.val) c -
    endpointWeight (b * p + r.val) c)|)]
  calc
    _ ≤ ∑ c : Fin K, if c.val = p then (b : ℝ) else 0 := by
      apply sum_le_sum
      intro c _
      by_cases hcp : c.val = p
      · simp only [hcp, ite_true]
        calc
          _ ≤ ∑ _k : Fin b, (1 : ℝ) := by
            apply sum_le_sum
            intro k _
            rw [abs_mul]
            exact mul_le_one₀ ha (abs_nonneg _) (abs_endpointWeight_sub_le _ _ _)
          _ = _ := by simp
      · have hpc : p ≠ c.val := Ne.symm hcp
        simp [endpointWeight_refine hb, hpc, hcp]
    _ ≤ b := by
      rw [sum_fin_indicator]
      split_ifs <;> simp

lemma sum_blockOsc_update_le {n m V : ℕ} (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (i : Fin n) (z c : ℕ) :
    |(∑ v : Fin V, gridOsc hm (blockValues χ (Function.update p i z) Y c v.val)) -
      ∑ v : Fin V, gridOsc hm (blockValues χ p Y c v.val)| ≤
      |χ i * (endpointWeight z c - endpointWeight (p i) c)| := by
  have he : ∀ (v : Fin V) (t : Fin m),
      blockValues χ (Function.update p i z) Y c v.val t =
        blockValues χ p Y c v.val t +
          (χ i * (endpointWeight z c - endpointWeight (p i) c)) *
          (if Y i < v.val * m + t.val + 1 then 1 else 0) := by
    intro v t
    exact endpointValue_update χ p Y i z c _
  simp_rw [show ∀ v : Fin V, blockValues χ (Function.update p i z) Y c v.val =
      (fun t : Fin m => blockValues χ p Y c v.val t +
        (χ i * (endpointWeight z c - endpointWeight (p i) c)) *
          (if Y i < v.val * m + t.val + 1 then 1 else 0)) from
    fun v => funext (he v)]
  exact sum_gridOsc_step hm (fun v => blockValues χ p Y c v.val) _ (Y i)

/-- A genuine one-coordinate update of the next digit changes the actual
finite oscillation potential by at most one over the number of comparison
rectangles. No concentration or influence hypothesis is assumed. -/
theorem gridPotential_refined_influence {n K V m b : ℕ}
    (hK : 0 < K) (hV : 0 < V) (hm : 0 < m) (hb : 0 < b)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1) (p Y : Fin n → ℕ)
    (r : Fin n → Fin b) (i : Fin n) (r' : Fin b) :
    |gridPotential (K * b) V m hm χ (refinedPositions p (Function.update r i r')) Y -
      gridPotential (K * b) V m hm χ (refinedPositions p r) Y| ≤ 1 / (K * V : ℕ) := by
  have hu : refinedPositions p (Function.update r i r') =
      Function.update (refinedPositions p r) i (b * p i + r'.val) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [refinedPositions]
    · simp [refinedPositions, hki]
  rw [hu]
  let f : Fin (K * b) → ℝ := fun c =>
    ∑ v : Fin V, gridOsc hm
      (blockValues χ (Function.update (refinedPositions p r) i (b * p i + r'.val)) Y c.val v.val)
  let g : Fin (K * b) → ℝ := fun c =>
    ∑ v : Fin V, gridOsc hm (blockValues χ (refinedPositions p r) Y c.val v.val)
  have hn : |(∑ c, f c) - ∑ c, g c| ≤ b := by
    calc
      _ = |∑ c, (f c - g c)| := by rw [sum_sub_distrib]
      _ ≤ ∑ c, |f c - g c| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ c : Fin (K * b), |χ i * (endpointWeight (b * p i + r'.val) c.val -
          endpointWeight (b * p i + (r i).val) c.val)| := by
        apply sum_le_sum
        intro c _
        exact sum_blockOsc_update_le hm χ (refinedPositions p r) Y i _ c.val
      _ ≤ b := sum_refined_weight_change_le hb (p i) (r i) r' (χ i) (hχ i)
  change |(∑ c, f c) / ((K * b) * V : ℕ) - (∑ c, g c) / ((K * b) * V : ℕ)| ≤ _
  rw [← sub_div, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((K * b) * V : ℕ))]
  calc
    _ ≤ (b : ℝ) / ((K * b) * V : ℕ) := div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by
      have hb' : (b : ℝ) ≠ 0 := by positivity
      have hK' : (K : ℝ) ≠ 0 := by positivity
      have hV' : (V : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp

end
end Oscillation
