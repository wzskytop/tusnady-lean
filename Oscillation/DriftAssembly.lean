import Oscillation.AveragedComparison

/-! Summing the actual row gains gives the full oscillation drift. -/
namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 1000000

/-- Sum the row comparison and its actual fresh-digit gain over all children
of one parent rectangle. -/
theorem local_gridMax_gain {n d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (p Y : Fin n → ℕ) (c v : ℕ) :
    (∑ l : Fin (2 * d), gridMax hm (blockValues χ p Y c (v * (2 * d) + l.val))) +
      Real.sqrt (interiorCount (2 * d) m p Y c v) / 8 ≤
    finAvg (fun r : Fin n → Fin (2 * d) => ∑ k : Fin (2 * d),
      gridMax (Nat.mul_pos (by omega : 0 < 2 * d) hm)
        (blockValues χ (refinedPositions p r) Y (2 * d * c + k.val) v)) := by
  let y := representativeHeight (b := 2 * d) hm χ p Y c v
  let A := fun (r : Fin n → Fin (2 * d)) (k l : Fin (2 * d)) =>
    endpointValue χ (refinedPositions p r) Y (2 * d * c + k.val) (y l)
  have hrow (r : Fin n → Fin (2*d)) :
      (∑ l : Fin (2*d), finAvg (fun k => A r k l)) +
        |finAvg (fun k : Fin (2*d) =>
          rowDifference χ (refinedPositions p r) Y (2*d*c+k.val) y)| ≤
      ∑ k : Fin (2*d), gridMax (Nat.mul_pos (by omega : 0 < 2*d) hm)
        (blockValues χ (refinedPositions p r) Y (2*d*c+k.val) v) := by
    simp_rw [rowDifference_endpoints hd, finAvg_sub]
    exact sum_gridMax_averaged_end_comparison hd (Nat.mul_pos (by omega : 0 < 2*d) hm)
      (fun k => blockValues χ (refinedPositions p r) Y (2*d*c+k.val) v)
      (representativeProbe (b := 2*d) hm χ p Y c v)
  have hbase (l : Fin (2*d)) :
      finAvg (fun r : Fin n → Fin (2*d) => finAvg (fun k => A r k l)) =
      gridMax hm (blockValues χ p Y c (v*(2*d)+l.val)) := by
    exact (averaged_endpoint_baseline d hd χ p Y c (y l)).trans
      (representativeHeight_value hm χ p Y c v l)
  have hs := finAvg_mono hrow
  simp only [finAvg_add, finAvg_sum, hbase] at hs
  have hgain := averaged_child_difference_gain hd hm χ hχ p Y c v
  rw [finAvg_sum]
  exact (add_le_add le_rfl hgain).trans hs

lemma gridMax_numerator_split_old {n : ℕ} (K V b m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) :
    (∑ c : Fin K, ∑ w : Fin (V * b), gridMax hm (blockValues χ p Y c.val w.val)) =
      ∑ c : Fin K, ∑ v : Fin V, ∑ l : Fin b,
        gridMax hm (blockValues χ p Y c.val (v.val * b + l.val)) := by
  apply sum_congr rfl
  intro c _
  simpa only [Nat.mul_comm] using
    (sum_fin_mul (K := V) (b := b) (fun w => gridMax hm (blockValues χ p Y c.val w)))

lemma gridMax_numerator_split_new {n : ℕ} (K V b m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) :
    (∑ w : Fin (K * b), ∑ v : Fin V, gridMax hm (blockValues χ p Y w.val v.val)) =
      ∑ c : Fin K, ∑ v : Fin V, ∑ k : Fin b,
        gridMax hm (blockValues χ p Y (b * c.val + k.val) v.val) := by
  rw [sum_fin_mul (fun w => ∑ v : Fin V, gridMax hm (blockValues χ p Y w v.val))]
  apply sum_congr rfl
  intro c _
  exact sum_comm

/-- The maxima alone gain one eighth of the interior square-root count,
divided by the total number of grid blocks. -/
theorem gridMaxPotential_gain {n K V d m : ℕ} (hK : 0 < K) (hV : 0 < V)
    (hd : 0 < d) (hm : 0 < m) (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1)
    (p Y : Fin n → ℕ) :
    gridMaxPotential K (V * (2 * d)) m hm χ p Y +
      interiorMass K V (2 * d) m p Y / (8 * (2 * d : ℕ) * (K * V : ℕ)) ≤
      finAvg (fun r : Fin n → Fin (2 * d) =>
        gridMaxPotential (K * (2 * d)) V ((2 * d) * m)
          (Nat.mul_pos (by omega : 0 < 2 * d) hm) χ (refinedPositions p r) Y) := by
  have hs := sum_le_sum (s := (univ : Finset (Fin K))) (fun c _ =>
    sum_le_sum (s := (univ : Finset (Fin V))) (fun v _ =>
      local_gridMax_gain hd hm χ hχ p Y c.val v.val))
  simp only [sum_add_distrib, ← sum_div] at hs
  have hn : (∑ c : Fin K, ∑ w : Fin (V * (2 * d)),
      gridMax hm (blockValues χ p Y c.val w.val)) + interiorMass K V (2 * d) m p Y / 8 ≤
      finAvg (fun r : Fin n → Fin (2 * d) =>
        ∑ w : Fin (K * (2 * d)), ∑ v : Fin V,
          gridMax (Nat.mul_pos (by omega : 0 < 2 * d) hm)
            (blockValues χ (refinedPositions p r) Y w.val v.val)) := by
    rw [gridMax_numerator_split_old]
    simp_rw [gridMax_numerator_split_new, finAvg_sum]
    simpa only [finAvg_sum, interiorMass] using hs
  have hden : K * (V * (2 * d)) = K * (2 * d) * V := by ring
  unfold gridMaxPotential
  rw [hden, finAvg_div_const]
  have hh := div_le_div_of_nonneg_right hn
    (by positivity : (0 : ℝ) ≤ (K * (2 * d) * V : ℕ))
  rw [add_div] at hh
  have he : interiorMass K V (2 * d) m p Y / 8 / (K * (2 * d) * V : ℕ) =
      interiorMass K V (2 * d) m p Y / (8 * (2 * d : ℕ) * (K * V : ℕ)) := by
    push_cast
    ring
  rw [he] at hh
  exact hh

/-- The actual oscillation potential has the paper's drift. This theorem
discharges both the representative comparison and its random gain. -/
theorem gridPotential_drift {n K V d m : ℕ} (hK : 0 < K) (hV : 0 < V)
    (hd : 0 < d) (hm : 0 < m) (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1)
    (p Y : Fin n → ℕ) :
    interiorMass K V (2 * d) m p Y / (4 * (2 * d : ℕ) * (K * V : ℕ)) ≤
      finAvg (fun r : Fin n → Fin (2 * d) =>
        gridPotential (K * (2 * d)) V ((2 * d) * m)
          (Nat.mul_pos (by omega : 0 < 2 * d) hm) χ (refinedPositions p r) Y) -
      gridPotential K (V * (2 * d)) m hm χ p Y := by
  have hpos := gridMaxPotential_gain hK hV hd hm χ hχ p Y
  have hneg := gridMaxPotential_gain hK hV hd hm (fun i => -χ i)
    (by intro i; simpa only [abs_neg] using hχ i) p Y
  simp_rw [gridPotential_eq_max_add_neg, finAvg_add]
  have he : interiorMass K V (2 * d) m p Y / (4 * (2 * d : ℕ) * (K * V : ℕ)) =
      interiorMass K V (2 * d) m p Y / (8 * (2 * d : ℕ) * (K * V : ℕ)) +
      interiorMass K V (2 * d) m p Y / (8 * (2 * d : ℕ) * (K * V : ℕ)) := by ring
  rw [he]
  linarith

/-- The drift in a form that accepts any positive even branching factor. -/
theorem gridPotential_drift_even {n K V b m : ℕ} (hK : 0 < K) (hV : 0 < V)
    (hb : 0 < b) (heven : Even b) (hm : 0 < m)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| = 1) (p Y : Fin n → ℕ) :
    interiorMass K V b m p Y / (4 * (b : ℝ) * (K * V : ℕ)) ≤
      finAvg (fun r : Fin n → Fin b =>
        gridPotential (K * b) V (b * m) (Nat.mul_pos hb hm) χ (refinedPositions p r) Y) -
      gridPotential K (V * b) m hm χ p Y := by
  obtain ⟨d, rfl⟩ := heven
  have hd : 0 < d := by omega
  revert hb
  rw [show d + d = 2 * d by omega]
  intro hb
  exact gridPotential_drift hK hV hd hm χ hχ p Y

end
end Oscillation
