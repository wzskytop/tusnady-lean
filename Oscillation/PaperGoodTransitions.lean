import Oscillation.DirectScale

namespace Oscillation.Direct
noncomputable section
open MeasureTheory Finset Riesz Riesz.PointSets
open scoped ENNReal Classical

/-- At least half the points lie in nonheavy interior buckets, including equality. -/
def bucketGood {n M : ℕ} (b : ℝ) (x : Fin n → Option (Fin M)) : Prop :=
  2 * (univ.filter (fun i => x i ∈ exceptional (heavy b x))).card ≤ n

theorem bucket_bad_transition_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {n M : ℕ} (hn : 0 < n) (hM : 0 < M) (hMn : M ≤ n)
    {b : ℝ} (hb : 3 ≤ b) (cell : α → Option (Fin M))
    (hinterior : ∀ c, μ.real {z | cell z = some c} ≤ 1/M)
    (hboundary : μ.real {z | cell z = none} ≤ 2/b) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {P | ¬bucketGood b (fun i => cell (P i))} ≤
      (4 * Real.sqrt (3/b))^n := by
  have hb0 : 0 < b := by linarith
  let E (H : Finset (Fin M)) : Set (Fin n → α) :=
    {P | (H.card:ℝ) ≤ M/b ∧ n ≤ 2 * (univ.filter (fun i => cell (P i) ∈ exceptional H)).card}
  have hsub : {P | ¬bucketGood b (fun i => cell (P i))} ⊆ ⋃ H, E H := by
    intro P hP
    let x := fun i => cell (P i)
    refine Set.mem_iUnion.mpr ⟨heavy b x, heavy_card hn hM hb0 x, ?_⟩
    exact Nat.le_of_lt (Nat.lt_of_not_ge hP)
  have hE (H : Finset (Fin M)) : (Measure.pi (fun _ : Fin n => μ)).real (E H) ≤
      2^n * (Real.sqrt (3/b))^n := by
    by_cases hH : (H.card:ℝ) ≤ M/b
    · have he : E H = {P | n ≤ 2 * (univ.filter (fun i => P i ∈ {z | cell z ∈ exceptional H})).card} := by
        ext P; simp [E,hH]
      rw [he]
      exact half_sample_bound μ n _ (by positivity) ((div_le_one hb0).mpr hb)
        (exceptional_mass μ hM hb0 cell hinterior hboundary H hH)
    · have he : E H = ∅ := by ext P; simp [E,hH]
      rw [he, measureReal_empty]; positivity
  calc
    _ ≤ (Measure.pi (fun _ : Fin n => μ)).real (⋃ H, E H) := measureReal_mono hsub
    _ ≤ ∑ H, (Measure.pi (fun _ : Fin n => μ)).real (E H) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _H : Finset (Fin M), 2^n * (Real.sqrt (3/b))^n := sum_le_sum (fun H _ => hE H)
    _ = (2:ℝ)^M * (2^n * (Real.sqrt (3/b))^n) := by simp
    _ ≤ (2:ℝ)^n * (2^n * (Real.sqrt (3/b))^n) := by gcongr; norm_num
    _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring


/-- Paper event G_j, using the actual real sample's interior bucket labels. -/
def paperGoodTransition {n : ℕ} (b h : ℕ) (hb : 0 < b) (j : ℕ) :
    Set (Fin n → ℝ × ℝ) :=
  {P | bucketGood b (fun i => rectangularBucket (b^j) (b^(h-j-1)) b (b^j)
    (pow_pos hb _) (pow_pos hb _) hb (pow_pos hb _) (P i))}

lemma measurableSet_paperGoodTransition {n : ℕ} (b h : ℕ) (hb : 0 < b) (j : ℕ) :
    MeasurableSet (paperGoodTransition (n := n) b h hb j) := by
  let : MeasurableSpace (Option (Fin (b^j*b^(h-j-1)))) := ⊤
  let cell := rectangularBucket (b^j) (b^(h-j-1)) b (b^j)
    (pow_pos hb _) (pow_pos hb _) hb (pow_pos hb _)
  have hm : Measurable (fun P : Fin n → ℝ × ℝ => fun i => cell (P i)) :=
    Measurable.of_eval (fun i => (rectangularBucket_measurable _ _ _ _ _ _ _ _).comp
      (measurable_pi_apply i))
  exact hm ((Set.to_countable {x | bucketGood (b:ℝ) x}).measurableSet)

lemma paper_bad_transition_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (hMn : b^(h-1) ≤ n) {j : ℕ} (hj : j < h) :
    (pointSampleLaw n).real
      (paperGoodTransition (n := n) b h (by omega) j)ᶜ ≤
      (4*Real.sqrt (3/b))^n := by
  have hb0 : 0 < b := by omega
  let K := b^j
  let V := b^(h-j-1)
  let m := b^j
  have hK : 0 < K := pow_pos hb0 _
  have hV : 0 < V := pow_pos hb0 _
  have hm : 0 < m := pow_pos hb0 _
  have hdim : K*V = b^(h-1) := layer_comparison_size hj
  have hfine : V*(b*m) = b^h := layer_fine_size hj
  have H := bucket_bad_transition_bound (μI.prod μI) hn (Nat.mul_pos hK hV)
    (by simpa only [hdim] using hMn) (by exact_mod_cast (show 3 ≤ b by omega) : (3:ℝ) ≤ b)
    (rectangularBucket K V b m hK hV hb0 hm)
    (fun c => by
      have hc := rectangularBucket_good_mass K V b m hK hV hb0 hm c
      simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1/(K*V:ℕ))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hc)
    (by
      have hc := rectangularBucket_bad_mass K V b m hK hV hb hm
      simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2/(b:ℝ))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hc)
  exact H

/-- Paper event G: at least half the transitions satisfy G_j. -/
def paperGood {n : ℕ} (b h : ℕ) (hb : 0 < b) : Set (Fin n → ℝ × ℝ) :=
  {P | (h:ℝ)/2 ≤ ∑ j ∈ range h,
    (paperGoodTransition b h hb j).indicator (fun _ => (1:ℝ)) P}

/-- Counting bad transitions needs only marginal bounds, never independence. -/
theorem paper_bad_geometry_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (pointSampleLaw n).real (paperGood (n := n) b h (by omega))ᶜ ≤
      2 * (4*Real.sqrt (3/b))^n := by
  let μ := pointSampleLaw n
  let E := fun j => (paperGoodTransition (n := n) b h (by omega) j)ᶜ
  let B := fun P => ∑ j ∈ range h, (E j).indicator (fun _ => (1:ℝ)) P
  have hm (j : ℕ) : MeasurableSet (E j) :=
    (measurableSet_paperGoodTransition b h (by omega) j).compl
  have hi (j : ℕ) : Integrable ((E j).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const _).indicator (hm j)
  have hB : Integrable B μ := integrable_finsetSum _ (fun j _ => hi j)
  have hB0 (P) : 0 ≤ B P := sum_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => by norm_num) P)
  have hs : (paperGood (n:=n) b h (by omega))ᶜ ⊆ {P | (h:ℝ)/2 ≤ B P} := by
    intro P hP
    have he (j : ℕ) : (E j).indicator (fun _ => (1:ℝ)) P =
        1 - (paperGoodTransition b h (by omega) j).indicator (fun _ => (1:ℝ)) P := by
      by_cases hj : P ∈ paperGoodTransition b h (by omega) j <;> simp [E, hj]
    have hb : B P = h - ∑ j ∈ range h,
        (paperGoodTransition b h (by omega) j).indicator (fun _ => (1:ℝ)) P := by
      simp [B, he, sum_sub_distrib]
    change ¬ (h:ℝ)/2 ≤ _ at hP
    change (h:ℝ)/2 ≤ B P
    rw [hb]; linarith
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (μ:=μ) (Filter.Eventually.of_forall hB0) hB ((h:ℝ)/2)
  have hInt : (∫ P, B P ∂μ) ≤ h*(4*Real.sqrt (3/b))^n := by
    rw [show (∫ P, B P ∂μ) = ∑ j ∈ range h, ∫ P, (E j).indicator (fun _ => (1:ℝ)) P ∂μ from
      integral_finsetSum _ (fun j _ => hi j)]
    calc
      _ = ∑ j ∈ range h, μ.real (E j) := by
        apply sum_congr rfl
        intro j _
        exact integral_indicator_one (hm j)
      _ ≤ ∑ _j ∈ range h, (4*Real.sqrt (3/b))^n :=
        sum_le_sum (fun j hj => paper_bad_transition_bound hn hb hMn (mem_range.mp hj))
      _ = _ := by simp
  have hmono := measureReal_mono (μ:=μ) hs (measure_ne_top _ _)
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have H := mul_le_mul_of_nonneg_left hmono (show (0:ℝ) ≤ h/2 by positivity)
  change μ.real _ ≤ _
  nlinarith

/-- A good transition supplies the square-root mass used by the main proof. -/
lemma paperGoodTransition_mass {n b h : ℕ} (hn : 0 < n) (hb : 0 < b)
    {j : ℕ} (hj : j < h) {P : Fin n → ℝ × ℝ}
    (hP : P ∈ paperGoodTransition b h hb j) :
    massFloor n b (b^(h-1):ℕ) ≤ pointLayerMass b h hb j P := by
  let K := b^j
  let V := b^(h-j-1)
  let m := b^j
  have hdim : K*V = b^(h-1) := layer_comparison_size hj
  have hfine : V*(b*m) = b^h := layer_fine_size hj
  let cell := rectangularBucket K V b m (pow_pos hb _) (pow_pos hb _) hb (pow_pos hb _)
  have H := mass_gain hn (by dsimp [K,V]; positivity : 0 < K*V)
    (by exact_mod_cast hb : (0:ℝ) < b) (fun i => cell (P i)) hP
  change n/(2*Real.sqrt ((b:ℝ)*n/(K*V:ℕ))) ≤ bucketSquareRootSum cell P at H
  dsimp [cell] at H
  rw [bucketSquareRootSum_eq_interiorMass,hdim] at H
  simp_rw [sampleCells_eq_of_grid_eq hfine _ (pow_pos hb h)] at H
  exact H

/-- The paper's good event is stronger than the older aggregate-mass event. -/
theorem paperGood_subset_good {n b h : ℕ} (hn : 0 < n) (hb : 0 < b) :
    paperGood (n := n) b h hb ⊆ good b h hb := by
  intro P hP
  let q := massFloor n b (b^(h-1):ℕ)
  have hq : 0 ≤ q := by dsimp [q,massFloor]; positivity
  have hp (j) (hj : j ∈ range h) :
      q*(paperGoodTransition b h hb j).indicator (fun _ => (1:ℝ)) P ≤ pointLayerMass b h hb j P := by
    by_cases hg : P ∈ paperGoodTransition b h hb j
    · simpa [q,Set.indicator_of_mem hg] using paperGoodTransition_mass hn hb (mem_range.mp hj) hg
    · simpa [Set.indicator_of_notMem hg] using pointLayerMass_nonneg b h hb j P
  have H := sum_le_sum hp
  rw [← mul_sum] at H
  have hg := mul_le_mul_of_nonneg_left hP hq
  change (h:ℝ)*q/2 ≤ _
  nlinarith

/-- Exact form of the manuscript's geometric failure probability. -/
theorem paper_bad_geometry_bound_exact {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (pointSampleLaw n).real (paperGood (n := n) b h (by omega))ᶜ ≤
      2*(48/(b:ℝ))^((n:ℝ)/2) := by
  have H := paper_bad_geometry_bound hn hb hh hMn
  rw [geometry_factor_eq (by exact_mod_cast (show 0 < b by omega))] at H
  exact H

/-- The same fluctuation estimate holds on the paper's stronger good event. -/
lemma paper_good_fixed_bad_bound {n b h : ℕ} (hn : 0 < n) (hb : 0 < b) (heven : Even b)
    (hh : 0 < h) (χ : Fin n → Bool) :
    (pointSampleLaw n).real (paperGood (n := n) b h hb ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) ≤
      Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  apply le_trans _ (good_fixed_bad_bound hn hb heven hh χ)
  exact measureReal_mono (Set.inter_subset_inter_left _ (paperGood_subset_good hn hb))

theorem paper_simultaneous_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b) (heven : Even b)
    (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n (threshold n h b (b^(h-1):ℕ))) ≤
      2*(4*Real.sqrt (3/b))^n + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  rw [← pointSampleLaw_eq_unifPts]
  have hs : badSet n (threshold n h b (b^(h-1):ℕ)) ⊆
      (paperGood (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        paperGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ := by
    intro P hP
    by_cases hg : P ∈ paperGood b h (by omega)
    · right
      rw [badSet_eq_iUnion_fixedColorBad] at hP
      obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp hP
      exact Set.mem_iUnion.mpr ⟨χ,hg,hχ⟩
    · exact Or.inl hg
  calc
    _ ≤ (pointSampleLaw n).real ((paperGood (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        paperGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ (pointSampleLaw n).real (paperGood (n := n) b h (by omega))ᶜ +
        (pointSampleLaw n).real (⋃ χ : Fin n → Bool, paperGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) := measureReal_union_le _ _
    _ ≤ 2*(4*Real.sqrt (3/b))^n +
        ∑ χ : Fin n → Bool, (pointSampleLaw n).real (paperGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) :=
      add_le_add (paper_bad_geometry_bound hn hb hh hMn) (measureReal_iUnion_fintype_le _)
    _ ≤ 2*(4*Real.sqrt (3/b))^n +
        ∑ _χ : Fin n → Bool, Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) :=
      add_le_add_right (sum_le_sum (fun χ _ => paper_good_fixed_bad_bound hn (by omega) heven hh χ)) _
    _ = _ := by simp


/-- Current manuscript Proposition 2.4, equation (9); old name retained separately. -/
theorem proposition_2_4 {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b) (heven : Even b)
    (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n ((h:ℝ)*Real.sqrt ((n:ℝ)/(b^(h-1):ℕ))/(64*(b:ℝ)^(3/2:ℝ)))) ≤
      2*(48/(b:ℝ))^((n:ℝ)/2) + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  have hbR : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have H := paper_simultaneous_bound hn hb heven hh hMn
  rw [threshold_eq hn h hbR (by positivity),geometry_factor_eq hbR] at H
  exact H

end
end Oscillation.Direct
