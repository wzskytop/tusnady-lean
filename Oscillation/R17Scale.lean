import Oscillation.StageCrowding

namespace Oscillation.Direct
noncomputable section
open MeasureTheory Finset Riesz Riesz.PointSets
open scoped ENNReal Classical

lemma crowding_factor_eq {n : ℕ} {b : ℝ} (hb : 0<b) :
    (2:ℝ)^n*Real.exp (-Real.log (b/4)*n/2) = (16/b)^((n:ℝ)/2) := by
  rw [Real.rpow_def_of_pos (by positivity)]
  have h2 : (2:ℝ)^n = Real.exp (n*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [h2, ← Real.exp_add, Real.log_div (by norm_num) hb.ne',
    Real.log_div hb.ne' (by norm_num)]
  have h16 : Real.log 16=4*Real.log 2 := by
    rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]
    norm_num
  have h4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [h16,h4]
  congr 1
  ring

lemma r17_crowding_bound {n b h : ℕ} (hn : 0<n) (hb : 4<b)
    (hh : 0<h) (hMn : b^(h-1)≤n) :
    (pointSampleLaw n).real {P | (∑j∈range h,pointLayerMass b h (by omega) j P) ≤
      h*massFloor n b (b^(h-1):ℕ)} ≤ (16/(b:ℝ))^((n:ℝ)/2) := by
  have H := crowding_bound hn hb hh hMn
  rw [crowding_factor_eq (by positivity)] at H
  exact H

/-- The geometric lemma needs no parity assumption, including the trivial small bases. -/
theorem r17_crowding_bound_all {n b h : ℕ} (hn : 0<n) (hb : 3≤b)
    (hh : 0<h) (hMn : b^(h-1)≤n) :
    (pointSampleLaw n).real {P | (∑j∈range h,pointLayerMass b h (by omega) j P) ≤
      h*massFloor n b (b^(h-1):ℕ)} ≤ (16/(b:ℝ))^((n:ℝ)/2) := by
  by_cases hb4 : 4<b
  · exact r17_crowding_bound hn hb4 hh hMn
  · have hbR : (0:ℝ)<b := by positivity
    have hb16 : (b:ℝ)≤16 := by exact_mod_cast (show b≤16 by omega)
    have hbase : (1:ℝ)≤16/b := (le_div_iff₀ hbR).mpr (by simpa using hb16)
    exact (measureReal_le_one).trans (Real.one_le_rpow hbase (by positivity))

lemma r17_bad_geometry_bound {n b h : ℕ} (hn : 0<n) (hb : 4<b)
    (hh : 0<h) (hMn : b^(h-1)≤n) :
    (pointSampleLaw n).real (good (n:=n) b h (by omega))ᶜ ≤ (16/(b:ℝ))^((n:ℝ)/2) := by
  apply le_trans _ (r17_crowding_bound hn hb hh hMn)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro P hP
  have H : (∑j∈range h,pointLayerMass b h (by omega) j P)<h*massFloor n b (b^(h-1):ℕ)/2 := lt_of_not_ge hP
  have hp : 0≤(h:ℝ)*massFloor n b (b^(h-1):ℕ) := by unfold massFloor; positivity
  change (∑j∈range h,pointLayerMass b h (by omega) j P) ≤ h*massFloor n b (b^(h-1):ℕ)
  linarith

theorem r17_simultaneous_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 < b) (heven : Even b)
    (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n (threshold n h b (b^(h-1):ℕ))) ≤
      (16/(b:ℝ))^((n:ℝ)/2) + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  rw [← pointSampleLaw_eq_unifPts]
  have hs : badSet n (threshold n h b (b^(h-1):ℕ)) ⊆
      (good (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        good b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ := by
    intro P hP
    by_cases hg : P ∈ good b h (by omega)
    · right
      rw [badSet_eq_iUnion_fixedColorBad] at hP
      obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp hP
      exact Set.mem_iUnion.mpr ⟨χ,hg,hχ⟩
    · exact Or.inl hg
  calc
    _ ≤ (pointSampleLaw n).real ((good (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        good b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ (pointSampleLaw n).real (good (n := n) b h (by omega))ᶜ +
        (pointSampleLaw n).real (⋃ χ : Fin n → Bool, good b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) := measureReal_union_le _ _
    _ ≤ (16/(b:ℝ))^((n:ℝ)/2) +
        ∑ χ : Fin n → Bool, (pointSampleLaw n).real (good b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) :=
      add_le_add (r17_bad_geometry_bound hn hb hh hMn) (measureReal_iUnion_fintype_le _)
    _ ≤ (16/(b:ℝ))^((n:ℝ)/2) +
        ∑ _χ : Fin n → Bool, Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) :=
      add_le_add_right (sum_le_sum (fun χ _ => good_fixed_bad_bound hn (by omega) heven hh χ)) _
    _ = _ := by simp

theorem r17_proposition_2_7 {n b h : ℕ} (hn : 0<n) (hb : 4<b)
    (heven : Even b) (hh : 0<h) (hMn : b^(h-1)≤n) :
    (unifPts n).real (badSet n ((h:ℝ)*Real.sqrt ((n:ℝ)/(b^(h-1):ℕ))/(64*(b:ℝ)^(3/2:ℝ)))) ≤
      (16/(b:ℝ))^((n:ℝ)/2)+2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  have H := r17_simultaneous_bound hn hb heven hh hMn
  rw [threshold_eq hn h (by positivity) (by positivity)] at H
  exact H

end
end Oscillation.Direct
