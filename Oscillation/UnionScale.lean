import Oscillation.PaperGoodTransitions

namespace Oscillation.Direct
noncomputable section
open MeasureTheory Finset Riesz Riesz.PointSets Direct Oscillation.Parameters
open scoped ENNReal Classical

/-- For this route every transition is good; no Markov estimate is needed. -/
def allGood {n : ℕ} (b h : ℕ) (hb : 0 < b) : Set (Fin n → ℝ × ℝ) :=
  {P | ∀ j < h, P ∈ paperGoodTransition b h hb j}

lemma measurableSet_allGood {n : ℕ} (b h : ℕ) (hb : 0 < b) :
    MeasurableSet (allGood (n := n) b h hb) := by
  simp only [allGood, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter
    (fun _ => measurableSet_paperGoodTransition b h hb j))

theorem allGood_compl_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (hMn : b^(h-1) ≤ n) :
    (pointSampleLaw n).real (allGood (n := n) b h (by omega))ᶜ ≤
      h*(4*Real.sqrt (3/b))^n := by
  have hs : (allGood (n := n) b h (by omega))ᶜ ⊆
      ⋃ j : Fin h, (paperGoodTransition b h (by omega) j.val)ᶜ := by
    intro P hP
    change ¬(∀ j < h, P ∈ paperGoodTransition b h (by omega) j) at hP
    push Not at hP
    obtain ⟨j,hj,hbad⟩ := hP
    exact Set.mem_iUnion.mpr ⟨⟨j,hj⟩,hbad⟩
  calc
    _ ≤ (pointSampleLaw n).real (⋃ j : Fin h, (paperGoodTransition b h (by omega) j.val)ᶜ) :=
      measureReal_mono hs
    _ ≤ ∑ j : Fin h, (pointSampleLaw n).real (paperGoodTransition b h (by omega) j.val)ᶜ :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin h, (4*Real.sqrt (3/b))^n :=
      sum_le_sum (fun j _ => paper_bad_transition_bound hn hb hMn j.isLt)
    _ = _ := by simp

lemma allGood_subset_good {n b h : ℕ} (hn : 0 < n) (hb : 0 < b) :
    allGood (n := n) b h hb ⊆ good b h hb := by
  intro P hP
  have H := sum_le_sum (s:=range h) (fun j hj =>
    paperGoodTransition_mass hn hb (mem_range.mp hj) (hP j (mem_range.mp hj)))
  simp only [sum_const, card_range, nsmul_eq_mul] at H
  have hq : 0 ≤ massFloor n b (b^(h-1):ℕ) := by unfold massFloor; positivity
  change (h:ℝ)*massFloor n b (b^(h-1):ℕ)/2 ≤ _
  have : 0 ≤ (h:ℝ)*massFloor n b (b^(h-1):ℕ) := mul_nonneg (Nat.cast_nonneg _) hq
  linarith

theorem union_simultaneous_bound {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (heven : Even b) (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n (threshold n h b (b^(h-1):ℕ))) ≤
      h*(4*Real.sqrt (3/b))^n + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  rw [← pointSampleLaw_eq_unifPts]
  have hs : badSet n (threshold n h b (b^(h-1):ℕ)) ⊆
      (allGood (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ := by
    intro P hP
    by_cases hg : P ∈ allGood b h (by omega)
    · right
      rw [badSet_eq_iUnion_fixedColorBad] at hP
      obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp hP
      exact Set.mem_iUnion.mpr ⟨χ,hg,hχ⟩
    · exact Or.inl hg
  have hf (χ : Fin n → Bool) :
      (pointSampleLaw n).real (allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) ≤
        Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
    apply le_trans _ (good_fixed_bad_bound hn (by omega) heven hh χ)
    exact measureReal_mono (Set.inter_subset_inter_left _ (allGood_subset_good hn (by omega)))
  calc
    _ ≤ (pointSampleLaw n).real ((allGood (n := n) b h (by omega))ᶜ ∪ ⋃ χ : Fin n → Bool,
        allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) := measureReal_mono hs
    _ ≤ (pointSampleLaw n).real (allGood (n := n) b h (by omega))ᶜ +
        (pointSampleLaw n).real (⋃ χ : Fin n → Bool, allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) := measureReal_union_le _ _
    _ ≤ h*(4*Real.sqrt (3/b))^n +
        ∑ χ : Fin n → Bool, (pointSampleLaw n).real (allGood b h (by omega) ∩ fixedColorBad n (threshold n h b (b^(h-1):ℕ)) χ) :=
      add_le_add (allGood_compl_bound hn hb hMn) (measureReal_iUnion_fintype_le _)
    _ ≤ h*(4*Real.sqrt (3/b))^n +
        ∑ _χ : Fin n → Bool, Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) :=
      add_le_add_right (sum_le_sum (fun χ _ => hf χ)) _
    _ = _ := by simp

lemma stages_le_sample {n b h : ℕ} (hb : 2 ≤ b) (hh : 0 < h)
    (hMn : b^(h-1) ≤ n) : h ≤ n := by
  have H : h ≤ 2^(h-1) := by
    have := Nat.lt_two_pow_self (n:=h-1)
    omega
  exact H.trans ((Nat.pow_le_pow_left hb _).trans hMn)

/-- A polynomial factor h is absorbed without changing the paper's base conditions. -/
lemma absorb_all_stages {A : ℝ} {n h : ℕ} (hn : 0 < n) (hhn : h ≤ n) :
    ((h:ℝ)+1)*Real.exp (-(A+2)*n) ≤ Real.exp (-A*n) := by
  have hnR : (0:ℝ) ≤ n := by positivity
  have hhR : (h:ℝ) ≤ n := by exact_mod_cast hhn
  have H : (h:ℝ)+1 ≤ Real.exp (2*(n:ℝ)) := by
    have he := Real.add_one_le_exp (2*(n:ℝ))
    linarith
  calc
    _ ≤ Real.exp (2*(n:ℝ))*Real.exp (-(A+2)*n) := mul_le_mul_of_nonneg_right H (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Same numerical threshold and constants as the paper; h replaces the geometric prefactor 2. -/
theorem proposition_2_7 {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (heven : Even b) (hh : 0 < h) (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n ((h:ℝ)*Real.sqrt ((n:ℝ)/(b^(h-1):ℕ))/(64*(b:ℝ)^(3/2:ℝ)))) ≤
      h*(48/(b:ℝ))^((n:ℝ)/2) + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) := by
  have hbR : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have H := union_simultaneous_bound hn hb heven hh hMn
  rw [threshold_eq hn h hbR (by positivity),geometry_factor_eq hbR] at H
  exact H

theorem allGood_compl_bound_exact {n b h : ℕ} (hn : 0 < n) (hb : 4 ≤ b)
    (hMn : b^(h-1) ≤ n) :
    (pointSampleLaw n).real (allGood (n := n) b h (by omega))ᶜ ≤
      h*(48/(b:ℝ))^((n:ℝ)/2) := by
  have H := allGood_compl_bound hn hb hMn
  rw [geometry_factor_eq (by exact_mod_cast (show 0 < b by omega))] at H
  exact H

end
end Oscillation.Direct
