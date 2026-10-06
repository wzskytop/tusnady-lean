import Oscillation

open MeasureTheory Riesz.PointSets
open scoped ENNReal BigOperators Classical

-- The full target is written out: the event contains all sample-dependent colorings.
example : ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ G : Set (Fin n → ℝ × ℝ), MeasurableSet G ∧
      ENNReal.ofReal (1 - Real.exp (-A*n)) ≤ unifPts n G ∧
      ∀ P ∈ G, (Finset.univ.image P).card = n ∧
        ∀ χ : ↥(Finset.univ.image P) → ℤˣ,
          ∃ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ Set.Icc (0:ℝ) 1,
            c * (Real.logb 2 n)^(3/2:ℝ) <
              |(colorSum (Finset.univ.image P) χ (Set.Icc 0 (x,y)) : ℝ)| :=
  Oscillation.paper_lower_bound

example : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    c * (Real.logb 2 n) ^ (3 / 2 : ℝ) < Riesz.PointSets.Δ₂ n :=
  Oscillation.planar_tusnady_lower_bound

-- The paper's exact simultaneous probability estimate, not an assumed interface.
example {n b h : ℕ} (hn : 0<n) (hb : 4≤b) (heven : Even b) (hh : 0<h)
    (hMn : b^(h-1) ≤ n) :
    (unifPts n).real (badSet n ((h:ℝ)*Real.sqrt ((n:ℝ)/(b^(h-1):ℕ))/(64*(b:ℝ)^(3/2:ℝ)))) ≤
      h*(48/(b:ℝ))^((n:ℝ)/2) + 2^n*Real.exp (-(h:ℝ)*(b^(h-1):ℕ)/(2048*(b:ℝ)^3)) :=
  Oscillation.R65.simultaneous_bound hn hb heven hh hMn

-- R65 good-transition events, with every integer base at least three.
example {n b h : ℕ} (hn : 0<n) (hb : 3≤b) (hh : 0<h)
    (hMn : b^(h-1)≤n) :
    (Oscillation.pointSampleLaw n).real
      (Oscillation.Direct.allGood (n:=n) b h (by omega))ᶜ ≤
      h*(48/(b:ℝ))^((n:ℝ)/2) :=
  Oscillation.R65.all_good_compl_bound hn hb hh hMn

example {n b h : ℕ} (hn : 0<n) (hb : 3≤b) (hMn : b^(h-1)≤n)
    {j : ℕ} (hj : j<h) :
    (Oscillation.pointSampleLaw n).real
      (Oscillation.Direct.paperGoodTransition (n:=n) b h (by omega) j)ᶜ ≤
      (48/(b:ℝ))^((n:ℝ)/2) :=
  Oscillation.R65.bad_transition_bound hn hb hMn hj

-- The centered sum itself, after fixing the vertical labels of the finite-probe model.
example {n b h : ℕ} (hn : 0 < n) (hb : 0 < b) (hh : 0 < h)
    (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1) (Y : Fin n → ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin n => μI)).real
      {U | Oscillation.centeredError (μ := Measure.pi (fun _ : Fin n => μI))
        (Oscillation.stageFiltration n b h hb) (Oscillation.stagePotential b h hb χ Y) h U ≤ -t} ≤
      Real.exp (-t^2*(b^(h-1):ℕ)^2/(2*h*n)) :=
  Oscillation.stage_centered_lower_tail hn hb hh χ hχ Y t ht

#print axioms Oscillation.paper_lower_bound
#print axioms Oscillation.planar_tusnady_lower_bound
#print axioms Oscillation.R65.simultaneous_bound
#print axioms Oscillation.R65.all_good_compl_bound
#print axioms Oscillation.R65.bad_transition_bound
#print axioms Oscillation.stage_centered_lower_tail

-- R65 Lemma 2.1 midpoint comparison. This is separately checked, not used by the all-n local-gain route.
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a z : ι) (haz : a≠z) (lo hi : ι → ℝ) (L U : ℝ)
    (hlo : ∀ i,L≤lo i) (hhi : ∀ i,hi i≤U) :
    (∑ i,(hi i-lo i))+2*|(hi z+lo z)/2-(hi a+lo a)/2| ≤ Fintype.card ι*(U-L) :=
  Oscillation.midpoint_range_comparison a z haz lo hi L U hlo hhi

example {Ω : Type*} [Fintype Ω] (μ : Riesz.Moments.FiniteLaw Ω)
    (X : Ω → ℝ) (v : ℝ) (hv : 0≤v)
    (hsecond : Riesz.Moments.expectation μ (fun x=>X x^2)=v)
    (hfourth : Riesz.Moments.expectation μ (fun x=>X x^4)≤3*v^2) :
    Real.sqrt (v/3)≤Riesz.Moments.expectation μ (fun x=>|X x|) :=
  Oscillation.abs_mean_of_fourth_three μ X v hv hsecond hfourth

#print axioms Oscillation.midpoint_range_comparison
#print axioms Oscillation.abs_mean_of_fourth_three
