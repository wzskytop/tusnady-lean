import R56Audit

open MeasureTheory ProbabilityTheory

/- Independent checks written for the supplied r65 audit package.
The principal statement uses no project-defined measure, discrepancy, or event. -/
example :
    ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (1 - Real.exp (-A * n)) ≤
        (MeasureTheory.Measure.pi fun _ : Fin n =>
          (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))
        {P : Fin n → ℝ × ℝ | ∀ χ : Fin n → ℤˣ,
          ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1,
            c * Real.logb 2 (n : ℝ) ^ (3 / 2 : ℝ) ≤
              |∑ i : Fin n, if 0 ≤ (P i).1 ∧ (P i).1 ≤ x ∧ 0 ≤ (P i).2 ∧ (P i).2 ≤ y
                then (((χ i : ℤˣ) : ℤ) : ℝ) else 0|} :=
  R56Audit.theorem_1_1_unfolded

-- The exact numerical proposition works for every integer base >= 3, including odd bases.
example {n b h : ℕ} (hb : 3 ≤ b) (hh : 1 ≤ h) (hmn : b ^ (h - 1) ≤ n) :
    (Riesz.PointSets.unifPts n).real {P | ∃ χ : Fin n → ℤˣ,
      R56Audit.supNorm χ P ≤ (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) *
        Real.sqrt (n / (b : ℝ) ^ (h - 1))} ≤
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
        2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) :=
  R56Audit.proposition_2_7 hb hh hmn

-- The potential takes suprema and infima over the full vertical intervals.
example {n : ℕ} (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (b h j : ℕ) :
    R56Audit.Zpot χ b h j P =
      (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h-j)),
        (sSup ((fun y => (R56Audit.F χ P ((c : ℝ) / (b : ℝ)^j) y +
          R56Audit.F χ P (((c : ℝ)+1) / (b : ℝ)^j) y) / 2) ''
          Set.Ico ((v : ℝ) * ((b : ℝ)^j / (b : ℝ)^h))
            (((v : ℝ)+1) * ((b : ℝ)^j / (b : ℝ)^h))) -
         sInf ((fun y => (R56Audit.F χ P ((c : ℝ) / (b : ℝ)^j) y +
          R56Audit.F χ P (((c : ℝ)+1) / (b : ℝ)^j) y) / 2) ''
          Set.Ico ((v : ℝ) * ((b : ℝ)^j / (b : ℝ)^h))
            (((v : ℝ)+1) * ((b : ℝ)^j / (b : ℝ)^h))))) / (b : ℝ)^h := rfl

example {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype ι] (X : ι → Ω → ℝ)
    (hi : iIndepFun X μ) (hs : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    {σ : ℝ} (hσ : 0 < σ) (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2)
    (hint : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ 3 * σ ^ 4) (θ : ℝ) :
    σ * Real.sqrt (Fintype.card ι / 3) ≤ ∫ ω, |θ + ∑ i, X i ω| ∂μ :=
  R56Audit.fact_2_2_general X hi hs hσ h2 hint h4 θ

example {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (Γ : Ω → G) (ξ : Fin n → Ω → E) (hΓ : Measurable Γ) (hξ : ∀ i, Measurable (ξ i))
    (hi : iIndepFun ξ μ) (hiΓ : IndepFun Γ (fun ω i => ξ i ω) μ)
    (φ : G × (Fin n → E) → ℝ) (hm : Measurable φ) {c : ℝ} (hc : 0 < c)
    (hd : ∀ γ x i a, |φ (γ, Function.update x i a) - φ (γ, x)| ≤ c)
    (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i ω)) μ) (t : ℝ) :
    ∀ᵐ ω ∂μ, (μ[fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
      (μ[fun ω => φ (Γ ω, fun i => ξ i ω) | MeasurableSpace.comap Γ inferInstance]) ω)) |
        MeasurableSpace.comap Γ inferInstance]) ω ≤ Real.exp (n * t^2 * c^2 / 2) :=
  R56Audit.fact_A_1 Γ ξ hΓ hξ hi hiΓ φ hm hc hd hint t

#print axioms R56Audit.theorem_1_1_unfolded
#print axioms R56Audit.proposition_2_7
#print axioms R56Audit.fact_2_2_general
#print axioms R56Audit.fact_A_1
