import Riesz.WeightedMoments

/-!
# From recursive independent samples to finite vectors

The weighted-moment proof uses an iterated binary product sample space. This
module identifies it with ordinary vectors and derives the normalized finite
sum needed by the conditional fresh-digit law. No moment or Laplace conclusion
is introduced as an assumption.
-/

namespace Riesz.Moments

open scoped BigOperators

universe u

/-- The recursive sample space is exactly the space of length-`n` vectors. -/
noncomputable def sampleSpaceEquiv (Ω : Type u) : (n : ℕ) → SampleSpace Ω n ≃ (Fin n → Ω)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n + 1 =>
    ((Equiv.prodCongr (sampleSpaceEquiv Ω n) (Equiv.refl Ω)).trans
      (Equiv.prodComm _ _)).trans (Fin.snocEquiv (fun _ : Fin (n + 1) => Ω))

@[simp] lemma sampleSpaceEquiv_castSucc (Ω : Type u) (n : ℕ) (ω : SampleSpace Ω (n + 1))
    (i : Fin n) :
    sampleSpaceEquiv Ω (n + 1) ω i.castSucc = sampleSpaceEquiv Ω n ω.1 i := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Ω) (sampleSpaceEquiv Ω n ω.1) ω.2 i.castSucc = _
  exact Fin.snoc_castSucc _ _ _

@[simp] lemma sampleSpaceEquiv_last (Ω : Type u) (n : ℕ) (ω : SampleSpace Ω (n + 1)) :
    sampleSpaceEquiv Ω (n + 1) ω (Fin.last n) = ω.2 := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Ω) (sampleSpaceEquiv Ω n ω.1) ω.2 (Fin.last n) = _
  exact Fin.snoc_last _ _

variable {Ω : Type u} [Fintype Ω]

lemma independentLaw_constant_weight (μ : FiniteLaw Ω) (c : ℝ)
    (hweight : ∀ ω, μ.weight ω = c) (n : ℕ) (ω : SampleSpace Ω n) :
    (independentLaw μ n).weight ω = c ^ n := by
  induction n with
  | zero => simp [independentLaw]
  | succ n ih =>
    change (independentLaw μ n).weight ω.1 * μ.weight ω.2 = c ^ (n + 1)
    rw [ih, hweight, pow_succ]

/-- Exact conversion of expectations under a uniform recursive product law
into a finite vector sum. -/
theorem expectation_independentLaw_vector (μ : FiniteLaw Ω) (c : ℝ)
    (hweight : ∀ ω, μ.weight ω = c) (n : ℕ) (H : (Fin n → Ω) → ℝ) :
    expectation (independentLaw μ n) (fun ω => H (sampleSpaceEquiv Ω n ω)) =
      c ^ n * ∑ ω : Fin n → Ω, H ω := by
  unfold expectation
  simp_rw [independentLaw_constant_weight μ c hweight n]
  rw [← Finset.mul_sum]
  congr 1
  exact (sampleSpaceEquiv Ω n).sum_comp H

omit [Fintype Ω] in
/-- The recursively defined weighted sum is the ordinary vector dot product. -/
lemma weightedSum_eq_vector_sum (W : Ω → ℝ) (n : ℕ) (a : Fin n → ℝ)
    (ω : SampleSpace Ω n) :
    weightedSum W n a ω = ∑ i, a i * W (sampleSpaceEquiv Ω n ω i) := by
  induction n with
  | zero => simp [weightedSum]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [weightedSum, sampleSpaceEquiv_castSucc, sampleSpaceEquiv_last]
    rw [ih]

/-- Exact expectation identity for independent uniform dyadic profile cells. -/
theorem profile_vector_expectation (m : ℕ) (hm : 0 < m) (n : ℕ)
    (H : (Fin n → (Fin 4 × Fin m)) → ℝ) :
    expectation (independentLaw (profileLaw m hm) n)
      (fun ω => H (sampleSpaceEquiv (Fin 4 × Fin m) n ω)) =
      (∑ ω : Fin n → (Fin 4 × Fin m), H ω) / (4 * (m : ℝ)) ^ n := by
  rw [expectation_independentLaw_vector (profileLaw m hm) (1 / (4 * (m : ℝ)))
    (fun _ => rfl)]
  rw [one_div_pow]
  ring

/-- The one-rectangle Laplace estimate as the normalized finite average over
ordinary profile-cell vectors, derived from the proved independent-sum theorem. -/
theorem profile_vector_laplace (m : ℕ) (hm : 0 < m)
    (n : ℕ) (a : Fin n → ℝ) (good : Finset (Fin n)) (C lam b : ℝ)
    (hC : 20 < C) (hlam : 1 ≤ lam) (hb : 0 < b)
    (hbC : b ≤ 1 / (512 * C ^ (3 / 2 : ℝ)))
    (hgood : ∀ i ∈ good, 1 / C ≤ |a i|) (hcount : (good.card : ℝ) / lam ≤ C) :
    (∑ ω : Fin n → (Fin 4 × Fin m),
      Real.exp (-|∑ i, a i * profileValue m (ω i)| / Real.sqrt lam)) /
      (4 * (m : ℝ)) ^ n ≤ Real.exp (-b * (good.card : ℝ) / lam) := by
  have hh := dyadic_profile_sum_laplace m hm n a good C lam b hC hlam hb hbC hgood hcount
  have heq := profile_vector_expectation m hm n
    (fun ω => Real.exp (-|∑ i, a i * profileValue m (ω i)| / Real.sqrt lam))
  rw [← heq]
  simpa only [weightedSum_eq_vector_sum] using hh


/-- Flatten each quarter/cell pair into its ordinary `4m`-cell index. -/
lemma profile_vector_sum_eq_flat (m n : ℕ) (H : (Fin n → (Fin 4 × Fin m)) → ℝ) :
    (∑ ω : Fin n → (Fin 4 × Fin m), H ω) =
      ∑ ω : Fin n → Fin (4 * m), H (fun i => finProdFinEquiv.symm (ω i)) := by
  let e : (Fin n → (Fin 4 × Fin m)) ≃ (Fin n → Fin (4 * m)) :=
    Equiv.piCongrRight (fun _ => finProdFinEquiv)
  apply Fintype.sum_equiv e
  intro ω
  congr 1
  funext i
  exact (finProdFinEquiv.symm_apply_apply (ω i)).symm

/-- The normalized finite average in the exact flattened-vector form used by
`condExp_freshGrid_vector`. Its probability denominator is `(4m)^n`. -/
theorem flat_profile_vector_laplace (m : ℕ) (hm : 0 < m)
    (n : ℕ) (a : Fin n → ℝ) (good : Finset (Fin n)) (C lam b : ℝ)
    (hC : 20 < C) (hlam : 1 ≤ lam) (hb : 0 < b)
    (hbC : b ≤ 1 / (512 * C ^ (3 / 2 : ℝ)))
    (hgood : ∀ i ∈ good, 1 / C ≤ |a i|) (hcount : (good.card : ℝ) / lam ≤ C) :
    (∑ ω : Fin n → Fin (4 * m),
      Real.exp (-|∑ i, a i * profileValue m (finProdFinEquiv.symm (ω i))| / Real.sqrt lam)) /
      ((4 * m : ℕ) : ℝ) ^ n ≤ Real.exp (-b * (good.card : ℝ) / lam) := by
  have hh := profile_vector_laplace m hm n a good C lam b hC hlam hb hbC hgood hcount
  rw [profile_vector_sum_eq_flat] at hh
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh


/-- The same bound for an arbitrary finite set of point indices, including a
rectangle's subtype of sample indices. Reindexing is by an actual equivalence. -/
theorem flat_profile_fintype_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (a : ι → ℝ) (good : Finset ι) (C lam b : ℝ)
    (hC : 20 < C) (hlam : 1 ≤ lam) (hb : 0 < b)
    (hbC : b ≤ 1 / (512 * C ^ (3 / 2 : ℝ)))
    (hgood : ∀ i ∈ good, 1 / C ≤ |a i|) (hcount : (good.card : ℝ) / lam ≤ C) :
    (∑ ω : ι → Fin (4 * m),
      Real.exp (-|∑ i, a i * profileValue m (finProdFinEquiv.symm (ω i))| / Real.sqrt lam)) /
      ((4 * m : ℕ) : ℝ) ^ Fintype.card ι ≤ Real.exp (-b * (good.card : ℝ) / lam) := by
  classical
  let e := Fintype.equivFin ι
  let a' : Fin (Fintype.card ι) → ℝ := fun i => a (e.symm i)
  let good' := good.map e.toEmbedding
  have hg : ∀ i ∈ good', 1 / C ≤ |a' i| := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simpa only [a', Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hgood j hj
  have hcnt : (good'.card : ℝ) / lam ≤ C := by simpa [good'] using hcount
  have hh := flat_profile_vector_laplace m hm (Fintype.card ι) a' good' C lam b
    hC hlam hb hbC hg hcnt
  let ev : (ι → Fin (4 * m)) ≃ (Fin (Fintype.card ι) → Fin (4 * m)) :=
    Equiv.arrowCongr e (Equiv.refl _)
  have hs : (∑ ω : ι → Fin (4 * m),
      Real.exp (-|∑ i, a i * profileValue m (finProdFinEquiv.symm (ω i))| / Real.sqrt lam)) =
      ∑ ω : Fin (Fintype.card ι) → Fin (4 * m),
        Real.exp (-|∑ i, a' i * profileValue m (finProdFinEquiv.symm (ω i))| / Real.sqrt lam) := by
    apply Fintype.sum_equiv ev
    intro ω
    change Real.exp (-|∑ i, a i * profileValue m (finProdFinEquiv.symm (ω i))| / Real.sqrt lam) =
      Real.exp (-|∑ i, a (e.symm i) * profileValue m (finProdFinEquiv.symm (ω (e.symm i)))| /
        Real.sqrt lam)
    rw [e.symm.sum_comp (fun i => a i * profileValue m (finProdFinEquiv.symm (ω i)))]
  rw [hs]
  simpa only [good', Finset.card_map] using hh

end Riesz.Moments
