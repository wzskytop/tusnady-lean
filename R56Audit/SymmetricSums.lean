import R56Audit.UniformDigits

/-!
# Fact 2.2 of the manuscript, in the form used by Lemma 2.3

Auditor's supplement (not part of the audited archive).

**Fact 2.2.** Let `X_1, …, X_m` be independent symmetric random variables with
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴`. Then `E|θ + X_1 + ⋯ + X_m| ≥ σ √(m/3)` for every real `θ`.

The fact itself, for real random variables on any probability space, is `fact_2_2_general`
in `SymmetricSumsGeneral.lean`. This file states it in the setting of Lemma 2.3: the
probability space is a finite product `Fin n → D` with the uniform law (`D` is the set of
digits, and `Oscillation.finAvg` is the expectation), `X_i = x_i(r_i)` is a function of the
`i`-th digit, and "symmetric" is witnessed by a permutation `φ_i` of the digits with
`x_i ∘ φ_i = -x_i` (`exists_symm_perm_iff`: this is exactly symmetry of the distribution).

* `symmetric_sum_abs`: the sum runs over the points of a set `S`, and the shift `θ` may
  depend on the digits of the other points: the conditioning step of the proof of Lemma 2.3
  ("condition on the children of all other points"). Proved from `fact_2_2_uniform`, the
  instance of `fact_2_2_general` for independent uniform digits, applied for every value of
  the other digits.
* `fact_2_2`: the case of a constant shift.
* `finAvg_mul_coord`, `finAvg_coord`, `finAvg_eq_zero_of_symm`: a digit is uniform and
  independent of the other digits; a symmetric function of a digit has mean zero (used for
  display (7)).
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ} {D : Type*} [Fintype D]

/-! ### The uniform law on a finite product: one coordinate is independent of the others -/

/-- `(r, d) ↦ (r with r_i := d, r_i)` is an involution of `(Fin n → D) × D`. -/
def updateEquiv (i : Fin n) : ((Fin n → D) × D) ≃ ((Fin n → D) × D) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    rcases p with ⟨r, d⟩
    simp
  right_inv p := by
    rcases p with ⟨r, d⟩
    simp

/-- Resampling one coordinate does not change an average. -/
lemma finAvg_update [Nonempty D] (i : Fin n) (F : (Fin n → D) → ℝ) :
    finAvg (fun r => finAvg (fun d => F (Function.update r i d))) = finAvg F := by
  have h1 := finAvg_prod (fun p : (Fin n → D) × D => F (Function.update p.1 i p.2))
  have h2 := finAvg_equiv (updateEquiv i) (fun p : (Fin n → D) × D => F p.1)
  have h3 := finAvg_prod (fun p : (Fin n → D) × D => F p.1)
  have h4 : finAvg (fun r : Fin n → D => finAvg (fun _ : D => F r)) = finAvg F :=
    finAvg_congr fun r => finAvg_const _
  rw [← h1]
  exact h2.trans (h3.trans h4)

/-- A function of the `i`-th digit is independent of a function that does not depend on
it. -/
lemma finAvg_mul_coord [Nonempty D] (i : Fin n) (g : D → ℝ) (Y : (Fin n → D) → ℝ)
    (hY : ∀ r d, Y (Function.update r i d) = Y r) :
    finAvg (fun r => g (r i) * Y r) = finAvg g * finAvg Y := by
  rw [← finAvg_update i]
  simp only [Function.update_self, hY]
  simp_rw [finAvg_mul_const]
  rw [finAvg_const_mul]

/-- The `i`-th digit is uniform. -/
lemma finAvg_coord [Nonempty D] (i : Fin n) (g : D → ℝ) :
    finAvg (fun r : Fin n → D => g (r i)) = finAvg g := by
  have h := finAvg_mul_coord i g (fun _ => (1 : ℝ)) (fun _ _ => rfl)
  simpa using h

lemma finAvg_neg' {α : Type*} [Fintype α] (f : α → ℝ) :
    finAvg (fun x => -f x) = -finAvg f := by
  have := finAvg_const_mul (-1) f
  simpa using this

/-- A symmetric function of a uniform digit has mean zero. -/
lemma finAvg_eq_zero_of_symm (φ : D ≃ D) (g : D → ℝ) (h : ∀ d, g (φ d) = -g d) :
    finAvg g = 0 := by
  have h1 := finAvg_equiv φ g
  simp only [h] at h1
  rw [finAvg_neg'] at h1
  linarith

/-- For a function `x` of a uniform digit, the existence of a permutation `φ` of the digits
with `x ∘ φ = -x` says exactly that `x` is symmetric, i.e. has the same distribution as `-x`:
every value `v` is taken as often as `-v`. So the hypothesis `hφ` of the results below is the
manuscript's "symmetric", not a stronger condition. -/
theorem exists_symm_perm_iff (x : D → ℝ) :
    (∃ φ : D ≃ D, ∀ d, x (φ d) = -x d) ↔
      ∀ v : ℝ, Nat.card {d // x d = v} = Nat.card {d // x d = -v} := by
  classical
  constructor
  · rintro ⟨φ, hφ⟩ v
    apply Nat.card_congr
    exact
      { toFun := fun d => ⟨φ d.1, by rw [hφ, d.2]⟩
        invFun := fun d => ⟨φ.symm d.1, by
          have h := hφ (φ.symm d.1)
          rw [Equiv.apply_symm_apply, d.2] at h
          linarith⟩
        left_inv := fun d => by simp
        right_inv := fun d => by simp }
  · intro h
    have e : ∀ v : ℝ, {d // x d = v} ≃ {d // x d = -v} := fun v =>
      (Finite.card_eq.mp (h v)).some
    let φ : D → D := fun d => (e (x d) ⟨d, rfl⟩).1
    have hφ : ∀ d, x (φ d) = -x d := fun d => (e (x d) ⟨d, rfl⟩).2
    have hval : ∀ d (v : ℝ) (hv : x d = v), φ d = (e v ⟨d, hv⟩).1 := by
      intro d v hv
      subst hv
      rfl
    have hinj : Function.Injective φ := by
      intro d d' hdd
      have hx : x d = x d' := by
        have h1 := hφ d
        have h2 := hφ d'
        rw [hdd] at h1
        linarith
      rw [hval d (x d') hx, hval d' (x d') rfl] at hdd
      have := (e (x d')).injective (Subtype.ext hdd)
      exact congrArg Subtype.val this
    exact ⟨Equiv.ofBijective φ (Finite.injective_iff_bijective.mp hinj), hφ⟩

/-! ### Sums of independent symmetric jumps -/

/-- `Σ_{i ∈ S} x_i(r_i)`: the sum of the jumps of the points in `S`. -/
def jumpSum (S : Finset (Fin n)) (x : Fin n → D → ℝ) (r : Fin n → D) : ℝ :=
  ∑ i ∈ S, x i (r i)

/-- The digits of the points of `S` and the digits of the other points. -/
def splitDigits (S : Finset (Fin n)) (D : Type*) :
    (Fin n → D) ≃ ({i // i ∈ S} → D) × ({i // i ∉ S} → D) :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ S) (fun _ => D)

omit [Fintype D] in
lemma splitDigits_symm_mem (S : Finset (Fin n)) (p : ({i // i ∈ S} → D) × ({i // i ∉ S} → D))
    (i : {i // i ∈ S}) : (splitDigits S D).symm p i = p.1 i := by
  simp [splitDigits, Equiv.piEquivPiSubtypeProd, i.2]

omit [Fintype D] in
lemma splitDigits_symm_notMem (S : Finset (Fin n))
    (p : ({i // i ∈ S} → D) × ({i // i ∉ S} → D)) {i : Fin n} (hi : i ∉ S) :
    (splitDigits S D).symm p i = p.2 ⟨i, hi⟩ := by
  simp [splitDigits, Equiv.piEquivPiSubtypeProd, hi]

/-- **Fact 2.2 (sums of symmetric variables)**, in the form in which Lemma 2.3 uses it: the
jumps `X_i = x_i(r_i)`, `i ∈ S`, are functions of independent uniform digits, and the shift
`θ` may depend on the digits of the other points. If the jumps are symmetric with
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴`, then `E|θ + Σ_{i ∈ S} X_i| ≥ σ √(m/3)`, where `m = |S|`.

"Now condition on the children of all other points \[…\]. This fixes \[…\] the number `θ`.
The children of the `m_R` points of `R^in` are independent of the conditioning, so the jumps
in `D` are still independent and symmetric. \[…\] So Fact 2.2 applies to `θ + D`, with
`m = m_R`." The proof does exactly this: for every value of the other digits, it applies
`fact_2_2_uniform`, the instance of Fact 2.2 (`fact_2_2_general`) for independent uniform
digits. -/
theorem symmetric_sum_abs [Nonempty D] (S : Finset (Fin n)) (x : Fin n → D → ℝ)
    (φ : Fin n → D ≃ D) (hφ : ∀ i ∈ S, ∀ d, x i (φ i d) = -x i d) {σ : ℝ} (hσ : 0 ≤ σ)
    (h2 : ∀ i ∈ S, finAvg (fun d => x i d ^ 2) = σ ^ 2)
    (h4 : ∀ i ∈ S, finAvg (fun d => x i d ^ 4) ≤ 3 * σ ^ 4)
    (θ : (Fin n → D) → ℝ)
    (hθ : ∀ r r' : Fin n → D, (∀ i, i ∉ S → r i = r' i) → θ r = θ r') :
    σ * Real.sqrt (S.card / 3) ≤ finAvg (fun r : Fin n → D => |θ r + jumpSum S x r|) := by
  classical
  rcases hσ.eq_or_lt with rfl | hσpos
  · rw [zero_mul]
    exact finAvg_nonneg fun _ => abs_nonneg _
  -- condition on the digits of the points outside `S`
  rw [← finAvg_equiv (splitDigits S D).symm, finAvg_prod, finAvg_finAvg_comm]
  have hne : Nonempty ({i // i ∉ S} → D) := ⟨fun _ => Classical.arbitrary D⟩
  refine le_trans (le_of_eq (finAvg_const (α := {i // i ∉ S} → D) _).symm) (finAvg_mono fun rO => ?_)
  -- the shift is now a number
  have hconst : ∀ rS : {i // i ∈ S} → D,
      θ ((splitDigits S D).symm (rS, rO)) =
        θ ((splitDigits S D).symm (fun _ => Classical.arbitrary D, rO)) := fun rS =>
    hθ _ _ fun i hi => by rw [splitDigits_symm_notMem S _ hi, splitDigits_symm_notMem S _ hi]
  have hsum : ∀ rS : {i // i ∈ S} → D,
      jumpSum S x ((splitDigits S D).symm (rS, rO)) = ∑ i : {i // i ∈ S}, x i (rS i) := by
    intro rS
    unfold jumpSum
    rw [← Finset.sum_coe_sort S (fun i => x i ((splitDigits S D).symm (rS, rO) i))]
    exact Finset.sum_congr rfl fun i _ => by rw [splitDigits_symm_mem]
  -- Fact 2.2 for the digits of the points of `S`
  have hF := fact_2_2_uniform (fun i : {i // i ∈ S} => x i) (fun i : {i // i ∈ S} => φ i)
    (fun i d => hφ i i.2 d) hσpos (fun i => h2 i i.2) (fun i => h4 i i.2)
    (θ ((splitDigits S D).symm (fun _ => Classical.arbitrary D, rO)))
  rw [Fintype.card_coe] at hF
  refine hF.trans (le_of_eq (finAvg_congr fun rS => ?_))
  rw [hconst rS, hsum rS]

/-- **Fact 2.2** in the manuscript's form, for `m` independent uniform digits: if
`X_i = x_i(r_i)` are symmetric with `E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴`, where `σ > 0`, then
`E|θ + X_1 + ⋯ + X_m| ≥ σ √(m/3)` for every real `θ`. (The case `ι = Fin m` of
`fact_2_2_uniform`; the statement for arbitrary real random variables is
`fact_2_2_general`.) -/
theorem fact_2_2 [Nonempty D] {m : ℕ} (x : Fin m → D → ℝ) (φ : Fin m → D ≃ D)
    (hφ : ∀ i d, x i (φ i d) = -x i d) {σ : ℝ} (hσ : 0 < σ)
    (h2 : ∀ i, finAvg (fun d => x i d ^ 2) = σ ^ 2)
    (h4 : ∀ i, finAvg (fun d => x i d ^ 4) ≤ 3 * σ ^ 4) (θ : ℝ) :
    σ * Real.sqrt (m / 3) ≤ finAvg (fun r : Fin m → D => |θ + ∑ i, x i (r i)|) := by
  have h := fact_2_2_uniform x φ hφ hσ h2 h4 θ
  rwa [Fintype.card_fin] at h

end

end R56Audit
