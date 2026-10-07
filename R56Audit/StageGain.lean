import R56Audit.Potential

/-!
# Summing Lemma 2.3 over the comparison rectangles of a transition

Auditor's supplement (not part of the audited archive).

Proof of Lemma 2.4: "Every old cell is a horizontal strip of exactly one comparison rectangle
`R = I × J`, and every new cell is a vertical strip of exactly one. So, with the children
`C_1, …, C_b` of `I` and the blocks `B_1, …, B_b` of `J` for each `R`,

`bM (Z_{j+1} - Z_j) = Σ_R (Σ_k osc_J a^{(C_k)} - Σ_ℓ osc_{B_ℓ} a^{(I)})`.

Conditionally on `𝓕_j`, the next digits perform the local experiment of Section 2.3 in every
`R` at once \[…\]. So Lemma 2.3 bounds the conditional expectation of each term, and dividing
by `bM` gives (11)."

`Zstep_gain` is this computation for fixed heights `V` and fixed stage-`j` indices `g`: the
average of `Z_{j+1}` over the next digits is at least `Z_j + δ_j`.

The comparison rectangle `R = I × J` with the index `(c, v)`, `c < b^j` and `v < b^{h-j-1}`,
has the `c`-th horizontal interval of stage `j` as `I` and the `v`-th vertical interval of
stage `j+1` as `J`. The two halves of the displayed identity are

* `Zstep_eq_sum_blocks`: `Z_j = (1/(bM)) Σ_R Σ_ℓ osc_{B_ℓ} a^{(I)}` (the old cells);
* `Zstep_succ_eq_sum_children`: `Z_{j+1} = (1/(bM)) Σ_R Σ_k osc_J a^{(C_k)}` (the new cells),
  where the endpoint average of the child `C_{k+1}` of `I`, the interval `b c + k` of stage
  `j+1`, is the child function of the local experiment (`childAvg_sideIdx`).
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ}

/-- The points of the inner region of the comparison rectangle `R = I × J` of the transition
`j → j+1`, where `I` is the `c`-th horizontal interval of stage `j` and `J` the `v`-th
vertical interval of stage `j+1`: the points with stage-`j` index `c` whose height lies in
`J` without its bottom and top blocks. -/
def innerSet (b h j : ℕ) (V : Fin n → ℝ) (g : Fin n → ℤ) (c v : ℕ) : Finset (Fin n) :=
  innerPoints b V (fun i => sideIdx (g i) c) ((v : ℝ) * vlen b h (j + 1)) (vlen b h j)

/-- `δ_j = (1/(4bM)) Σ_R √(m_R)` of display (11), read from the heights and the indices. -/
def deltaStep (b h j : ℕ) (V : Fin n → ℝ) (g : Fin n → ℤ) : ℝ :=
  (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)),
      Real.sqrt ((innerSet b h j V g c v).card)) / (4 * (b : ℝ) * (b : ℝ) ^ (h - 1))

/-- The numbers below `b ^ (m + 1)` are the numbers `b v + ℓ` with `v < b ^ m` and `ℓ < b`. -/
lemma sum_fin_pow_eq_sum_mul_add (b : ℕ) {e m : ℕ} (he : e = m + 1) (f : ℕ → ℝ) :
    ∑ w : Fin (b ^ e), f w = ∑ v : Fin (b ^ m), ∑ ℓ : Fin b, f (b * v + ℓ) := by
  subst he
  rw [Fin.sum_univ_eq_sum_range f (b ^ (m + 1)), pow_succ,
    ← Fin.sum_univ_eq_sum_range f (b ^ m * b), ← finProdFinEquiv.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun ℓ _ => ?_
  rw [finProdFinEquiv_apply_val, add_comm]

/-- The weight in the child `C_{κ+1}` of the interval `c` is that in the interval `b c + κ`. -/
lemma childWeight_sideIdx {b : ℕ} (G : ℤ) (c : ℕ) (ρ κ : Fin b) :
    childWeight (sideIdx G c) ρ κ =
      oldWeight (sideIdx ((b : ℤ) * G + ((ρ : ℕ) : ℤ)) (b * c + κ)) := by
  have hρ : ((ρ : ℕ) : ℤ) < b := by exact_mod_cast ρ.isLt
  have hκ : ((κ : ℕ) : ℤ) < b := by exact_mod_cast κ.isLt
  unfold sideIdx
  rw [Nat.cast_add, Nat.cast_mul]
  rcases lt_trichotomy G (c : ℤ) with hG | rfl | hG
  · -- to the left of `I`, hence to the left of every child
    have h1 : (b : ℤ) * G + (ρ : ℕ) < (b : ℤ) * c + (κ : ℕ) := by nlinarith
    rw [ite_eq_left hG, ite_eq_left h1]
    rfl
  · -- in `I`: the next digit `ρ` is compared with `κ`
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    change (if ρ < κ then (1 : ℝ) else if ρ = κ then 1 / 2 else 0) = _
    rcases lt_trichotomy ρ κ with hr | rfl | hr
    · have h1 : (b : ℤ) * c + (ρ : ℕ) < (b : ℤ) * c + (κ : ℕ) := by omega
      rw [ite_eq_left hr, ite_eq_left h1]
      rfl
    · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, ite_eq_right (lt_irrefl _),
        ite_eq_left rfl]
      rfl
    · have h1 : (b : ℤ) * c + (κ : ℕ) < (b : ℤ) * c + (ρ : ℕ) := by omega
      rw [ite_eq_right (lt_asymm hr), ite_eq_right hr.ne', ite_eq_right (lt_asymm h1),
        ite_eq_right h1.ne']
      rfl
  · -- to the right of `I`, hence to the right of every child
    have h1 : (b : ℤ) * c + (κ : ℕ) < (b : ℤ) * G + (ρ : ℕ) := by nlinarith
    rw [ite_eq_right (lt_asymm hG), ite_eq_right hG.ne', ite_eq_right (lt_asymm h1),
      ite_eq_right h1.ne']
    rfl

/-- The child function `a_{k+1}` of `I` is the endpoint average of the interval `b c + k`. -/
lemma childAvg_sideIdx {b : ℕ} (ε V : Fin n → ℝ) (g : Fin n → ℤ) (c : ℕ)
    (r : Fin n → Fin b) (k : Fin b) :
    childAvg ε V (fun i => sideIdx (g i) c) r k =
      endpointAvg ε V (fun i => sideIdx (refineIdx g r i) (b * c + k)) := by
  funext y
  refine stepFn_congr V (fun i => ?_) y
  change ε i * childWeight (sideIdx (g i) c) (r i) k =
    ε i * oldWeight (sideIdx ((b : ℤ) * g i + ((r i : ℕ) : ℤ)) (b * c + k))
  rw [childWeight_sideIdx]

/-- `Z_j = (1/(bM)) Σ_R Σ_ℓ osc_{B_ℓ} a^{(I)}`: an old cell is a horizontal strip of one `R`. -/
lemma Zstep_eq_sum_blocks {b h j : ℕ} (hj : j < h) (ε V : Fin n → ℝ) (g : Fin n → ℤ) :
    Zstep ε b h j V g =
      (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), ∑ ℓ : Fin b,
        osc (block ((v : ℝ) * vlen b h (j + 1)) (vlen b h j) ℓ)
          (endpointAvg ε V (fun i => sideIdx (g i) c))) / (b : ℝ) ^ h := by
  unfold Zstep
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  -- the vertical intervals of stage `j` are the blocks `b v + ℓ` of those of stage `j + 1`
  rw [sum_fin_pow_eq_sum_mul_add b (by omega : h - j = h - j - 1 + 1)
    (fun w => osc (vcell b h j w) (endpointAvg ε V (fun i => sideIdx (g i) c)))]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun ℓ _ => ?_
  rw [vcell_eq_block]

/-- `Z_{j+1} = (1/(bM)) Σ_R Σ_k osc_J a^{(C_k)}`: a new cell is a vertical strip of one `R`. -/
lemma Zstep_succ_eq_sum_children {b : ℕ} (h j : ℕ) (ε V : Fin n → ℝ) (g : Fin n → ℤ)
    (r : Fin n → Fin b) :
    Zstep ε b h (j + 1) V (refineIdx g r) =
      (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), ∑ k : Fin b,
        osc (Set.Ico ((v : ℝ) * vlen b h (j + 1)) ((v : ℝ) * vlen b h (j + 1) + b * vlen b h j))
          (childAvg ε V (fun i => sideIdx (g i) c) r k)) / (b : ℝ) ^ h := by
  unfold Zstep
  congr 1
  -- the horizontal intervals of stage `j + 1` are the children `b c + k` of those of stage `j`
  rw [Nat.sub_add_eq, sum_fin_pow_eq_sum_mul_add b rfl (fun w => ∑ v : Fin (b ^ (h - j - 1)),
    osc (vcell b h (j + 1) v) (endpointAvg ε V (fun i => sideIdx (refineIdx g r i) w)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k _ => ?_
  rw [vcell_succ_eq, childAvg_sideIdx]

/-- **Lemma 2.4 for fixed heights and stage-`j` indices**: the average of `Z_{j+1}` over the
next digits is at least `Z_j + δ_j`. -/
theorem Zstep_gain {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) (ε : Fin n → ℝ)
    (hε : ∀ i, |ε i| = 1) (V : Fin n → ℝ) (g : Fin n → ℤ) :
    Zstep ε b h j V g + deltaStep b h j V g ≤
      finAvg (fun r : Fin n → Fin b => Zstep ε b h (j + 1) V (refineIdx g r)) := by
  have hb0 : 0 < b := by omega
  -- `4bM = 4b^h`
  have hbM : 4 * (b : ℝ) * (b : ℝ) ^ (h - 1) = 4 * (b : ℝ) ^ h := by
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ h)]
  -- `Z_j + δ_j`, as a sum over the comparison rectangles (the old cells)
  calc Zstep ε b h j V g + deltaStep b h j V g
      = (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)),
          (∑ ℓ : Fin b, osc (block ((v : ℝ) * vlen b h (j + 1)) (vlen b h j) ℓ)
              (endpointAvg ε V (fun i => sideIdx (g i) c)) +
            (1 / 4) * Real.sqrt (innerSet b h j V g c v).card)) / (b : ℝ) ^ h := by
        rw [Zstep_eq_sum_blocks hj, deltaStep, hbM]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    -- Lemma 2.3 in every comparison rectangle
    _ ≤ (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)),
          finAvg (fun r : Fin n → Fin b => ∑ k : Fin b,
            osc (Set.Ico ((v : ℝ) * vlen b h (j + 1))
                ((v : ℝ) * vlen b h (j + 1) + b * vlen b h j))
              (childAvg ε V (fun i => sideIdx (g i) c) r k))) / (b : ℝ) ^ h :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun v _ =>
          local_gain hb ε hε V _ _ (vlen_pos hb0 h j)) (by positivity)
    -- the new cells; the average of a sum is the sum of the averages
    _ = finAvg (fun r : Fin n → Fin b => Zstep ε b h (j + 1) V (refineIdx g r)) := by
        simp_rw [Zstep_succ_eq_sum_children, finAvg_div_const, finAvg_sum]

end

end R56Audit
