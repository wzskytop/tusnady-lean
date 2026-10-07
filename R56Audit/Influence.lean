import R56Audit.Potential

/-!
# One digit of one point changes the potential by at most `1/M`

Auditor's supplement (not part of the audited archive).

Step 1 of the proof of Lemma 2.6: "Changing the next digit of one point `P_i` changes
`Z_{j+1}` by at most `1/M`. Indeed, the change moves `P_i` to another child of its stage-`j`
interval `I`. So the weight of `P_i` changes only in the `b` children of `I`, in each of them
by a number in `[-1,1]`. Hence the endpoint average of each child changes by a multiple of the
function `y ↦ 1{V_i ≤ y}`, with a factor in `[-1,1]`, and the endpoint average of no other
interval of stage `j+1` changes. Consider a cell `C × B` of stage `j+1`, where `C` is a child
of `I`. If `V_i ∉ B`, the added function is constant on `B`, and `osc_B a^{(C)}` does not
change, by shift invariance. If `V_i ∈ B`, the added function has oscillation at most `1` on
`B`, and `osc_B a^{(C)}` changes by at most `1`, by the reverse triangle inequality. The
second case occurs for `b` cells, one for each child. Since `Z_{j+1}` is the sum of the
oscillations over the `bM` cells, divided by `bM`, it changes by at most `b/(bM) = 1/M`."

`Zstep_update_le` is this statement, for fixed heights `V` and fixed stage-`j` indices `g`.
Its proof follows the sentences above:

* `refineIdx_mem_block`, `refineIdx_update_of_ne`: the change moves `P_i` to another child of
  `I`, and it moves no other point;
* `abs_oldWeight_sideIdx_sub_le`, `sum_ite_block_le`: the weight of `P_i` changes only in the
  `b` children of `I`, in each of them by a number in `[-1,1]`;
* `abs_osc_endpointAvg_sub_le`: one cell `C × B`, with the two cases of the manuscript. If
  `V_i ∉ B`, the added function is constant on `B` (`stepFn_single_eq_of_notMem` in
  `StepOsc.lean`), and the oscillation does not change, by shift invariance (`osc_add_const`).
  If `V_i ∈ B`, the added function has oscillation at most the size of its jump
  (`osc_stepFn_single_le`), and the oscillation changes by at most this much, by the reverse
  triangle inequality (`abs_osc_add_sub_le`);
* `sum_abs_osc_endpointAvg_sub_le`: `V_i` lies in at most one vertical interval `B` of the
  stage (`vcell_unique`), so the second case occurs for at most one cell of each child;
* `abs_Zstep_sub_le`: the sum of the oscillations over all cells changes by at most `b`.
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ}

/-! ### The weight of `P_i` changes only in the `b` children of `I` -/

/-- Two weights differ by at most `1`. -/
lemma abs_oldWeight_sub_le (sd sd' : Side) : |oldWeight sd' - oldWeight sd| ≤ 1 := by
  cases sd <;> cases sd' <;> simp only [oldWeight] <;> norm_num

/-- Two indices in a block `[m, m + b)` lie on the same side of every index outside the block. -/
lemma sideIdx_eq_of_block {m x x' : ℤ} {b c : ℕ} (hx : m ≤ x ∧ x < m + b)
    (hx' : m ≤ x' ∧ x' < m + b) (hc : ¬(m ≤ (c : ℤ) ∧ (c : ℤ) < m + b)) :
    sideIdx x c = sideIdx x' c := by
  unfold sideIdx
  split_ifs <;> first | rfl | omega

/-- A point moving within a block `[m, m + b)` changes weight only in the block, by at most `1`. -/
lemma abs_oldWeight_sideIdx_sub_le {m x x' : ℤ} {b : ℕ} (hx : m ≤ x ∧ x < m + b)
    (hx' : m ≤ x' ∧ x' < m + b) (c : ℕ) :
    |oldWeight (sideIdx x' c) - oldWeight (sideIdx x c)| ≤
      if m ≤ (c : ℤ) ∧ (c : ℤ) < m + b then 1 else 0 := by
  split_ifs with hc
  · exact abs_oldWeight_sub_le _ _
  · rw [sideIdx_eq_of_block hx' hx hc, sub_self, abs_zero]

/-- A block `[m, m + b)` contains at most `b` of the indices `0, …, N - 1`. -/
lemma sum_ite_block_le (N b : ℕ) (m : ℤ) :
    ∑ c : Fin N, (if m ≤ ((c : ℕ) : ℤ) ∧ ((c : ℕ) : ℤ) < m + b then (1 : ℝ) else 0) ≤ b := by
  -- the indices in the block inject into the interval `[m, m + b)` of integers
  have hcard := Finset.card_le_card_of_injOn (t := Finset.Ico m (m + b))
    (s := Finset.univ.filter fun c : Fin N => m ≤ ((c : ℕ) : ℤ) ∧ ((c : ℕ) : ℤ) < m + b)
    (fun c : Fin N => ((c : ℕ) : ℤ))
    (fun c hc => Finset.mem_Ico.mpr (Finset.mem_filter.mp hc).2)
    (fun c _ c' _ hcc => Fin.ext (Nat.cast_injective hcc))
  rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] at hcard
  rw [Finset.sum_boole]
  exact_mod_cast hcard

/-! ### The cells of one horizontal interval -/

/-- A height lies in at most one vertical interval of a stage. -/
lemma vcell_unique {b : ℕ} (hb : 0 < b) (h j : ℕ) {v v' : ℕ} {y : ℝ} (hv : y ∈ vcell b h j v)
    (hv' : y ∈ vcell b h j v') : v = v' := by
  have hL := (vlen_pos hb h j).le
  have h1 : (v : ℝ) < v' + 1 := lt_of_mul_lt_mul_right (hv.1.trans_lt hv'.2) hL
  have h2 : (v' : ℝ) < v + 1 := lt_of_mul_lt_mul_right (hv'.1.trans_lt hv.2) hL
  have h1' : v < v' + 1 := by exact_mod_cast h1
  have h2' : v' < v + 1 := by exact_mod_cast h2
  omega

/-- One cell `C × B`, with `B = [s, t)`: moving `P_i` changes `osc_B a` by at most
`|ε_i (w_i' - w_i)|`, and only if `V_i ∈ B`. The proof has the two cases of the manuscript:
"If `V_i ∉ B`, the added function is constant on `B`, and `osc_B a^{(C)}` does not change, by
shift invariance. If `V_i ∈ B`, the added function has oscillation at most `1` on `B`, and
`osc_B a^{(C)}` changes by at most `1`, by the reverse triangle inequality." Here the added
function is `ε_i (w_i' - w_i) 1{V_i ≤ ·}`, and the bound is `|ε_i (w_i' - w_i)|` in place of
`1`. -/
lemma abs_osc_endpointAvg_sub_le (ε V : Fin n → ℝ) {side side' : Fin n → Side} (i : Fin n)
    (hside : ∀ k, k ≠ i → side' k = side k) {s t : ℝ} (hst : s < t) :
    |osc (Set.Ico s t) (endpointAvg ε V side') - osc (Set.Ico s t) (endpointAvg ε V side)| ≤
      if V i ∈ Set.Ico s t then |ε i * (oldWeight (side' i) - oldWeight (side i))| else 0 := by
  have hB : (Set.Ico s t).Nonempty := ⟨s, le_rfl, hst⟩
  have hfin : ((endpointAvg ε V side) '' Set.Ico s t).Finite := stepFn_image_finite V _ _
  -- the endpoint average changes by a multiple of the function `y ↦ 1{V_i ≤ y}`
  have hadd : endpointAvg ε V side' = fun y => endpointAvg ε V side y +
      stepFn V (fun k => ε k * (oldWeight (side' k) - oldWeight (side k))) y := by
    funext y
    unfold endpointAvg
    rw [← stepFn_add]
    exact stepFn_congr V (fun k => by ring) y
  -- the added function has its only jump at the height `V_i`
  have hd : ∀ k, k ≠ i → ε k * (oldWeight (side' k) - oldWeight (side k)) = 0 :=
    fun k hk => by rw [hside k hk, sub_self, mul_zero]
  rw [hadd]
  rcases (Classical.em (V i ∈ Set.Ico s t)).symm with hi | hi
  · -- "If `V_i ∉ B`, the added function is constant on `B`, and `osc_B a^{(C)}` does not
    -- change, by shift invariance."
    -- On `B`, the added function is the constant `ε_i (w_i' - w_i)` if `V_i` lies below `B`,
    -- and the constant `0` if `V_i` lies above `B`.
    have hconst : ∀ y ∈ Set.Ico s t,
        endpointAvg ε V side y +
            stepFn V (fun k => ε k * (oldWeight (side' k) - oldWeight (side k))) y =
          endpointAvg ε V side y +
            if V i < s then ε i * (oldWeight (side' i) - oldWeight (side i)) else 0 :=
      fun y hy => by rw [stepFn_single_eq_of_notMem V _ i hd hi hy]
    -- shift invariance: adding a constant does not change the oscillation on `B`
    rw [osc_congr hconst, osc_add_const hB hfin, sub_self, abs_zero, ite_eq_right hi]
  · -- "If `V_i ∈ B`, the added function has oscillation at most `1` on `B`, and `osc_B a^{(C)}`
    -- changes by at most `1`, by the reverse triangle inequality."
    exact (abs_osc_add_sub_le hB hfin (stepFn_image_finite V _ _)).trans
      (osc_stepFn_single_le V _ i hd hst)

/-- The cells of one horizontal interval change by at most `|ε_i (w_i' - w_i)|` in total. -/
lemma sum_abs_osc_endpointAvg_sub_le {b : ℕ} (hb : 0 < b) (h j N : ℕ) (ε V : Fin n → ℝ)
    {side side' : Fin n → Side} (i : Fin n) (hside : ∀ k, k ≠ i → side' k = side k) :
    ∑ v : Fin N, |osc (vcell b h j v) (endpointAvg ε V side') -
        osc (vcell b h j v) (endpointAvg ε V side)| ≤
      |ε i * (oldWeight (side' i) - oldWeight (side i))| := by
  have hcell := fun v : Fin N => abs_osc_endpointAvg_sub_le ε V i hside (vcell_lt hb h j v)
  -- the oscillation does not change on the vertical intervals that do not contain `V_i`
  have hout : ∀ v : Fin N, V i ∉ vcell b h j v →
      |osc (vcell b h j v) (endpointAvg ε V side') -
        osc (vcell b h j v) (endpointAvg ε V side)| = 0 := fun v hv =>
    le_antisymm ((hcell v).trans (ite_eq_right hv).le) (abs_nonneg _)
  by_cases hex : ∃ v₀ : Fin N, V i ∈ vcell b h j v₀
  · -- `V_i` lies in the vertical interval `v₀`, and in no other
    obtain ⟨v₀, hv₀⟩ := hex
    rw [Finset.sum_eq_single_of_mem v₀ (Finset.mem_univ v₀) fun v _ hv =>
      hout v fun hy => hv (Fin.ext (vcell_unique hb h j hy hv₀))]
    exact (hcell v₀).trans (ite_eq_left hv₀).le
  · -- `V_i` lies in none of the vertical intervals
    rw [Finset.sum_eq_zero fun v _ => hout v fun hy => hex ⟨v, hy⟩]
    exact abs_nonneg _

/-! ### The potential -/

/-- Moving one point within a block of `b` horizontal intervals changes `Z` by at most `b/b^h`. -/
theorem abs_Zstep_sub_le {b h j : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (V : Fin n → ℝ) {G G' : Fin n → ℤ} (i : Fin n) (hG : ∀ k, k ≠ i → G' k = G k) {m : ℤ}
    (hm : m ≤ G i ∧ G i < m + b) (hm' : m ≤ G' i ∧ G' i < m + b) :
    |Zstep ε b h j V G' - Zstep ε b h j V G| ≤ (b : ℝ) / (b : ℝ) ^ h := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- the cells of the `c`-th horizontal interval: they change only if `c` is in the block
  have hcol : ∀ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
      |osc (vcell b h j v) (endpointAvg ε V fun k => sideIdx (G' k) c) -
        osc (vcell b h j v) (endpointAvg ε V fun k => sideIdx (G k) c)| ≤
      if m ≤ ((c : ℕ) : ℤ) ∧ ((c : ℕ) : ℤ) < m + b then 1 else 0 := by
    intro c
    refine (sum_abs_osc_endpointAvg_sub_le hb h j _ ε V i fun k hk => by rw [hG k hk]).trans ?_
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hε i)).trans
      (abs_oldWeight_sideIdx_sub_le hm hm' c)
  -- the sum over all cells, divided by `b^h`
  unfold Zstep
  rw [← sub_div, abs_div, abs_of_pos (pow_pos hbR h), ← Finset.sum_sub_distrib]
  refine div_le_div_of_nonneg_right ?_ (pow_pos hbR h).le
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun c _ => ?_).trans (sum_ite_block_le (b ^ j) b m))
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (hcol c)

/-! ### The next digit -/

/-- The stage-`(j+1)` index of a point is that of one of the `b` children of its interval. -/
lemma refineIdx_mem_block {b : ℕ} (g : Fin n → ℤ) (r : Fin n → Fin b) (k : Fin n) :
    (b : ℤ) * g k ≤ refineIdx g r k ∧ refineIdx g r k < (b : ℤ) * g k + b := by
  have hr := (r k).isLt
  unfold refineIdx
  omega

/-- Changing the next digit of the point `i` does not move the other points. -/
lemma refineIdx_update_of_ne {b : ℕ} (g : Fin n → ℤ) (r : Fin n → Fin b) {i k : Fin n}
    (hk : k ≠ i) (a : Fin b) :
    refineIdx g (Function.update r i a) k = refineIdx g r k := by
  unfold refineIdx
  rw [Function.update_of_ne hk]

/-- **Step 1 of the proof of Lemma 2.6**: changing the next digit of the point `i` from
`r i` to `a` changes `Z_{j+1}` by at most `1/M`, where `M = b^{h-1}`. -/
theorem Zstep_update_le {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) (V : Fin n → ℝ) (g : Fin n → ℤ) (r : Fin n → Fin b) (i : Fin n)
    (a : Fin b) :
    |Zstep ε b h (j + 1) V (refineIdx g (Function.update r i a)) -
        Zstep ε b h (j + 1) V (refineIdx g r)| ≤ 1 / (b : ℝ) ^ (h - 1) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- `b^h = bM`
  have hpow : (b : ℝ) ^ h = b * (b : ℝ) ^ (h - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ h)]
  calc |Zstep ε b h (j + 1) V (refineIdx g (Function.update r i a)) -
          Zstep ε b h (j + 1) V (refineIdx g r)|
      ≤ (b : ℝ) / (b : ℝ) ^ h :=
        abs_Zstep_sub_le hb ε hε V i (fun k hk => refineIdx_update_of_ne g r hk a)
          (refineIdx_mem_block g r i) (refineIdx_mem_block g (Function.update r i a) i)
    _ = 1 / (b : ℝ) ^ (h - 1) := by rw [hpow, div_mul_cancel_left₀ hbR.ne', one_div]

end

end R56Audit
