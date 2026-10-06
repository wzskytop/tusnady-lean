import Oscillation.HistogramTransport
import Mathlib.Data.Fintype.Powerset
import Mathlib.MeasureTheory.Measure.Real

namespace Oscillation.Direct
noncomputable section
open MeasureTheory Finset
open scoped ENNReal Classical

/-- Direct subset counting: at least half of the iid points in a region of mass at most q. -/
theorem half_sample_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (n : ℕ) (s : Set α) {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hs : μ.real s ≤ q) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {P | n ≤ 2 * (univ.filter (fun i => P i ∈ s)).card} ≤
      2^n * (Real.sqrt q)^n := by
  classical
  let E (t : Finset (Fin n)) : Set (Fin n → α) :=
    {P | n ≤ 2*t.card ∧ ∀ i ∈ t, P i ∈ s}
  have hsub : {P : Fin n → α | n ≤ 2 * (univ.filter (fun i => P i ∈ s)).card} ⊆ ⋃ t, E t := by
    intro P hP
    exact Set.mem_iUnion.mpr ⟨univ.filter (fun i => P i ∈ s), hP,
      fun i hi => (mem_filter.mp hi).2⟩
  have ht (t : Finset (Fin n)) : (Measure.pi (fun _ : Fin n => μ)).real (E t) ≤
      (Real.sqrt q)^n := by
    by_cases hn : n ≤ 2*t.card
    · have he : E t = (t : Set (Fin n)).pi (fun _ => s) := by
        ext P; simp [E, hn, Set.mem_pi]
      rw [he, measureReal_def, Measure.pi_pi_finset, ENNReal.toReal_prod]
      simp only [prod_const]
      calc
        (μ s).toReal ^ t.card ≤ q^t.card := pow_le_pow_left₀ ENNReal.toReal_nonneg hs _
        _ = (Real.sqrt q)^(2*t.card) := by rw [pow_mul, Real.sq_sqrt hq.le]
        _ ≤ (Real.sqrt q)^n := pow_le_pow_of_le_one (Real.sqrt_nonneg _) ((Real.sqrt_le_one).mpr hq1) hn
    · have he : E t = ∅ := by ext P; simp [E, hn]
      simp only [he, measureReal_empty]; positivity
  calc
    _ ≤ (Measure.pi (fun _ : Fin n => μ)).real (⋃ t, E t) := measureReal_mono hsub
    _ ≤ ∑ t, (Measure.pi (fun _ : Fin n => μ)).real (E t) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _t : Finset (Fin n), (Real.sqrt q)^n := sum_le_sum (fun t _ => ht t)
    _ = _ := by simp

/-- Counts of the finite interior buckets. -/
def count {n M : ℕ} (x : Fin n → Option (Fin M)) (c : Fin M) : ℕ :=
  (univ.filter (fun i => x i = some c)).card

def heavy {n M : ℕ} (b : ℝ) (x : Fin n → Option (Fin M)) : Finset (Fin M) :=
  univ.filter (fun c => b*n/M < (count x c : ℝ))

def exceptional {M : ℕ} (H : Finset (Fin M)) : Set (Option (Fin M)) :=
  {c | c = none ∨ ∃ a ∈ H, c = some a}

lemma sum_count_le {n M : ℕ} (x : Fin n → Option (Fin M)) :
    (∑ c, count x c) ≤ n := by
  have h := histogram_count_sum (histogram x)
  rw [Fintype.sum_option] at h
  simp_rw [histogramCount_eq_card] at h
  dsimp [count]
  omega

lemma heavy_card {n M : ℕ} (hn : 0 < n) (hM : 0 < M) {b : ℝ} (hb : 0 < b)
    (x : Fin n → Option (Fin M)) : (heavy b x).card ≤ (M:ℝ)/b := by
  classical
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hc : (heavy b x).card * (b*n/M) ≤ n := by
    calc
      _ = ∑ _c ∈ heavy b x, b*n/M := by simp
      _ ≤ ∑ c ∈ heavy b x, (count x c : ℝ) := sum_le_sum (fun c hc => (mem_filter.mp hc).2.le)
      _ ≤ ∑ c, (count x c : ℝ) := sum_le_univ_sum_of_nonneg (fun _ => by positivity)
      _ ≤ n := by exact_mod_cast sum_count_le x
  have hc' := (div_le_iff₀ hm).mp (show (heavy b x).card*b*n/M ≤ n by convert hc using 1 <;> ring)
  apply (le_div_iff₀ hb).mpr
  nlinarith

/-- At least half the sample outside the exceptional union implies a square-root mass gain. -/
lemma mass_gain {n M : ℕ} (hn : 0 < n) (hM : 0 < M) {b : ℝ} (hb : 0 < b)
    (x : Fin n → Option (Fin M))
    (hgood : 2 * (univ.filter (fun i => x i ∈ exceptional (heavy b x))).card ≤ n) :
    n / (2 * Real.sqrt (b*n/M)) ≤ ∑ c, Real.sqrt (count x c) := by
  classical
  let H := heavy b x
  let f : Option (Fin M) → ℝ := fun c => if c ∈ exceptional H then 0 else 1
  have hsum := sum_sample_eq_counts x f
  have hcount : (∑ i, f (x i)) = n - (univ.filter (fun i => x i ∈ exceptional H)).card := by
    have he := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => x i ∈ exceptional H)
    simp only [card_univ, Fintype.card_fin] at he
    have heR : ((univ.filter (fun i => x i ∈ exceptional H)).card : ℝ) +
        (univ.filter (fun i => ¬x i ∈ exceptional H)).card = n := by exact_mod_cast he
    have hf (i : Fin n) : f (x i) = if ¬x i ∈ exceptional H then 1 else 0 := by simp [f]
    simp_rw [hf]
    rw [sum_boole]
    linarith
  have hout : (n:ℝ)/2 ≤ ∑ c ∈ univ.filter (fun c => c ∉ H), (count x c : ℝ) := by
    have he (c : Fin M) : (some c : Option (Fin M)) ∈ exceptional H ↔ c ∈ H := by simp [exceptional]
    have hfnone : f none = 0 := by simp [f, exceptional]
    have hfsome (c : Fin M) : f (some c) = if c ∈ H then 0 else 1 := by simp only [f, he]
    rw [Fintype.sum_option, hfnone, mul_zero, zero_add] at hsum
    simp_rw [hfsome, histogramCount_eq_card, mul_ite, mul_zero, mul_one] at hsum
    change (∑ i, f (x i)) = ∑ c, if c ∈ H then 0 else (count x c : ℝ) at hsum
    rw [hcount] at hsum
    have he' : (∑ c, if c ∈ H then (0:ℝ) else (count x c : ℝ)) =
        ∑ c ∈ univ.filter (fun c => c ∉ H), (count x c : ℝ) := by simp [sum_filter]
    rw [he'] at hsum
    have hg : 2 * ((univ.filter (fun i => x i ∈ exceptional H)).card : ℝ) ≤ n := by exact_mod_cast hgood
    linarith
  have hroot : 0 < Real.sqrt (b*n/M) := Real.sqrt_pos.mpr (by positivity)
  have hc (c : Fin M) (hc : c ∈ univ.filter (fun c => c ∉ H)) :
      (count x c : ℝ) ≤ Real.sqrt (count x c) * Real.sqrt (b*n/M) := by
    have hcap : (count x c : ℝ) ≤ b*n/M := by
      have hnot := (mem_filter.mp hc).2
      simpa [H, heavy, not_lt] using hnot
    have hs := Real.sqrt_le_sqrt hcap
    have he := Real.sq_sqrt (show (0:ℝ) ≤ count x c by positivity)
    nlinarith [Real.sqrt_nonneg (count x c)]
  have hbound : (n:ℝ)/2 ≤ (∑ c, Real.sqrt (count x c)) * Real.sqrt (b*n/M) := by
    calc
      _ ≤ ∑ c ∈ univ.filter (fun c => c ∉ H), (count x c : ℝ) := hout
      _ ≤ ∑ c ∈ univ.filter (fun c => c ∉ H), Real.sqrt (count x c) * Real.sqrt (b*n/M) := sum_le_sum hc
      _ ≤ ∑ c, Real.sqrt (count x c) * Real.sqrt (b*n/M) := sum_le_univ_sum_of_nonneg (fun _ => by positivity)
      _ = _ := by rw [sum_mul]
  apply (div_le_iff₀ (mul_pos (by norm_num) hroot)).mpr
  nlinarith

/-- The exceptional region has mass at most 3/b, for every fixed small bucket collection. -/
lemma exceptional_mass {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {M : ℕ} (hM : 0 < M) {b : ℝ} (hb : 0 < b)
    (cell : α → Option (Fin M))
    (hinterior : ∀ c, μ.real {z | cell z = some c} ≤ 1/M)
    (hboundary : μ.real {z | cell z = none} ≤ 2/b)
    (H : Finset (Fin M)) (hH : (H.card:ℝ) ≤ M/b) :
    μ.real {z | cell z ∈ exceptional H} ≤ 3/b := by
  have he : {z | cell z ∈ exceptional H} =
      {z | cell z = none} ∪ ⋃ c ∈ H, {z | cell z = some c} := by
    ext z; simp [exceptional]
  rw [he]
  calc
    _ ≤ μ.real {z | cell z = none} + μ.real (⋃ c ∈ H, {z | cell z = some c}) := measureReal_union_le _ _
    _ ≤ 2/b + ∑ c ∈ H, μ.real {z | cell z = some c} :=
      add_le_add hboundary (measureReal_biUnion_finset_le H _)
    _ ≤ 2/b + H.card/M := by
      gcongr
      calc
        _ ≤ ∑ _c ∈ H, (1:ℝ)/M := sum_le_sum (fun c _ => hinterior c)
        _ = _ := by simp; ring
    _ ≤ 3/b := by
      have hm : (0:ℝ) < M := by exact_mod_cast hM
      have hc := div_le_div_of_nonneg_right hH hm.le
      have hid : (M:ℝ)/b/M = 1/b := by field_simp
      rw [hid] at hc
      calc
        _ ≤ 2/b + 1/b := add_le_add_right hc _
        _ = _ := by ring

/-- A direct occupancy lower-tail bound, with no histogram enumeration or Laplace estimate. -/
theorem bucket_mass_small {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {n M : ℕ} (hn : 0 < n) (hM : 0 < M) (hMn : M ≤ n)
    {b : ℝ} (hb : 3 ≤ b) (cell : α → Option (Fin M))
    (hinterior : ∀ c, μ.real {z | cell z = some c} ≤ 1/M)
    (hboundary : μ.real {z | cell z = none} ≤ 2/b) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {P | bucketSquareRootSum cell P < n / (2 * Real.sqrt (b*n/M))} ≤
      (4 * Real.sqrt (3/b))^n := by
  have hb0 : 0 < b := by linarith
  let E (H : Finset (Fin M)) : Set (Fin n → α) :=
    {P | (H.card:ℝ) ≤ M/b ∧ n ≤ 2 * (univ.filter (fun i => cell (P i) ∈ exceptional H)).card}
  have hsub : {P | bucketSquareRootSum cell P < n / (2 * Real.sqrt (b*n/M))} ⊆ ⋃ H, E H := by
    intro P hP
    let x := fun i => cell (P i)
    refine Set.mem_iUnion.mpr ⟨heavy b x, heavy_card hn hM hb0 x, ?_⟩
    by_contra hbad
    have hg := mass_gain hn hM hb0 x (Nat.le_of_lt (Nat.lt_of_not_ge hbad))
    have he : (∑ c, Real.sqrt (count x c)) = bucketSquareRootSum cell P := rfl
    rw [he] at hg
    exact (not_lt.mpr hg) hP
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

end
end Oscillation.Direct
