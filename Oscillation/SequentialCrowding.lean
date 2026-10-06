import Oscillation.DirectCounting
import Oscillation.Exponential

/-! Sequential capped occupancy. Each new point is rejected only by boundary
strips or buckets already filled by the previously exposed points. -/
namespace Oscillation.Direct
noncomputable section
open Finset MeasureTheory
open scoped ENNReal Classical
set_option maxHeartbeats 600000

/-- Number of points kept when each interior bucket has capacity q. -/
def capped {k M : ℕ} (q : ℕ) (x : Fin k → Option (Fin M)) : ℕ :=
  ∑ c, min (count x c) q

def accepted {k M : ℕ} (q : ℕ) (x : Fin k → Option (Fin M)) : Option (Fin M) → ℕ
  | none => 0
  | some c => if count x c < q then 1 else 0

lemma count_snoc {k M : ℕ} (x : Fin k → Option (Fin M)) (z : Option (Fin M)) (c : Fin M) :
    count (Fin.snoc x z) c = count x c + if z = some c then 1 else 0 := by
  have H : ∀ {l : ℕ} (y : Fin l → Option (Fin M)),
      count y c = ∑ i, if y i = some c then (1:ℕ) else 0 := by
    intro l y
    simp [count]
  rw [H,Fin.sum_univ_castSucc,H]
  simp

lemma capped_snoc {k M : ℕ} (q : ℕ) (x : Fin k → Option (Fin M)) (z : Option (Fin M)) :
    capped q (Fin.snoc x z) = capped q x + accepted q x z := by
  unfold capped
  simp_rw [count_snoc]
  cases z with
  | none => simp [accepted]
  | some a =>
    have H (c : Fin M) : min (count x c + if some a = some c then 1 else 0) q =
        min (count x c) q + if c = a then accepted q x (some a) else 0 := by
      by_cases h : c=a
      · subst c; simp only [ite_true,accepted]; split_ifs <;> omega
      · simp [h,Ne.symm h]
    simp_rw [H]
    simp [sum_add_distrib]

lemma capped_le_sample {k M : ℕ} (q : ℕ) (x : Fin k → Option (Fin M)) : capped q x ≤ k :=
  (sum_le_sum (fun c _ => min_le_left (count x c) q)).trans (sum_count_le x)

/-- The total mass of buckets full before the next draw is at most k/(qM). -/
lemma rejection_mass {k M q : ℕ} (hq : 0 < q) (hM : 0 < M)
    (p : Option (Fin M) → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hgood : ∀ c, p (some c) ≤ 1/M) {b : ℝ} (hb : 0<b)
    (hbad : p none ≤ 2/b) (hk : (k:ℝ) ≤ 2*q*M/b)
    (x : Fin k → Option (Fin M)) :
    (∑ z, p z * (1-(accepted q x z:ℝ))) ≤ 4/b := by
  let H := univ.filter (fun c => q ≤ count x c)
  have hcount : H.card*q ≤ k := by
    calc
      _ = ∑ _c ∈ H, q := by simp
      _ ≤ ∑ c ∈ H, count x c := sum_le_sum (fun c hc => (mem_filter.mp hc).2)
      _ ≤ ∑ c, count x c := sum_le_sum_of_subset_of_nonneg (subset_univ H) (by intros; omega)
      _ ≤ k := sum_count_le x
  have hcR : (H.card:ℝ)*q ≤ k := by exact_mod_cast hcount
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hMR : (0:ℝ)<M := by exact_mod_cast hM
  have hcard : (H.card:ℝ) ≤ 2*M/b := by
    apply (mul_le_mul_iff_left₀ hqR).mp
    calc
      _ = (H.card:ℝ)*q := by ring
      _ ≤ k := hcR
      _ ≤ 2*q*M/b := hk
      _ = _ := by ring
  have he : (∑ z, p z*(1-(accepted q x z:ℝ))) = p none + ∑ c ∈ H, p (some c) := by
    rw [Fintype.sum_option]
    simp only [accepted,Nat.cast_zero,sub_zero,mul_one]
    congr 1
    simp only [sum_filter,H,mem_filter,mem_univ,true_and]
    apply sum_congr rfl
    intro c _
    split_ifs <;> norm_num at * <;> omega
  rw [he]
  calc
    _ ≤ 2/b + ∑ _c ∈ H, (1:ℝ)/M := add_le_add hbad (sum_le_sum (fun c _ => hgood c))
    _ = 2/b + H.card/M := by simp; ring
    _ ≤ 4/b := by
      have H := div_le_div_of_nonneg_right hcard hMR.le
      have he : 2*(M:ℝ)/b/M=2/b := by field_simp
      rw [he] at H
      have hr : 2/b+2/b=4/b := by ring
      linarith

/-- One sequential exponential-moment step, for an arbitrary previous sample. -/
lemma capped_exp_step {k M q : ℕ} (hq : 0<q) (hM : 0<M)
    (p : Option (Fin M) → ℝ) (hp : ∀ z, 0≤p z) (htotal : ∑ z,p z=1)
    (hgood : ∀ c, p (some c)≤1/M) {b : ℝ} (hb : 4<b)
    (hbad : p none≤2/b) (hk : (k:ℝ)≤2*q*M/b) (x : Fin k → Option (Fin M)) :
    (∑ z, p z * Real.exp (Real.log (b/4)*(1-(accepted q x z:ℝ)))) ≤ 2 := by
  have he (z : Option (Fin M)) : Real.exp (Real.log (b/4)*(1-(accepted q x z:ℝ))) =
      1+(b/4-1)*(1-(accepted q x z:ℝ)) := by
    cases z with
    | none => simp [accepted,Real.exp_log (show 0<b/4 by positivity)]
    | some c => by_cases h : count x c < q <;> simp [accepted,h,Real.exp_log (show 0<b/4 by positivity)]
  simp_rw [he,mul_add,mul_one]
  rw [sum_add_distrib,htotal]
  have hr := rejection_mass hq hM p hp hgood (by linarith) hbad hk x
  have H := mul_le_mul_of_nonneg_left hr (show 0≤b/4-1 by linarith)
  have halg : (∑ z,p z*((b/4-1)*(1-(accepted q x z:ℝ)))) =
      (b/4-1)*∑ z,p z*(1-(accepted q x z:ℝ)) := by rw [mul_sum]; congr 1; funext z; ring
  rw [halg]
  have hid : (b/4-1)*(4/b) = 1-4/b := by field_simp <;> ring
  rw [hid] at H
  have : 0≤4/b := by positivity
  linarith

lemma weighted_snoc_sum {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (k : ℕ)
    (f : (Fin (k+1) → Ω) → ℝ) :
    (∑ x,productWeight p x*f x) = ∑ x : Fin k → Ω, productWeight p x *
      ∑ z, p z*f (Fin.snoc x z) := by
  let e : ((Fin k → Ω) × Ω) ≃ (Fin (k+1) → Ω) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Ω))
  rw [← e.sum_comp, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro z _
  change productWeight p (Fin.snoc x z)*f (Fin.snoc x z)=_
  simp only [productWeight,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  ring

/-- Repeatedly expose one new point. The capacity is fixed using the final n. -/
lemma capped_exp_bound {n M q : ℕ} (hq : 0<q) (hM : 0<M)
    (p : Option (Fin M) → ℝ) (hp : ∀ z, 0≤p z) (htotal : ∑ z,p z=1)
    (hgood : ∀ c, p (some c)≤1/M) {b : ℝ} (hb : 4<b)
    (hbad : p none≤2/b) (hn : (n:ℝ)≤2*q*M/b) :
    (∑ x : Fin n → Option (Fin M),productWeight p x *
      Real.exp (Real.log (b/4)*(n-(capped q x:ℝ)))) ≤ 2^n := by
  suffices H : ∀ k≤n, (∑ x : Fin k → Option (Fin M),productWeight p x *
      Real.exp (Real.log (b/4)*(k-(capped q x:ℝ)))) ≤ 2^k from H n le_rfl
  intro k
  induction k with
  | zero => intro _; simp [capped,count,productWeight]
  | succ k ih =>
    intro hk
    rw [weighted_snoc_sum]
    have hkn : (k:ℝ)≤n := by exact_mod_cast (show k≤n by omega)
    have hstep (x : Fin k → Option (Fin M)) :
        (∑ z, p z * Real.exp (Real.log (b/4)*((k+1:ℕ)-(capped q (Fin.snoc x z):ℝ)))) ≤
        Real.exp (Real.log (b/4)*(k-(capped q x:ℝ)))*2 := by
      simp_rw [capped_snoc,Nat.cast_add,Nat.cast_one]
      have he (z) : Real.log (b/4)*((k:ℝ)+1-((capped q x:ℝ)+(accepted q x z:ℝ))) =
          Real.log (b/4)*(k-(capped q x:ℝ))+Real.log (b/4)*(1-(accepted q x z:ℝ)) := by ring
      simp_rw [he,Real.exp_add]
      have he' : (∑ z,p z*(Real.exp (Real.log (b/4)*(k-(capped q x:ℝ)))*
          Real.exp (Real.log (b/4)*(1-(accepted q x z:ℝ))))) =
          Real.exp (Real.log (b/4)*(k-(capped q x:ℝ)))*
            ∑ z,p z*Real.exp (Real.log (b/4)*(1-(accepted q x z:ℝ))) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      rw [he']
      exact mul_le_mul_of_nonneg_left (capped_exp_step hq hM p hp htotal hgood hb hbad (hkn.trans hn) x) (Real.exp_nonneg _)
    calc
      _ ≤ ∑ x : Fin k → Option (Fin M), productWeight p x *
          (Real.exp (Real.log (b/4)*(k-(capped q x:ℝ)))*2) :=
        sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hstep x) (prod_nonneg (fun i _=>hp (x i))))
      _ = (∑ x : Fin k → Option (Fin M),productWeight p x*Real.exp (Real.log (b/4)*(k-(capped q x:ℝ))))*2 := by
        rw [sum_mul]; apply sum_congr rfl; intros; ring
      _ ≤ 2^k*2 := mul_le_mul_of_nonneg_right (ih (by omega)) (by norm_num)
      _ = _ := (pow_succ _ _).symm


lemma capped_sqrt_bound {n M q : ℕ} {v : ℝ} (hv : 0≤v) (hq : (q:ℝ)≤v^2)
    (x : Fin n → Option (Fin M)) :
    (capped q x:ℝ) ≤ v * ∑ c,Real.sqrt (count x c) := by
  have hqr := Real.sqrt_nonneg (q:ℝ)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) q)
  have hqv : Real.sqrt (q:ℝ)≤v := by nlinarith
  rw [capped,Nat.cast_sum,mul_sum]
  apply sum_le_sum
  intro c _
  have hmr := Real.sqrt_nonneg (count x c:ℝ)
  have hms := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) (count x c))
  by_cases hm : count x c ≤ q
  · rw [min_eq_left hm]
    have hr := (Real.sqrt_le_sqrt (show (count x c:ℝ)≤q by exact_mod_cast hm)).trans hqv
    nlinarith
  · rw [min_eq_right (by omega)]
    have hr := Real.sqrt_le_sqrt (show (q:ℝ)≤count x c by exact_mod_cast (show q≤count x c by omega))
    nlinarith [mul_le_mul hqv hr hqr hv]

/-- The sequential cap yields an exponential bound on the square-root mass. -/
theorem sequential_mass_exp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {n M : ℕ}
    [MeasurableSpace (Option (Fin M))] [MeasurableSingletonClass (Option (Fin M))] (hn : 0<n) (hM : 0<M) (hMn : M≤n)
    {b : ℝ} (hb : 4<b) (cell : α → Option (Fin M)) (hcell : Measurable cell)
    (hgood : ∀ c,μ.real {z | cell z=some c}≤1/M)
    (hbad : μ.real {z | cell z=none}≤2/b) :
    (∫ P : Fin n → α,Real.exp (Real.log (b/4)*
        (n-Real.sqrt (b*n/M)*bucketSquareRootSum cell P)) ∂Measure.pi (fun _ => μ)) ≤ 2^n := by
  let q := Nat.ceil (b*n/(2*M))
  let p := bucketProbability μ cell
  have hb0 : 0<b := by linarith
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hMR : (0:ℝ)<M := by exact_mod_cast hM
  have hx : 1≤b*n/(2*M) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hMnR : (M:ℝ)≤n := by exact_mod_cast hMn
    nlinarith
  have hqlo : b*n/(2*M)≤q := Nat.le_ceil _
  have hqhi : (q:ℝ)≤b*n/M := by
    have H := Nat.ceil_lt_add_one (show 0≤b*n/(2*M) by positivity)
    dsimp [q]
    linarith [show b*n/M=2*(b*n/(2*M)) by ring]
  have hq : 0<q := by
    have H : (0:ℝ)<q := lt_of_lt_of_le (by positivity : 0<b*n/(2*M)) hqlo
    exact_mod_cast H
  have hfull : (n:ℝ)≤2*q*M/b := by
    have H := (div_le_iff₀ (show 0<(2:ℝ)*M by positivity)).mp hqlo
    apply (le_div_iff₀ hb0).mpr
    nlinarith
  have ht : ∑ z,p z=1 := by
    have H := sum_measureReal_preimage_singleton (μ:=μ) (univ : Finset (Option (Fin M)))
      (f:=cell) (fun z _ => hcell (measurableSet_singleton z))
    simpa [p,bucketProbability,measureReal_def,Set.preimage] using H
  have he := capped_exp_bound hq hM p (fun _=>ENNReal.toReal_nonneg) ht hgood hb hbad hfull
  change (∫ P : Fin n → α, Real.exp (Real.log (b/4)*
    (n-Real.sqrt (b*n/M)*(∑ c, Real.sqrt (count (fun i => cell (P i)) c))))
    ∂Measure.pi (fun _ => μ)) ≤ 2^n
  rw [integral_iid_buckets μ cell hcell n (fun x : Fin n → Option (Fin M) => Real.exp (Real.log (b/4)*(n-Real.sqrt (b*n/M)*(∑ c, Real.sqrt (count x c)))))]
  apply le_trans _ he
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun _ _=>ENNReal.toReal_nonneg))
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by linarith : 1≤b/4))
  have H := capped_sqrt_bound (Real.sqrt_nonneg (b*n/M))
    (by rw [Real.sq_sqrt (show 0≤b*n/M by positivity)]; exact hqhi) x
  change (n:ℝ)-Real.sqrt (b*n/M)*(∑ c,Real.sqrt (count x c)) ≤ n-(capped q x:ℝ)
  linarith

end
end Oscillation.Direct
