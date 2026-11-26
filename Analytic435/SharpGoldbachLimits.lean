module
public import GoldbachWindowTests
public import FirstBlockBound

/-! An arithmetic characterization of decay on the whole first Goldbach
block. It applies along any sequence of eligible moduli tending to infinity. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Finset Set
open scoped Topology
namespace GoldbachSpectral435.FirstLineLimits
open GoldbachPrimitive GoldbachSieve

lemma sieve_error_decay :
    Tendsto (fun N : ℕ => 1/(N:ℝ)+(Real.log N)^2/Real.sqrt N) atTop (𝓝 0) := by
  have v := (isLittleO_log_rpow_rpow_atTop 2 (show (0:ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have w := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).add v
  simpa only [Real.sqrt_eq_rpow,Function.comp_def,Real.rpow_two,add_zero] using w

lemma distribution_zero (N : ℕ) : distribution N 0=0 := by
  unfold distribution
  have h (n : ℕ) : ¬(n:ℝ)/N<0 := not_lt.mpr (by positivity)
  simp [h]

theorem sharp_limit_of_smooth {n : ℕ→ℕ} (ng : Tendsto n atTop atTop) (he : ∀ j, Even (n j))
    (smooth : ∀ f : ℝ→ℝ, FiniteModelWeight f → Tendsto (fun j => observed (n j) f) atTop (𝓝 (mean f)))
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : Tendsto (fun j => distribution (n j) t) atTop (𝓝 t) := by
  rcases ht.1.eq_or_lt with zero|tp
  · simp [← zero,distribution_zero]
  obtain ⟨C,cp,inc⟩ := distribution_increment
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let d := min (t/8) (ε/(32*(C+1)))
  have dp : 0<d := lt_min (by positivity) (by positivity)
  have sep : 4*d≤t := by have b : d≤t/8 := min_le_left ..; linarith
  have loss := (le_div_iff₀ (show 0<32*(C+1) by positivity)).mp (show d≤ε/(32*(C+1)) from min_le_right ..)
  have sm := Metric.tendsto_nhds.mp (smooth _ (window_weight dp sep ht.2)) d dp
  have tiny := (sieve_error_decay.comp ng).eventually_lt_const dp
  filter_upwards [ng.eventually_ge_atTop (2^64),sm,tiny] with j big near small
  let N := n j
  change 1/(N:ℝ)+(Real.log N)^2/Real.sqrt N<d at small
  rw [Real.dist_eq,abs_lt] at near ⊢
  have low := (inc N big (he j) 0 (2*d) le_rfl (by positivity) (by linarith [ht.2])).2
  rw [distribution_zero,sub_zero] at low
  have high := (inc N big (he j) (t-2*d) t (by linarith) (by linarith) ht.2).2
  obtain ⟨a,b⟩ := window_mass_compare N (t:=t) dp
  obtain ⟨m,M⟩ := window_mean dp sep ht.2
  change -d<observed N (window t d)-mean (window t d) ∧ observed N (window t d)-mean (window t d)<d at near
  change -ε<distribution N t-t ∧ distribution N t-t<ε
  have err := mul_lt_mul_of_pos_left small cp
  constructor <;> nlinarith only [a,b,m,M,near.1,near.2,low,high,loss,err,mul_pos dp cp,dp]

theorem sharp_limit {n : ℕ→ℕ} [∀ j, NeZero (n j)] (h : FirstScaleDecay n)
    (ng : Tendsto n atTop atTop) (he : ∀ j, Even (n j)) (grh : ∀ j, GRH (n j))
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : Tendsto (fun j => distribution (n j) t) atTop (𝓝 t) :=
  sharp_limit_of_smooth ng he (smooth_limit h ng he grh) t ht

def SharpDecay (n : ℕ→ℕ) : Prop := ∀ ε : ℝ, 0<ε →
  ∀ᶠ j in atTop, ∀ t∈Icc (0:ℝ) 1, |distribution (n j) t-t|≤ε

theorem uniform_sharp_of_pointwise {n : ℕ→ℕ}
    (pointwise : ∀ t∈Icc (0:ℝ) 1,Tendsto (fun j => distribution (n j) t) atTop (𝓝 t)) : SharpDecay n := by
  intro ε ep
  obtain ⟨q,gap⟩ := exists_nat_one_div_lt (half_pos ep)
  let m := q+1
  have mp : 0<m := Nat.succ_pos q
  have mr : 0<(m:ℝ) := by exact_mod_cast mp
  have gap' : 1/(m:ℝ)<ε/2 := by simpa [m] using gap
  have points : ∀ᶠ j in atTop, ∀ i∈range (m+1), |distribution (n j) (i/(m:ℝ))-i/m|<ε/2 := by
    apply (eventually_all_finset _).mpr
    intro i mem
    have le : i≤m := by have := mem_range.mp mem; omega
    have hi : (i:ℝ)/m≤1 := (div_le_one mr).mpr (by exact_mod_cast le)
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (pointwise _ ⟨by positivity,hi⟩) (ε/2) (half_pos ep)
  filter_upwards [points] with j pt
  intro t ht
  let N := n j
  have s := singularSeries_pos N
  have mesh (i : ℕ) (hi : i≤m) : |primitive N (i/(m:ℝ))|≤singularSeries N*(ε/2) := by
    rw [distribution_eq,abs_mul,abs_of_pos s]
    exact mul_le_mul_of_nonneg_left (pt i (mem_range.mpr (by omega))).le s.le
  have res := between_mesh_points N m mp _ mesh t ht
  rw [distribution_eq,abs_mul,abs_of_pos s] at res
  apply le_of_mul_le_mul_left _ s
  apply res.trans
  rw [show singularSeries N/m=singularSeries N*(1/(m:ℝ)) by ring,← mul_add]
  exact mul_le_mul_of_nonneg_left (by linarith) s.le

theorem uniform_sharp {n : ℕ→ℕ} [∀ j, NeZero (n j)] (h : FirstScaleDecay n)
    (ng : Tendsto n atTop atTop) (he : ∀ j, Even (n j)) (grh : ∀ j, GRH (n j)) : SharpDecay n :=
  uniform_sharp_of_pointwise (sharp_limit h ng he grh)

/-- At the first scale the norm estimate for all original tests is equivalent
to the sharp, uniform asymptotic for all prefix counts. -/
theorem first_scale_iff_sharp {n : ℕ→ℕ} [∀ j, NeZero (n j)] (ng : Tendsto n atTop atTop)
    (he : ∀ j, Even (n j)) (grh : ∀ j, GRH (n j)) : FirstScaleDecay n ↔ SharpDecay n := by
  refine ⟨fun h => uniform_sharp h ng he grh,?_⟩
  intro sharp ε ep
  let η := ε/(1152*Real.pi)
  have et : 0<η := by dsimp [η]; positivity
  have lim := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp ng
  obtain ⟨K,big⟩ := evenEventually_large
  filter_upwards [sharp η et,lim.eventually_lt_const et,ng.eventually_ge_atTop K] with j bound small large
  let N := n j
  have v := big N large (he j)
  have s := singularSeries_pos N
  have ha := (large_parameters v).2.2
  have H (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : |primitive N t|≤singularSeries N*η := by
    rw [distribution_eq,abs_mul,abs_of_pos s]
    exact mul_le_mul_of_nonneg_left (bound t ht) s.le
  intro f hf
  obtain ⟨norm,form⟩ := FiniteDiscrepancy.exact_form N 1 zero_lt_one (he j) v (grh j) ha f hf
  rw [← form,← norm]
  simp only [one_mul]
  apply (first_scale_bound N (he j) v (grh j) ha _ H f hf).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  change 1/(N:ℝ)<η at small
  have err := mul_le_mul_of_nonneg_left small.le s.le
  have c : 576*Real.pi*(η+η)=ε := by dsimp [η]; field_simp; ring
  calc
    _ ≤ 576*Real.pi*(singularSeries N*η+singularSeries N*η) := by
      gcongr
      simpa only [mul_one_div] using err
    _ = ε*singularSeries N := by rw [← c]; ring

theorem sharp_of_exists (h : ∃ h, HypothesisS h) {n : ℕ→ℕ} [∀ j, NeZero (n j)]
    (ng : Tendsto n atTop atTop) (he : ∀ j, Even (n j)) (grh : ∀ j, GRH (n j)) : SharpDecay n :=
  (first_scale_iff_sharp ng he grh).mp (first_scale_of_exists h ng he grh)

#print axioms first_scale_iff_sharp
#print axioms sharp_of_exists
end GoldbachSpectral435.FirstLineLimits
