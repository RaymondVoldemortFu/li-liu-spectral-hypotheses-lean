module
public import PrimePairVariation
public import SharpGoldbachLimits

/-! Actual ordered prime representations with a sharp endpoint in the
first summand and the usual Hardy--Littlewood normalization. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset Set
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open FirstLineLimits GoldbachPrimitive

def prefixIndices (N : ℕ) (t : ℝ) := (range N).filter (fun n : ℕ => (n:ℝ)/N<t)

def primeCount (N : ℕ) (t : ℝ) : ℕ :=
  ((prefixIndices N t).filter (fun n => n.Prime ∧ (N-n).Prime)).card

def primeDistribution (N : ℕ) (t : ℝ) : ℝ :=
  (Real.log N)^2*(primeCount N t:ℝ)/((N:ℝ)*singularSeries N)

private lemma raw_prefix (N : ℕ) (t : ℝ) :
    distribution N t=(∑ n∈prefixIndices N t, rawMass N n)/((N:ℝ)*singularSeries N) := by
  unfold distribution
  rw [← sum_filter]
  have eq (n : ℕ) : mass N n=rawMass N n/N := by unfold mass rawMass; split <;> simp
  simp_rw [eq]
  rw [← sum_div,div_div]
  rfl

theorem distribution_comparison :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 2^64≤N → Even N → ∀ t : ℝ,
      |distribution N t-primeDistribution N t|≤C*(1/Real.log N+(Real.log N)^2/Real.sqrt N) := by
  obtain ⟨C,cp,err⟩ := variation_bound
  refine ⟨C,cp,?_⟩
  intro N big ev t
  let I := prefixIndices N t
  let L := Real.log (N:ℝ)
  let S := singularSeries N
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have sp : 0<S := singularSeries_pos N
  have one : 1≤S := (singularSeries_gt_one N).le
  have rp := Real.sqrt_pos.mpr np
  have sq := Real.sq_sqrt np.le
  have lh : 0<L := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have count : (primeCount N t:ℝ)=∑ n∈I, pairIndicator N n := by simp [primeCount,I,pairIndicator,sum_boole]
  rw [raw_prefix,primeDistribution,count,mul_sum,← sub_div,abs_div,abs_of_pos (mul_pos np sp)]
  apply (div_le_iff₀ (mul_pos np sp)).mpr
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => abs_nonneg _)).trans
  apply (err N big ev).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ cp.le
  change (N:ℝ)*S/L+Real.sqrt N*L^2≤(1/L+L^2/Real.sqrt N)*(N*S)
  have lift := mul_le_mul_of_nonneg_left one (show 0≤Real.sqrt N*L^2 by positivity)
  calc
    _ ≤ (N:ℝ)*S/L+Real.sqrt N*L^2*S := by linarith only [lift]
    _ = _ := by
      have term : L^2/Real.sqrt N*((N:ℝ)*S)=Real.sqrt N*L^2*S := calc
        _ = L^2/Real.sqrt N*((Real.sqrt N)^2*S) := by rw [sq]
        _ = _ := by field_simp
      rw [add_mul,term]
      ring

def PrimeCountDecay (n : ℕ→ℕ) : Prop := ∀ ε : ℝ, 0<ε →
  ∀ᶠ j in atTop, ∀ t∈Icc (0:ℝ) 1, |primeDistribution (n j) t-t|≤ε

theorem sharp_iff_prime {n : ℕ→ℕ} (ng : Tendsto n atTop atTop) (he : ∀ j, Even (n j)) :
    SharpDecay n ↔ PrimeCountDecay n := by
  obtain ⟨C,cp,bound⟩ := distribution_comparison
  have r := (isLittleO_log_rpow_rpow_atTop 2 (show (0:ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero.comp
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp ng)
  have l := Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp ng)
  have inv : Tendsto (fun j => 1/Real.log (n j)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop l
  have decay : Tendsto (fun j => C*(1/Real.log (n j)+(Real.log (n j))^2/Real.sqrt (n j))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow,Function.comp_def,Real.rpow_two,add_zero,mul_zero] using ((inv.add r).const_mul C)
  constructor <;> intro h ε ep <;>
    filter_upwards [h (ε/2) (half_pos ep),decay.eventually_lt_const (half_pos ep),ng.eventually_ge_atTop (2^64)] with j h small big <;>
    intro t ht
  · have a := (bound (n j) big (he j) t).trans small.le
    have b := h t ht
    rw [abs_sub_comm] at a
    exact (abs_sub_le _ (distribution (n j) t) _).trans (by linarith)
  · have a := (bound (n j) big (he j) t).trans small.le
    have b := h t ht
    exact (abs_sub_le _ (primeDistribution (n j) t) _).trans (by linarith)

/-- The whole first-scale estimate is equivalent to the usual sharp
asymptotic for genuine prime representations, uniformly in the endpoint. -/
theorem first_scale_iff_prime {n : ℕ→ℕ} [∀ j, NeZero (n j)] (ng : Tendsto n atTop atTop)
    (he : ∀ j, Even (n j)) (grh : ∀ j, GRH (n j)) : FirstScaleDecay n ↔ PrimeCountDecay n :=
  (first_scale_iff_sharp ng he grh).trans (sharp_iff_prime ng he)

theorem prime_counts_of_exists (h : ∃ h, HypothesisS h) {n : ℕ→ℕ} [∀ j, NeZero (n j)]
    (ng : Tendsto n atTop atTop) (he : ∀ j, Even (n j)) (grh : ∀ j, GRH (n j)) : PrimeCountDecay n :=
  (first_scale_iff_prime ng he grh).mp (first_scale_of_exists h ng he grh)

#print axioms distribution_comparison
#print axioms first_scale_iff_prime
#print axioms prime_counts_of_exists
end GoldbachSpectral435.GoldbachSieve
