module
public import TruncatedSingular
public import SingleScaleCriterion

/-! One logarithmic prime cutoff suffices for all local factors up to the
complete finite horizon prescribed by the original norm criterion. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open PhysicalTests

def localCutoff (N : ℕ) := ⌊Real.log (N:ℝ)/64⌋₊

lemma cutoff_grows : Tendsto localCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).atTop_div_const (by norm_num : (0:ℝ)<64))

theorem cutoff_horizon (N : ℕ) (np : 0<N) (big : 128≤localCutoff N) :
    (primorial (localCutoff N):ℝ)^3≤Real.sqrt N ∧
    ∀ H : ℕ, 0<H → H≤2*scale N*N →
      Real.log H≤2304*(localCutoff N:ℝ)*Real.log (localCutoff N) := by
  let L := Real.log (N:ℝ)
  let z := localCutoff N
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have l0 : 0≤L := Real.log_nonneg (by exact_mod_cast np : (1:ℝ)≤N)
  have low : (z:ℝ)≤L/64 := Nat.floor_le (by positivity)
  have high : L/64<(z:ℝ)+1 := Nat.lt_floor_add_one _
  have zr : (128:ℝ)≤z := by exact_mod_cast big
  have zp : 0<(z:ℝ) := by linarith
  have lp : 0<L := by linarith
  have x : L≤128*z := by linarith
  have zlog : 1≤Real.log (z:ℝ) := (Real.le_log_iff_exp_le zp).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have llog : 1≤Real.log L := (Real.le_log_iff_exp_le lp).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have c : Real.log L≤2*Real.log z := by
    have b := Real.log_le_log lp (x.trans (show 128*(z:ℝ)≤(z:ℝ)^2 by nlinarith only [mul_le_mul_of_nonneg_right zr zp.le]))
    rwa [Real.log_pow] at b
  have qpos : 0<((primorial z):ℝ) := by exact_mod_cast primorial_pos z
  have lq : Real.log (primorial z)≤2*z := by
    have h := Real.log_le_log qpos (show (primorial z:ℝ)≤(4:ℝ)^z by exact_mod_cast (primorial_lt_four_pow z (by omega : z≠0)).le)
    rw [Real.log_pow] at h
    have four : Real.log 4≤2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith only [h,mul_le_mul_of_nonneg_left four zp.le]
  constructor
  · apply (sq_le_sq₀ (pow_nonneg qpos.le _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt nr.le,← pow_mul]
    apply (Real.log_le_log_iff (pow_pos qpos _) nr).mp
    rw [Real.log_pow]
    change _≤L
    norm_num
    linarith
  · intro H hp bound
    have hr : 0<(H:ℝ) := by exact_mod_cast hp
    let X := Real.exp (horizon N)
    have HH : L≤horizon N := by
      change L≤8*L*Real.log L
      nlinarith only [mul_le_mul_of_nonneg_left llog lp.le,lp]
    have nx : (N:ℝ)≤X := by simpa only [L,Real.exp_log nr] using Real.exp_le_exp.mpr HH
    have ceilBound : (scale N:ℝ)<X/N+1 := Nat.ceil_lt_add_one (div_nonneg (Real.exp_pos _).le nr.le)
    have km := mul_le_mul_of_nonneg_right ceilBound.le nr.le
    rw [add_mul,div_mul_cancel₀ _ nr.ne',one_mul] at km
    have bc : (H:ℝ)≤4*X := by
      have br : (H:ℝ)≤2*(scale N:ℝ)*N := by exact_mod_cast bound
      linarith
    have ub := Real.log_le_log hr bc
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp] at ub
    have four : Real.log 4≤3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
    have prod := mul_le_mul x c (by linarith : 0≤Real.log L) (by positivity : 0≤128*(z:ℝ))
    change Real.log H≤2304*(z:ℝ)*Real.log z
    change Real.log H≤Real.log 4+8*L*Real.log L at ub
    nlinarith only [ub,four,prod,mul_le_mul_of_nonneg_left zlog zp.le,zr]

/-- Relative convergence is uniform in every shift entering the one-scale
criterion; the period of the cutoff sieve has cube at most sqrt(N). -/
theorem all_horizon_factors (ε : ℝ) (ep : 0<ε) :
    ∀ᶠ N : ℕ in atTop, (primorial (localCutoff N):ℝ)^3≤Real.sqrt N ∧
      ∀ H : ℕ, 0<H → H≤2*scale N*N →
      |truncatedSeries H (localCutoff N)/singularSeries H-1|≤ε := by
  filter_upwards [eventually_ge_atTop (1:ℕ),cutoff_grows.eventually_ge_atTop 128,
    cutoff_grows.eventually (truncated_series_uniform 2304 ε ep)] with N np big bound
  obtain ⟨a,b⟩ := cutoff_horizon N np big
  exact ⟨a,fun H hp hh => bound H hp (b H hp hh)⟩

#print axioms all_horizon_factors
end GoldbachSpectral435.GoldbachSieve
