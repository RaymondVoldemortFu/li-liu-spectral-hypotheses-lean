module
public import BandPNT
public import PhysicalAP
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The principal von Mangoldt sum with a smooth, compact physical test. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Chebyshev MeasureTheory Finset Filter Asymptotics
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve

def primeSum (M : ℕ) (f : ℝ→ℝ) := ∑ n∈range M, weightedMangoldt M n f

private lemma endpoint {f : ℝ→ℝ} (hf : FiniteModelWeight f) : f 1=0 := by
  by_contra nz
  exact lt_irrefl 1 (hf.mem_support_unit nz).2

lemma primeSum_integral (M : ℕ) (mp : 0<M) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    primeSum M f/M= -(∫ u in (0:ℝ)..1, deriv f u*(psi (M*u)/M)) := by
  let m := (M:ℝ)
  have mr : 0<m := Nat.cast_pos.mpr mp
  let F := fun x : ℝ => f (x/m)
  have der (x : ℝ) : HasDerivAt F (deriv f (x/m)/m) x := by
    simpa [F,Function.comp_def,div_eq_mul_inv] using ((hf.smooth.differentiable (by decide) (x/m)).hasDerivAt.comp x
      ((hasDerivAt_id x).div_const m))
  have dc := hf.smooth.continuous_deriv (by decide)
  have derivF : deriv F=fun x : ℝ => deriv f (x/m)/m := funext fun x => (der x).deriv
  have cont : Continuous (deriv F) := by rw [derivF]; exact (dc.comp (continuous_id.div_const _)).div_const _
  have ab := sum_mul_eq_sub_integral_mul' (f:=F) mangoldt M (fun x _ => (der x).differentiableAt)
    cont.integrableOn_Icc
  have ed : F M=0 := by dsimp only [F]; change f (m/m)=0; rw [div_self mr.ne',endpoint hf]
  have e : (∑ n∈Finset.Icc 0 M,F n*mangoldt n)=primeSum M f := by
    rw [← Nat.range_succ_eq_Icc_zero,Finset.sum_range_succ,ed,zero_mul,add_zero]
    exact sum_congr rfl (fun n _ => mul_comm ..)
  rw [e,ed,zero_mul,zero_sub,derivF] at ab
  simp_rw [← psi_eq_sum_Icc] at ab
  let g := fun x : ℝ => deriv f (x/m)/m*psi x
  have changeVar := intervalIntegral.smul_integral_comp_mul_left (a:=(0:ℝ)) (b:=1) g m
  simp only [smul_eq_mul,mul_zero,mul_one] at changeVar
  have eq (u : ℝ) : g (m*u)=deriv f u*(psi (m*u)/m) := by
    dsimp [g]
    rw [mul_div_cancel_left₀ _ mr.ne']
    ring
  change primeSum M f= -(∫ t in Set.Ioc (0:ℝ) m,g t) at ab
  rw [← intervalIntegral.integral_of_le mr.le,← changeVar] at ab
  simp_rw [eq] at ab
  rw [ab]
  rw [neg_div,mul_div_cancel_left₀ _ mr.ne']

lemma integral_by_parts (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    (∫ u in (0:ℝ)..1, deriv f u*u)= -(∫ u in (0:ℝ)..1, f u) := by
  have parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (u:=fun t : ℝ => t) (u':=fun _ => (1:ℝ)) (v:=f) (v':=deriv f)
    continuous_id.continuousOn hf.continuous.continuousOn (fun t _ => hasDerivAt_id t)
    (fun t _ => (hf.smooth.differentiable (by decide) t).hasDerivAt) (by simp) ((hf.smooth.continuous_deriv (by decide)).intervalIntegrable ..)
  simp only [endpoint hf,mul_zero,zero_mul,sub_zero,zero_sub,one_mul] at parts
  simpa only [mul_comm] using parts

theorem primeSum_limit (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    Tendsto (fun M : ℕ => primeSum M f/M) atTop (𝓝 (∫ u in (0:ℝ)..1,f u)) := by
  let μ := volume.restrict (Set.Ioc (0:ℝ) 1)
  let A := fun (M : ℕ) (u : ℝ) => deriv f u*(psi (M*u)/M)
  let F := fun u : ℝ => deriv f u*u
  let K := Real.log 4+4
  have kp : 0<K := by dsimp [K]; positivity
  have dc := hf.smooth.continuous_deriv (by decide)
  have psiLimit : Tendsto (fun x : ℝ => psi x/x) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (eventually_ne_atTop (0:ℝ))).mp WeakPNT''
  have conv : Tendsto (fun M : ℕ => ∫ u,A M u ∂μ) atTop (𝓝 (∫ u,F u ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun u => |deriv f u| * K)
    · intro M
      exact (dc.measurable.mul ((psi_mono.measurable.comp (measurable_const.mul measurable_id)).div_const _)).aestronglyMeasurable
    · exact ((dc.abs.mul continuous_const).intervalIntegrable 0 1).1
    · intro M
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with u hu
      have up := hu.1
      have ub := hu.2
      simp only [A,Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg (psi_nonneg _) (Nat.cast_nonneg _))]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      by_cases zero : M=0
      · simp [zero,kp.le]
      have mr : 0<(M:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero zero)
      apply (div_le_iff₀ mr).mpr
      exact (psi_le_const_mul_self (mul_nonneg mr.le up.le)).trans (by
        change K*((M:ℝ)*u)≤K*M
        nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ub mr.le) kp.le])
    · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with u hu
      have up := hu.1
      have growth : Tendsto (fun M : ℕ => (M:ℝ)*u) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const up
      have lim := ((psiLimit.comp growth).mul_const u).const_mul (deriv f u)
      simp only [one_mul] at lim
      apply lim.congr' _
      filter_upwards [eventually_ge_atTop (1:ℕ)] with M mp
      have mr : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
      change deriv f u*(psi ((M:ℝ)*u)/((M:ℝ)*u)*u)=_
      dsimp [A]
      field_simp
  have parts := integral_by_parts f hf
  have same : -(∫ u,F u ∂μ)=∫ u in (0:ℝ)..1,f u := by
    dsimp only [μ,F]
    rw [← intervalIntegral.integral_of_le zero_le_one]
    simpa only [mul_comm,neg_neg] using congrArg Neg.neg parts
  rw [← same]
  apply conv.neg.congr' _
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M mp
  simpa only [μ,A,intervalIntegral.integral_of_le zero_le_one] using (primeSum_integral M mp f hf).symm

#print axioms primeSum_limit
end GoldbachSpectral435.GoldbachSieve
