module
public import Entry
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set
namespace GoldbachSpectral435

def physicalDensity (f : ℝ → ℝ) (u : ℝ) := f u/2-u*deriv f u
def physicalEnergy (f : ℝ → ℝ) : ℝ := ∫ u in Ioi (0:ℝ), (physicalDensity f u)^2

private theorem density_companion {f : ℝ → ℝ} (hf : Differentiable ℝ f) {u : ℝ} (hu : 0<u) :
    derivativeWeight f u = Real.sqrt u*physicalDensity f u := by
  have de := (Real.hasDerivAt_sqrt hu.ne').mul (hf u).hasDerivAt
  have sq := Real.sq_sqrt hu.le
  have nz := (Real.sqrt_pos.mpr hu).ne'
  unfold derivativeWeight physicalDensity companion
  have d : deriv (fun v => Real.sqrt v*f v) u = 1/(2*Real.sqrt u)*f u + Real.sqrt u*deriv f u := de.deriv
  rw [d]
  field_simp
  nlinarith only [sq,
    show (Real.sqrt u)^2*f u=u*f u by rw [sq],
    show (Real.sqrt u)^2*u*deriv f u=u*u*deriv f u by rw [sq]]

/-- Uniform norm estimate on the published strip. The bound applies at
the doubled sampling scale and does not depend on the support endpoints. -/
theorem norm_at_double_le (N : ℕ) (lar : Real.exp 10 < (N:ℝ))
    (f : ℝ → ℝ) (s : FiniteModelWeight f) :
    normFunctional (2*N) f (alpha N) ≤ ((2*Real.pi)⁻¹*Real.exp 4)*physicalEnergy f := by
  obtain ⟨n4,lg,_⟩ := large_parameters lar
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have mp : 0<((2*N:ℕ):ℝ) := by positivity
  have ad : 0 ≤ 2*alpha N := by unfold alpha; positivity
  have nf : Differentiable ℝ f := s.smooth.differentiable (by norm_num)
  have cf : Continuous (physicalDensity f) :=
    (s.continuous.div_const _).sub (continuous_id.mul (s.smooth.continuous_deriv (by norm_num)))
  have hh : HasCompactSupport (fun u => f u/2) := by
    simp only [div_eq_mul_inv]
    exact s.hasCompactSupport.mul_right
  have hs : HasCompactSupport (physicalDensity f) := hh.sub (s.hasCompactSupport.deriv.mul_left)
  have hp : HasCompactSupport (fun u => (physicalDensity f u)^2) := by
    simp only [pow_two]
    exact hs.mul_right
  have integr : Integrable (fun u => (physicalDensity f u)^2) := (cf.pow 2).integrable_of_hasCompactSupport hp
  let v := fun u : ℝ => Real.rpow (((2*N:ℕ):ℝ)*u) (2*alpha N) * derivativeWeight f u^2 /
    (1+Real.rpow (((2*N:ℕ):ℝ)*u) (-2*(beta-alpha N))) / u
  have non : ∀ u ∈ Ioi (0:ℝ), 0 ≤ v u := by
    intro u hu
    have hu' : 0<u := hu
    dsimp [v]
    positivity
  have point (u : ℝ) (hu : u ∈ Ioi (0:ℝ)) : v u ≤ Real.exp 4*(physicalDensity f u)^2 := by
    have up : 0<u := hu
    have pos := mul_pos mp up
    have num : 0 ≤ Real.rpow (((2*N:ℕ):ℝ)*u) (2*alpha N)*derivativeWeight f u^2 := mul_nonneg (Real.rpow_nonneg pos.le _) (sq_nonneg _)
    have den : 1 ≤ 1+Real.rpow (((2*N:ℕ):ℝ)*u) (-2*(beta-alpha N)) :=
      le_add_of_nonneg_right (Real.rpow_nonneg pos.le _)
    apply (div_le_div_of_nonneg_right (div_le_self num den) up.le).trans
    rw [density_companion nf up,mul_pow,Real.sq_sqrt up.le]
    rw [show Real.rpow (((2*N:ℕ):ℝ)*u) (2*alpha N)*(u*(physicalDensity f u)^2)/u =
        Real.rpow (((2*N:ℕ):ℝ)*u) (2*alpha N)*(physicalDensity f u)^2 by field_simp]
    by_cases cut : u ≤ 1
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have ub : ((2*N:ℕ):ℝ)*u ≤ (N:ℝ)*N := by
        have l := mul_le_mul_of_nonneg_left cut mp.le
        push_cast at l ⊢
        nlinarith [show (2:ℝ)≤N by exact_mod_cast (show 2≤N by omega)]
      apply (Real.rpow_le_rpow pos.le ub ad).trans_eq
      rw [Real.rpow_def_of_pos (mul_pos np np),Real.log_mul np.ne' np.ne']
      unfold alpha
      congr 1
      field_simp
      norm_num
    · have out : u ∉ tsupport f := fun h => cut ((closure_minimal s.support_subset isClosed_Icc h).2.trans s.upper_lt_one.le)
      have zf := (notMem_tsupport_iff_eventuallyEq.mp out).eq_of_nhds
      simp [physicalDensity,zf,deriv_of_notMem_tsupport out]
  have upper := integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall non))
    ((integr.const_mul (Real.exp 4)).integrableOn (s := Ioi 0))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall point))
  unfold normFunctional physicalEnergy
  rw [integral_const_mul] at upper
  exact (mul_le_mul_of_nonneg_left upper (by positivity : 0≤(2*Real.pi)⁻¹)).trans_eq (by ring)

/-- Removing the physical scale gives exactly one inverse factor of M. -/
theorem physical_rescale (b : ℝ → ℝ) (smooth : Differentiable ℝ b) (M : ℝ) (mp : 0<M) :
    physicalEnergy (fun u => b (M*u)) = physicalEnergy b/M := by
  have de (u : ℝ) : deriv (fun x => b (M*x)) u = deriv b (M*u)*M := by
    have h := (smooth (M*u)).hasDerivAt.comp u ((hasDerivAt_id u).const_mul M)
    simpa only [Function.comp_def,mul_one] using h.deriv
  have eqn (u : ℝ) : physicalDensity (fun v => b (M*v)) u = physicalDensity b (M*u) := by
    unfold physicalDensity
    rw [de]
    ring
  unfold physicalEnergy
  simp_rw [eqn]
  rw [integral_comp_mul_left_Ioi (fun u => physicalDensity b u^2) _ mp,mul_zero,smul_eq_mul]
  ring

#print axioms norm_at_double_le
#print axioms physical_rescale
end GoldbachSpectral435

