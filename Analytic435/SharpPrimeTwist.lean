module
public import LogDerivativeMass
public import ReciprocalMellin

/-! The estimated logarithmic derivative is tested against a Mellin
frequency with one-sided physical support. Only its real part is needed. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex Filter Set MeasureTheory
open scoped ComplexConjugate Topology
namespace GoldbachSpectral435.CriticalCharacter

private lemma one_sided_bound (W D : ℝ→ℂ) (w : ℝ→ℝ) (C : ℝ)
    (direct : Integrable (fun t => W t*D t)) (mirror : Integrable (fun t => conj (W t)*D t))
    (z : (∫ t,conj (W t)*D t)=0) (cap : ∀ t, ‖W t‖≤C*w t)
    (re : Integrable (fun t => w t*|(D t).re|)) :
    ‖∫ t,W t*D t‖≤2*C*(∫ t,w t*|(D t).re|) := by
  let A := fun t => W t*D t
  let B := fun t => W t*conj (D t)
  have bi : Integrable B := by
    have h := Complex.conjCLE.toContinuousLinearMap.integrable_comp mirror
    simpa only [Complex.conjCLE_apply,ContinuousLinearEquiv.coe_coe,map_mul,conj_conj,Function.comp_def,B] using h
  have zero : (∫ t,B t)=0 := by
    have e := congrArg (fun v : ℂ => conj v) z
    simpa only [← integral_conj,map_mul,conj_conj,map_zero,B] using e
  have eq (t : ℝ) : A t+B t=W t*(2*((D t).re:ℂ)) := by
    dsimp only [A,B]
    rw [← mul_add,Complex.add_conj,ofReal_mul,ofReal_ofNat]
  have per (t : ℝ) : ‖A t+B t‖≤2*C*(w t*|(D t).re|) := by
    rw [eq,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (cap t) (by positivity)).trans_eq (by ring)
  have cmp := integral_mono (direct.add bi).norm (re.const_mul (2*C)) per
  rw [integral_const_mul] at cmp
  have e : (∫ t,A t+B t)=∫ t,W t*D t := by rw [integral_add direct bi,zero,add_zero]
  rw [← e]
  exact (norm_integral_le_integral_norm _).trans cmp

/-- Square-root cancellation with a single conductor logarithm. The
constant only depends on the fixed compact test. -/
theorem sharp_prime_twist (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ M : ℕ in atTop, ∀ (q : ℕ) [NeZero q], 4≤q → q≤M → GRH q →
      ∀ χ : Character q, χ≠1 → ‖primeTwist χ M f‖≤C*Real.sqrt M*(6+Real.log q) := by
  obtain ⟨A,ap,decay⟩ := mellin_axis f hf
  obtain ⟨B,bp,mass⟩ := realpart_mass
  let c := ‖(2*(Real.pi:ℂ))⁻¹‖
  let K := Real.exp 1*A
  have cp : 0<c := norm_pos_iff.mpr (inv_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have kp : 0<K := mul_pos (Real.exp_pos _) ap
  have growth := (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const hf.lower_pos
  refine ⟨c*(2*K)*B,by positivity,?_⟩
  filter_upwards [growth.eventually_gt_atTop 1] with M large
  intro q inst q4 qm grh χ nc
  have mp : 0<M := by omega
  have mr : 0<(M:ℝ) := Nat.cast_pos.mpr mp
  let L := Real.log (M:ℝ)
  let σ := 1/L
  have l1 : 1≤L := (Real.le_log_iff_exp_le mr).mpr (Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3≤M by omega)))
  have lp : 0<L := zero_lt_one.trans_le l1
  have sp : 0<σ := one_div_pos.mpr lp
  have s1 : σ≤1 := (div_le_one lp).mpr l1
  let W := fun t => (M:ℂ)^(line σ t)*mellin (fun u => (companion f u:ℂ)) (line σ t)
  let D := fun t => logDerivative χ (line σ t)
  have wb (t : ℝ) : ‖W t‖≤K*lineWeight t := by
    have r : (line σ t).re=σ := by simp [line]
    have e : (M:ℝ)^σ=Real.exp 1 := by
      rw [Real.rpow_def_of_pos mr]
      change Real.exp (L*(1/L))=_
      rw [mul_one_div_cancel lp.ne']
    have d := decay (line σ t) (by rw [r]; exact ⟨sp.le,s1⟩)
    rw [show (line σ t).im=t by simp [line]] at d
    dsimp only [W]
    rw [norm_mul,← ofReal_natCast M,Complex.norm_cpow_eq_rpow_re_of_pos mr,r,e]
    exact (mul_le_mul_of_nonneg_left d (Real.exp_pos _).le).trans_eq (by dsimp [K,lineWeight]; ring)
  obtain ⟨hi,inv⟩ := nonprincipal_sampling q4 grh χ nc M qm (companion f)
    ((FiniteModel.companion_contDiff hf).of_le (by norm_num)) (FiniteModel.companion_support_subset hf) σ sp s1
  obtain ⟨mi,zero⟩ := conjugate_sampling_zero q4 grh χ nc M qm f hf large σ sp s1
  obtain ⟨intR,est⟩ := mass q q4 grh χ nc σ sp s1
  have integral := (one_sided_bound W D lineWeight K hi mi zero wb intR).trans
    (mul_le_mul_of_nonneg_left est (by positivity : 0≤2*K))
  change (2*(Real.pi:ℂ))⁻¹*(∫ t,W t*D t)= -characterSample χ M (companion f) at inv
  have norm := congrArg (fun v : ℂ => ‖v‖) inv
  simp only [norm_mul,norm_neg] at norm
  change c*‖∫ t,W t*D t‖=‖characterSample χ M (companion f)‖ at norm
  rw [prime_twist_eq_sample χ M mp f hf,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),← norm]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left integral cp.le) (Real.sqrt_nonneg _)).trans_eq (by ring)

#print axioms sharp_prime_twist
end GoldbachSpectral435.CriticalCharacter
