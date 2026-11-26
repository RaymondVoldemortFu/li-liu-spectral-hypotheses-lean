module
public import HorizontalLogDerivative
public import ZeroPoissonMass

/-! A uniform weighted L¹ estimate for the real part of the logarithmic
derivative, all the way to the critical line from the right. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex MeasureTheory Filter Set
namespace GoldbachSpectral435.CriticalCharacter

def lineWeight (t : ℝ) := (1+|t|)⁻¹^4

theorem realpart_mass :
    ∃ B : ℝ, 0<B ∧ ∀ (q : ℕ) [NeZero q], 4≤q → GRH q → ∀ χ : Character q, χ≠1 →
      ∀ σ : ℝ, 0<σ → σ≤1 →
      let F := fun t => lineWeight t*|(logDerivative χ (line σ t)).re|
      Integrable F ∧ (∫ t,F t)≤B*(6+Real.log q) := by
  obtain ⟨K,kp,zMass⟩ := zero_poisson_mass_bound
  obtain ⟨C,cp,ref⟩ := zeroPoisson_anchor_bound
  let D := 3*(Real.log 4+4)+16
  let A := C+D+8
  let V := fun t : ℝ => (1+|t|)⁻¹^2
  have di : 0<D := by dsimp [D]; positivity
  have ap : 0<A := by dsimp [A]; positivity
  have vi : Integrable V := by
    have h := integrable_one_add_norm (E:=ℝ) (μ:=volume) (r:=2) (by simp)
    convert h using 1
    ext t
    simp [V,Real.norm_eq_abs,Real.rpow_neg (by positivity : 0≤1+|t|)]
  have vpos : 0≤∫ t,V t := integral_nonneg (fun t => sq_nonneg _)
  refine ⟨Real.pi*K+A*(∫ t,V t),by positivity,?_⟩
  intro q inst q4 grh χ nc σ sp s1 F
  let J := 6+Real.log (q:ℝ)
  let Z := fun t => poissonKernelReal 1 t*zeroPoisson χ σ t
  have zi : Integrable Z := (zero_poisson_mass χ nc σ sp).1
  have qr : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have lq : 0≤Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.pos q)
  have j1 : 1≤J := by dsimp [J]; linarith
  have jp : 0<J := zero_lt_one.trans_le j1
  have bound (t : ℝ) : F t≤Real.pi*Z t+(A*J)*V t := by
    let w := 1+|t|
    have w1 : 1≤w := by dsimp [w]; linarith [abs_nonneg t]
    have wp := zero_lt_one.trans_le w1
    have a := horizontal_comparison grh χ nc σ t sp s1
    have z1 : 0≤zeroPoisson χ σ t := tsum_nonneg (fun _ => by positivity)
    have z2 : 0≤zeroPoisson χ (3/2) t := tsum_nonneg (fun _ => by positivity)
    have sl : Real.log ((q:ℝ)*(|t|+2))≤J*w := by
      rw [Real.log_mul qr.ne' (by positivity)]
      have b := Real.log_le_sub_one_of_pos (show 0< |t|+2 by positivity)
      dsimp only [J,w]
      nlinarith only [b,mul_nonneg lq (abs_nonneg t),abs_nonneg t]
    have ref' := (ref q inst χ nc t).trans (mul_le_mul_of_nonneg_left sl cp.le)
    have de : D+8*Real.log q≤(D+8)*(J*w) := by
      have jw := le_mul_of_one_le_right jp.le w1
      have h := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le j1 w1) di.le
      dsimp only [J] at jw h ⊢
      nlinarith only [jw,h]
    have re : |(logDerivative χ (line σ t)).re|≤zeroPoisson χ σ t+A*J*w := by
      rw [abs_le] at a ⊢
      dsimp only [A,D] at de ⊢
      constructor <;> nlinarith only [a.1,a.2,z1,z2,ref',de]
    have w2 : 1+t^2≤w^2 := by dsimp [w]; nlinarith only [sq_abs t,abs_nonneg t]
    have wc : lineWeight t≤Real.pi*poissonKernelReal 1 t := by
      dsimp [lineWeight,poissonKernelReal]
      rw [one_pow,show Real.pi*(1/(Real.pi*(1+t^2)))=1/(1+t^2) by field_simp]
      change w⁻¹^4≤1/(1+t^2)
      rw [inv_pow,one_div]
      exact inv_le_inv₀ (pow_pos wp _) (by positivity) |>.mpr
        (w2.trans (pow_le_pow_right₀ w1 (by decide : 2≤4)))
    have wn : 0≤lineWeight t := pow_nonneg (inv_nonneg.mpr wp.le) _
    apply (mul_le_mul_of_nonneg_left re wn).trans
    rw [mul_add]
    apply add_le_add ((mul_le_mul_of_nonneg_right wc z1).trans_eq (mul_assoc ..))
    change w⁻¹^4*(A*J*w)≤(A*J)*w⁻¹^2
    rw [show w⁻¹^4*(A*J*w)=(A*J)*w⁻¹^2*w⁻¹ by field_simp]
    exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ w1)
  have fc : Continuous (fun t => logDerivative χ (line σ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (logDerivative_analyticAt_of_GRH grh χ nc (by simpa [line] using sp : 0<(line σ t).re)).continuousAt.comp
    fun_prop [line]
  have fct : Continuous F := by
    dsimp only [F,lineWeight]
    exact (((continuous_const.add continuous_abs).inv₀ (fun t : ℝ => (show (0:ℝ)<1+|t| by positivity).ne')).pow 4).mul
      ((Complex.continuous_re.comp fc).abs)
  have hi := (zi.const_mul Real.pi).add (vi.const_mul (A*J))
  have fi : Integrable F := hi.mono' fct.aestronglyMeasurable (Eventually.of_forall (fun t => by
    rw [Real.norm_of_nonneg (show 0≤F t by dsimp [F,lineWeight]; positivity)]
    exact bound t))
  refine ⟨fi,?_⟩
  have bi := integral_mono fi hi bound
  change (∫ t,F t)≤∫ t,Real.pi*Z t+(A*J)*V t at bi
  rw [integral_add (zi.const_mul _) (vi.const_mul _),integral_const_mul,integral_const_mul] at bi
  have z := zMass q χ nc σ sp s1
  have ll : Real.log (2*(q:ℝ))≤J := by
    rw [Real.log_mul (by norm_num) qr.ne']
    dsimp [J]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have zb := mul_le_mul_of_nonneg_left (z.trans (mul_le_mul_of_nonneg_left ll kp.le)) Real.pi_pos.le
  change Real.pi*(∫ t,Z t)≤_ at zb
  change (∫ t,F t)≤(Real.pi*K+A*(∫ t,V t))*J
  linarith only [bi,zb]

#print axioms realpart_mass
end GoldbachSpectral435.CriticalCharacter
