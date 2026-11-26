module
public import ConductorCorrection
public import ConductorMoments
public import DiagonalPole


/-! The two leading central terms of the Li–Liu model when the conductor
runs through the powers of a fixed even integer. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Set Complex
open scoped Topology ComplexConjugate
namespace GoldbachSpectral435.SecondMoment
open GoldbachSpectral435.ConductorCorrection GoldbachSpectral435.ConductorMoments

def slopeCoefficient (b : ℕ) : ℂ :=
  Complex.log (Real.pi:ℂ)+localCorrection b-logDeriv Gamma (3/4)

private def regular (b : ℕ) (w : ℂ) : ℂ :=
  (Real.pi:ℂ)^w*((singularSeries b:ℂ)*baselineProductR b w)*
  (riemannZeta₁ (1+w)*riemannZeta₁ (1-w))*(gammaQuotient (w/2))^2

private lemma gamma_slope : HasDerivAt (fun w : ℂ => gammaQuotient (w/2))
    (-logDeriv Gamma (3/4)/2) 0 := by
  have hA : HasDerivAt (fun w : ℂ => (3/2-w/2)/2) (-1/4) 0 := by
    convert ((hasDerivAt_const (0:ℂ) (3/2:ℂ)).sub ((hasDerivAt_id 0).div_const 2)).div_const 2 using 1 <;> norm_num
  have hB : HasDerivAt (fun w : ℂ => (3/2+w/2)/2) (1/4) 0 := by
    convert (((hasDerivAt_id (0:ℂ)).div_const 2).const_add (3/2)).div_const 2 using 1 <;> norm_num
  have z : 0<(3/4:ℂ).re := by norm_num
  have na := Gamma_ne_zero_of_re_pos z
  have da := (hasDerivAt_Gamma_of_re_pos (s:=(3/2-(0:ℂ)/2)/2) (by norm_num)).differentiableAt.hasDerivAt.comp 0 hA
  have db := (hasDerivAt_Gamma_of_re_pos (s:=(3/2+(0:ℂ)/2)/2) (by norm_num)).differentiableAt.hasDerivAt.comp 0 hB
  convert da.div db (by simpa only [Function.comp_apply,zero_div,add_zero,
    show (3/2:ℂ)/2=3/4 by norm_num] using na) using 1
  · rfl
  · simp only [Function.comp_apply,zero_div,sub_zero,add_zero,show (3/2:ℂ)/2=3/4 by norm_num,logDeriv_apply]
    field_simp
    ring

private lemma gamma0 : gammaQuotient 0 = 1 := by
  unfold gammaQuotient
  simp only [sub_zero,add_zero]
  exact div_self (Gamma_ne_zero_of_re_pos (by norm_num))

private lemma regular_one (b : ℕ) (ev : Even b) (bp : 0<b) : regular b 0=1 := by
  simp [regular,baselineProductR_zero b ev bp,gamma0]

private lemma regular_slope (b : ℕ) (ev : Even b) (bp : 0<b) :
    HasDerivAt (regular b) (slopeCoefficient b) 0 := by
  have pp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have A := (hasDerivAt_id (0:ℂ)).const_cpow (c:=(Real.pi:ℂ)) (Or.inl pp)
  have B := normalized_product_derivative b ev bp
  have za : HasDerivAt (fun w : ℂ => 1+w) 1 0 := by simpa using (hasDerivAt_id (0:ℂ)).const_add 1
  have zb : HasDerivAt (fun w : ℂ => 1-w) (-1) 0 := by
    convert (hasDerivAt_const (0:ℂ) (1:ℂ)).sub (hasDerivAt_id 0) using 1
    · rfl
    · norm_num
  have C := ((differentiable_riemannZeta₁ (1+(0:ℂ))).hasDerivAt.comp 0 za).mul
    ((differentiable_riemannZeta₁ (1-(0:ℂ))).hasDerivAt.comp 0 zb)
  convert (((A.mul B).mul C).mul (gamma_slope.pow 2)) using 1
  all_goals first | rfl | (simp [Function.comp_apply,gamma0,baselineProductR_zero b ev bp,slopeCoefficient]; ring)

private lemma regular_power (b k : ℕ) (w : ℂ) : regular (b^(k+1)) w=regular b w := by
  have eq : baselineProductR (b^(k+1)) w=baselineProductR b w := by
    unfold baselineProductR
    rw [Nat.primeFactors_pow_succ]
    congr 1
    apply tprod_congr
    intro p
    by_cases hp : p.Prime
    · have test : p∣b^(k+1) ↔ p∣b := ⟨hp.dvd_of_dvd_pow,fun d => d.trans (dvd_pow_self b (Nat.succ_ne_zero k))⟩
      simp only [test]
    · simp [hp]
  simp only [regular,eq,singular_power]

private lemma model_regular (N : ℕ) (ev : Even N) (np : 0<N) (w : ℂ) (wp : 0<w.re) :
    w^2*continuedModel N (w/2) (w/2) = -((N:ℂ)^(-w))*regular N w := by
  have wn : w≠0 := by intro e; simp [e] at wp
  have zn : (N:ℂ)≠0 := by exact_mod_cast np.ne'
  have p1 : 1+w≠(1:ℂ) := by simpa using wn
  have p2 : 1-w≠(1:ℂ) := by intro e; apply wn; linear_combination -e
  unfold continuedModel regular
  rw [show w/2+w/2=w by ring,show 1-w/2-w/2=1-w by ring,
    densityEulerProduct_eq_zeta_baseline N ev np wp,
    riemannZeta_eq_inv_sub_mul p1,riemannZeta_eq_inv_sub_mul p2,
    ← Complex.ofReal_natCast,
    Complex.div_cpow_ofReal_nonneg Real.pi_pos.le (Nat.cast_nonneg _) w]
  simp only [add_sub_cancel_left,sub_sub_cancel_left,Complex.ofReal_natCast,Complex.cpow_neg]
  field_simp

/-- This limit is on the moving scale of the original strip. It retains
the linear correction after the universal double pole has been subtracted. -/
theorem model_second_term (b : ℕ) (hb : 1<b) (ev : Even b) (c : ℝ) (cp : 0<c) :
    let n := fun k : ℕ => b^(k+1)
    let x := fun k : ℕ => c/Real.log (n k)
    Tendsto (fun k => (x k:ℂ) * (continuedModel (n k) (x k) (x k) +
      (Real.exp (-2*c):ℂ)/(4*(x k:ℂ)^2))) atTop
      (𝓝 (-(Real.exp (-2*c):ℂ)*slopeCoefficient b/2)) := by
  intro n x
  have ng : Tendsto n atTop atTop := (pow_right_strictMono₀ hb).tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have lp (k : ℕ) : 0<Real.log (n k) := Real.log_pos (by exact_mod_cast one_lt_pow₀ hb (Nat.succ_ne_zero k))
  have xp (k : ℕ) : 0<x k := div_pos cp (lp k)
  have lim : Tendsto x atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp ng))
  let w := fun k => 2*(x k:ℂ)
  have wl : Tendsto w atTop (𝓝[≠] (0:ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall (fun k => ?_)⟩
    · simpa [w] using (Complex.continuous_ofReal.continuousAt.tendsto.comp lim).const_mul (2:ℂ)
    · change 2*(x k:ℂ)≠0
      exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (xp k).ne')
  have slopes := (regular_slope b ev (by omega)).tendsto_slope_zero.comp wl
  have scaled := slopes.const_mul (-(Real.exp (-2*c):ℂ)/2)
  convert scaled using 1
  · funext k
    have wp : 0<(w k).re := by dsimp [w]; simp; exact xp k
    have eq := model_regular (n k) (ev.pow_of_ne_zero (Nat.succ_ne_zero k)) (by dsimp [n]; positivity) _ wp
    have expo : (n k:ℂ)^(-w k) = (Real.exp (-2*c):ℂ) := by
      have nr : (0:ℝ)<n k := by exact_mod_cast (show 0<n k by dsimp [n]; positivity)
      rw [← Complex.ofReal_natCast]
      have cast : -w k = ((-(2*x k):ℝ):ℂ) := by dsimp [w]; push_cast; rfl
      rw [cast,← Complex.ofReal_cpow nr.le,Real.rpow_def_of_pos nr]
      congr 2
      dsimp [x]; field_simp [(lp k).ne']
    rw [expo,regular_power b k] at eq
    have arg : w k/2=(x k:ℂ) := by dsimp [w]; ring
    rw [arg] at eq
    have xn := Complex.ofReal_ne_zero.mpr (xp k).ne'
    simp only [Function.comp_apply,zero_add,regular_one b ev (by omega),smul_eq_mul]
    have algebra {y M E G : ℂ} (nz : y≠0) (h : (2*y)^2*M= -E*G) :
        y*(M+E/(4*y^2)) = -E/2*((2*y)⁻¹*(G-1)) := by
      field_simp
      linear_combination 4*h
    exact algebra xn eq
  · ring

/-- A necessary two-term asymptotic for the unmodified odd-character
mean square itself. The remaining expression contains only Dirichlet
logarithmic derivatives and explicit constants. -/
theorem odd_mean_second_term_of_exists_S (s : ∃ h, HypothesisS h)
    (b : ℕ) [NeZero b] (hb : 1<b) (ev : Even b) (g : ∀ k : ℕ, GRH (b^(k+1)))
    (c : ℝ) (hc : 1<c) :
    let n := fun k : ℕ => b^(k+1)
    let x := fun k : ℕ => c/Real.log (n k)
    Tendsto (fun k =>
      (x k:ℂ) * ((2/(Nat.totient (n k):ℂ))*
        (∑ χ ∈ oddCharacters (n k), ((‖logDerivative χ (line (x k) 0)‖^2:ℝ):ℂ)) -
        (1-(Real.exp (-2*c):ℂ))/(4*(x k:ℂ)^2))) atTop
      (𝓝 (-(Real.exp (-2*c):ℂ)*slopeCoefficient b/2)) := by
  intro n x
  have bp : 0<b := by omega
  have cp : 0<c := zero_lt_one.trans hc
  have ng : Tendsto n atTop atTop := (pow_right_strictMono₀ hb).tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have ne (k : ℕ) : Even (n k) := ev.pow_of_ne_zero (Nat.succ_ne_zero k)
  have lp (k : ℕ) : 0<Real.log (n k) := Real.log_pos (by exact_mod_cast one_lt_pow₀ hb (Nat.succ_ne_zero k))
  have xp (k : ℕ) : 0<x k := div_pos cp (lp k)
  have lim : Tendsto x atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp ng))
  have gap (k : ℕ) : (c-1)/c*x k ≤ x k-alpha (n k) := by
    change (c-1)/c*(c/Real.log (n k)) ≤ c/Real.log (n k)-1/Real.log (n k)
    apply le_of_eq; field_simp
  have res := common_shift_error s ng ne g (singularSeries_pos b) (singular_power b)
    xp lim (show 0<(c-1)/c by positivity) gap 0
  let w := fun k => 2*x k
  have right : Tendsto w atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa using lim.const_mul 2,Eventually.of_forall (fun k => mul_pos (by norm_num) (xp k))⟩
  have D := ((DiagonalPole.diagonal_no_simple_pole b bp).comp right).const_mul (1/2:ℂ)
  have M := model_second_term b hb ev c cp
  have total := (res.add D).add M
  rw [mul_zero,add_zero,zero_add] at total
  apply total.congr'
  filter_upwards with k
  rw [← moment_eq_mean_square (n k) (x k) 0]
  change (x k:ℂ)*residual (n k) (line (x k) 0) (conj (line (x k) 0))+
      (1/2:ℂ)*(((2*x k:ℝ):ℂ)*(diagonalSeries b (2*x k:ℝ)-
        ((((2*x k:ℝ):ℂ))^2)⁻¹))+
      (x k:ℂ)*(continuedModel (n k) (x k) (x k)+(Real.exp (-2*c):ℂ)/(4*(x k:ℂ)^2)) = _
  have di (v : ℂ) : diagonalSeries (n k) v = diagonalSeries b v := diagonal_power b k v
  simp only [ConditionalGoldbach.residual,moment,line,Complex.ofReal_zero,zero_mul,
    add_zero,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_ofNat,← two_mul,di]
  have nz := Complex.ofReal_ne_zero.mpr (xp k).ne'
  field_simp
  ring

#print axioms odd_mean_second_term_of_exists_S
#print axioms model_second_term
end GoldbachSpectral435.SecondMoment
