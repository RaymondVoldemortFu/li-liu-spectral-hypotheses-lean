module
public import ConditionalGoldbach.Proofs.CharacterPoissonComparison
public import ConditionalGoldbach.Proofs.SpectralPerronTruncation

/-! The horizontal comparison with the positive Poisson sum of zeros,
for every nonprincipal character of either parity. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex Filter Set
open scoped Topology
namespace GoldbachSpectral435.CriticalCharacter
attribute [local instance] conductorNeZero

private lemma parity_shift {d : ℕ} (χ : Character d) :
    ∃ k : ℝ, 0≤k ∧ ∀ z : ℂ, χ.gammaFactor z=Gammaℝ (z+k) := by
  rcases χ.even_or_odd with ev|od
  · exact ⟨0,le_rfl,fun z => by simpa using ev.gammaFactor_def z⟩
  · exact ⟨1,zero_le_one,fun z => by simpa using od.gammaFactor_def z⟩

private lemma completed_derivative {d : ℕ} [NeZero d] (χ : Character d) (nc : χ≠1)
    {k : ℝ} (kp : 0≤k) (gamma : ∀ z : ℂ,χ.gammaFactor z=Gammaℝ (z+k))
    {z : ℂ} (zp : 0<z.re) (nz : χ.LFunction z≠0) :
    logDeriv (completedL χ) z=logDeriv χ.LFunction z+
      (Complex.log (d:ℂ)-Complex.log (Real.pi:ℂ))/2+logDeriv Gamma ((z+k)/2)/2 := by
  let P := fun w : ℂ => (d:ℂ)^((1/2)*w+1/2)
  let Q := fun w : ℂ => (Real.pi:ℂ)^((-1/2)*w+(-k:ℂ)/2)
  let G := fun w : ℂ => Gamma ((w+k)/2)
  have dn : (d:ℂ)≠0 := by exact_mod_cast NeZero.ne d
  have pn : (Real.pi:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have gp : 0<((z+k)/2).re := by simp only [div_ofNat_re,add_re,ofReal_re]; linarith
  have gn := Gamma_ne_zero_of_re_pos gp
  have gd := (hasDerivAt_Gamma_of_re_pos gp).differentiableAt.hasDerivAt.comp z (((hasDerivAt_id z).add_const (k:ℂ)).div_const 2)
  have gd' : HasDerivAt G (deriv Gamma ((z+k)/2)*(1/2)) z := by simpa [G,Function.comp_def] using gd
  have pz : P z≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl dn)
  have qz : Q z≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl pn)
  have pd : Differentiable ℂ P := ((differentiable_id.const_mul _).add_const _).const_cpow (Or.inl dn)
  have qd : Differentiable ℂ Q := ((differentiable_id.const_mul _).add_const _).const_cpow (Or.inl pn)
  have eq : completedL χ=ᶠ[𝓝 z] P*Q*G*χ.LFunction := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds zp] with w hw
    have hc : w≠0 := by intro e; simp [e] at hw
    have h := (eq_div_iff (gammaFactor_ne_zero_re_pos χ hw)).mp (χ.LFunction_eq_completed_div_gammaFactor w (Or.inl hc))
    simp only [completedL,← h,gamma,Gammaℝ_def,Pi.mul_apply,P,Q,G]
    rw [show (w+1)/2=(1/2)*w+1/2 by ring,show -(w+(k:ℂ))/2=(-1/2)*w+(-k:ℂ)/2 by ring]
    ring
  rw [(logDeriv_congr_nhds eq).eq_of_nhds,
    logDeriv_mul (f:=P*Q*G) (g:=χ.LFunction) z (mul_ne_zero (mul_ne_zero pz qz) gn) nz
      ((pd z).mul (qd z)|>.mul gd'.differentiableAt) (χ.differentiable_LFunction nc z),
    logDeriv_mul (f:=P*Q) (g:=G) z (mul_ne_zero pz qz) gn ((pd z).mul (qd z)) gd'.differentiableAt,
    logDeriv_mul (f:=P) (g:=Q) z pz qz (pd z) (qd z)]
  change logDeriv (fun w : ℂ => (d:ℂ)^((1/2)*w+1/2)) z+
    logDeriv (fun w : ℂ => (Real.pi:ℂ)^((-1/2)*w+(-k:ℂ)/2)) z+logDeriv G z+_ = _
  rw [logDeriv_cpow_affine _ _ _ _ dn,logDeriv_cpow_affine _ _ _ _ pn,logDeriv_apply G,gd'.deriv]
  dsimp only [G,logDeriv_apply]
  ring

private lemma gamma_quarter {u v : ℂ} (hu : 1/4≤u.re) (hv : 1/4≤v.re) :
    ‖logDeriv Gamma u-logDeriv Gamma v‖≤32*‖u-v‖ := by
  have hs := Gamma_logDeriv_difference_hasSum (lt_of_lt_of_le (by norm_num) hu) (lt_of_lt_of_le (by norm_num) hv)
  apply le_of_tendsto hs.tendsto_sum_nat.norm
  apply Eventually.of_forall
  intro n
  calc
    _ ≤ ∑ j∈Finset.range n, ‖1/(v+(j:ℂ))-1/(u+(j:ℂ))‖ := norm_sum_le _ _
    _ ≤ (‖u-v‖/(1/4:ℝ)^2)*∑ j∈Finset.range n,1/((j:ℝ)+1)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => gamma_resolvent_norm_bound u v (1/4) (by norm_num) (by norm_num) hu hv j)
    _ ≤ (‖u-v‖/(1/4:ℝ)^2)*2 := mul_le_mul_of_nonneg_left
      ((sum_one_div_nat_add_one_sq_le n).trans (sub_le_self _ (by positivity))) (by positivity)
    _ = _ := by ring

theorem horizontal_comparison {q : ℕ} [NeZero q] (grh : GRH q) (χ : Character q)
    (nc : χ≠1) (σ t : ℝ) (sp : 0<σ) (s1 : σ≤1) :
    |(logDerivative χ (line σ t)).re-(zeroPoisson χ σ t-zeroPoisson χ (3/2) t)|≤
      3*(Real.log 4+4)+16+8*Real.log q := by
  let u := (1/2:ℂ)+line σ t
  let v := (1/2:ℂ)+line (3/2) t
  have ur : 1/2<u.re := by simp [u,line,sp]
  have vr : 1/2<v.re := by norm_num [v,line]
  have pp := primitiveCharacter_ne_one_of_ne_one χ nc
  have nonzero (z : ℂ) (hz : 1/2<z.re) := primitive_LFunction_ne_zero_of_GRH grh χ.conductor_dvd_level
    χ.primitiveCharacter χ.primitiveCharacter_isPrimitive pp hz
  have comp (z : ℂ) (hz : 1/2<z.re) : completedL χ.primitiveCharacter z≠0 := by
    intro h
    exact nonzero z hz ((completedL_eq_zero_iff χ.primitiveCharacter pp χ.primitiveCharacter_isPrimitive _).mp h).2.2
  obtain ⟨k,kp,eq⟩ := parity_shift χ.primitiveCharacter
  let a := (u+k)/2
  let b := (v+k)/2
  have hu : 1/4≤a.re := by dsimp [a]; rw [div_ofNat_re,add_re,ofReal_re]; linarith
  have hv : 1/4≤b.re := by dsimp [b]; rw [div_ofNat_re,add_re,ofReal_re]; linarith
  have g := gamma_quarter hu hv
  have gap : a-b=((σ/2-3/4:ℝ):ℂ) := by dsimp [a,b,u,v,line]; push_cast; ring
  rw [gap,norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)] at g
  have ud : 0<u.re := by linarith
  have vd : 0<v.re := by linarith
  have had := completedL_logDerivative_difference χ.primitiveCharacter pp χ.primitiveCharacter_isPrimitive
    u v (comp u ur) (comp v vr)
  change logDeriv (completedL χ.primitiveCharacter) u-logDeriv (completedL χ.primitiveCharacter) v=_ at had
  rw [completed_derivative _ pp kp eq ud (nonzero _ ur),completed_derivative _ pp kp eq vd (nonzero _ vr)] at had
  have eu := logDeriv_eq_primitive_add_euler χ nc ud (nonzero _ ur)
  have ev := logDeriv_eq_primitive_add_euler χ nc vd (nonzero _ vr)
  have de : logDerivative χ (line σ t)-zeroDifference χ.primitiveCharacter u v=
      logDerivative χ (line (3/2) t)-(logDeriv Gamma a-logDeriv Gamma b)/2+
        eulerCorrection χ u-eulerCorrection χ v := by
    change logDeriv χ.LFunction u-_=logDeriv χ.LFunction v-(_-_)/2+_-_
    dsimp only [a,b]
    linear_combination eu-ev+had
  have z := zeroDifference_real_eq_poisson grh χ nc σ (3/2) t sp (by norm_num)
  rw [← z,← sub_re,de]
  apply (abs_re_le_norm _).trans
  have g0 := logDerivative_right_bound q χ (line (3/2) t) (by norm_num [line])
  have g1 := eulerCorrection_norm_le χ ur.le
  have g2 := eulerCorrection_norm_le χ vr.le
  calc
    _ ≤ (‖logDerivative χ (line (3/2) t)‖+‖(logDeriv Gamma a-logDeriv Gamma b)/2‖+
      ‖eulerCorrection χ u‖)+‖eulerCorrection χ v‖ :=
      (norm_sub_le ..).trans (add_le_add (norm_add_le .. |>.trans (add_le_add (norm_sub_le ..) (le_refl _))) (le_refl _))
    _ ≤ _ := by rw [norm_div,Complex.norm_ofNat]; linarith only [g0,g1,g2,g,sp]

#print axioms horizontal_comparison
end GoldbachSpectral435.CriticalCharacter
