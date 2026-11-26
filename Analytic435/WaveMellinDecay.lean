module
public import PrimeLineFrequencies

/-! Mellin decay for physical Fourier modulations of a compact real
weight. The constant is uniform in the modulation frequency. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open ConditionalGoldbach Complex MeasureTheory Set
namespace GoldbachSpectral435.CriticalCharacter
open GoldbachSieve

def trigTest (b : Bool) (t : ℝ) (h : ℝ→ℝ) :=
  if b then sinTest t h else cosTest t h

private def mt (h : ℝ→ℝ) (s : ℂ) := mellin (fun u => (h u:ℂ)) s

private lemma trigTest_smooth {k : ℕ} {h : ℝ→ℝ} (hf : ContDiff ℝ k h) (b : Bool) (t : ℝ) :
    ContDiff ℝ k (trigTest b t h) := by
  cases b
  · exact hf.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
  · exact hf.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

private lemma trigTest_support (b : Bool) (t : ℝ) (h : ℝ→ℝ) :
    Function.support (trigTest b t h)⊆Function.support h := by
  intro u hu z
  apply hu
  cases b <;> simp [trigTest,sinTest,cosTest,z]

private lemma trigTest_norm (b : Bool) (t : ℝ) (h : ℝ→ℝ) (u : ℝ) : |trigTest b t h u|≤|h u| := by
  cases b <;> simp only [trigTest,Bool.false_eq_true,ite_false,ite_true,sinTest,cosTest,abs_mul]
  · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

private lemma base_bound (h : ℝ→ℝ) (hf : ContDiff ℝ 0 h) (a d : ℝ) (ap : 0<a) (d1 : d≤1)
    (supp : Function.support h⊆Icc a d) :
    ∃ C : ℝ, 0<C ∧ ∀ b t s, 0<s.re → s.re≤1 → ‖mt (trigTest b t h) s‖≤C := by
  have comp : HasCompactSupport h := HasCompactSupport.intro isCompact_Icc fun u hu => by
    by_contra nz
    exact hu (supp nz)
  have fi := hf.continuous.integrable_of_hasCompactSupport (μ:=volume) comp
  let C := ∫ u in Ioi (0:ℝ), a⁻¹*|h u|
  have cp : 0≤C := integral_nonneg fun _ => mul_nonneg (inv_nonneg.mpr ap.le) (abs_nonneg _)
  refine ⟨C+1,by positivity,fun b t s sp _ => ?_⟩
  apply le_trans _ (le_add_of_nonneg_right zero_le_one : C≤C+1)
  have sm : ContDiff ℝ 0 (trigTest b t h) := trigTest_smooth (k:=0) hf b t
  have sup := (trigTest_support b t h).trans supp
  have ii := (compact_mellin_regular _ sm.continuous a d sup s sp).1.norm
  unfold mt mellin
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae ii (fi.abs.const_mul a⁻¹).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hu,sub_re,one_re]
  by_cases z : h u=0
  · have zero : trigTest b t h u=0 := by by_contra nz; exact trigTest_support b t h nz z
    simp [zero,z]
  have loc := supp (Function.mem_support.mpr z)
  have pow : u^(s.re-1)≤a⁻¹ := calc
    _ ≤ u^(-(1:ℝ)) := Real.rpow_le_rpow_of_exponent_ge hu (loc.2.trans d1) (by linarith)
    _ = u⁻¹ := Real.rpow_neg_one u
    _ ≤ a⁻¹ := inv_anti₀ ap loc.1
  exact mul_le_mul pow (trigTest_norm b t h u) (abs_nonneg _) (inv_nonneg.mpr ap.le)

private lemma step_point {h : ℝ→ℝ} (dh : Differentiable ℝ h) (b : Bool) (t u : ℝ) :
    mellinD (trigTest b t h) u=trigTest b t (mellinD h) u+
      (if b then -t else t)*trigTest (!b) t (fun v => v*h v) u := by
  have id' : HasDerivAt (fun v : ℝ => t*v) t u := by simpa using (hasDerivAt_id u).const_mul t
  have sc := (dh u).hasDerivAt.mul ((Real.hasDerivAt_sin _).comp u id')
  have cc := (dh u).hasDerivAt.mul ((Real.hasDerivAt_cos _).comp u id')
  change HasDerivAt (sinTest t h) _ u at sc
  change HasDerivAt (cosTest t h) _ u at cc
  cases b <;> simp only [mellinD,trigTest,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,
    sc.deriv,cc.deriv,sinTest,cosTest,Function.comp_apply] <;> ring

private lemma mt_linear {h j : ℝ→ℝ} (c : ℝ) (s : ℂ)
    (hi : MellinConvergent (fun u => (h u:ℂ)) s)
    (ji : MellinConvergent (fun u => (j u:ℂ)) s) :
    mt (fun u => h u+c*j u) s=mt h s+(c:ℂ)*mt j s := by
  unfold MellinConvergent at hi ji
  unfold mt mellin
  simp only [smul_eq_mul] at *
  rw [← integral_const_mul,← integral_add hi (ji.const_mul (c:ℂ))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  push_cast
  ring

private theorem polynomial_bound (k : ℕ) (h : ℝ→ℝ) (hf : ContDiff ℝ k h)
    (a d : ℝ) (ap : 0<a) (d1 : d≤1) (supp : Function.support h⊆Icc a d) :
    ∃ C : ℝ, 0<C ∧ ∀ (b : Bool) (t : ℝ) (s : ℂ), 0<s.re → s.re≤1 →
      ‖mt (trigTest b t h) s‖*(1+|s.im|)^k≤C*(1+|t|)^k := by
  induction k generalizing h with
  | zero =>
    obtain ⟨C,cp,cap⟩ := base_bound h hf a d ap d1 supp
    exact ⟨C,cp,fun b t s sp s1 => by simpa using cap b t s sp s1⟩
  | succ k ih =>
    let j := fun u : ℝ => u*h u
    have sj : Function.support j⊆Icc a d := fun u hu => supp (right_ne_zero_of_mul hu)
    have sm : ContDiff ℝ k j := contDiff_id.mul (hf.of_le (by norm_cast; omega))
    have sd := mellinD_contDiff_finite k hf
    obtain ⟨C,cp,ca⟩ := ih (mellinD h) sd (mellinD_support_Icc supp)
    obtain ⟨K,kp,ka⟩ := ih j sm sj
    refine ⟨2*(C+K),by positivity,fun b t s sp s1 => ?_⟩
    let h₁ := trigTest b t (mellinD h)
    let h₂ := trigTest (!b) t j
    let c := if b then -t else t
    have ac : |c|=|t| := by cases b <;> simp [c]
    have hh₁ := (compact_mellin_regular _ (trigTest_smooth sd b t).continuous a d
      ((trigTest_support ..).trans (mellinD_support_Icc supp)) s sp).1
    have hh₂ := (compact_mellin_regular _ (trigTest_smooth sm (!b) t).continuous a d
      ((trigTest_support ..).trans sj) s sp).1
    have e : (1+s)*mt (trigTest b t h) s=mt h₁ s+(c:ℂ)*mt h₂ s := by
      have df : ContDiff ℝ 1 h := hf.of_le (by norm_cast; omega)
      unfold mt
      rw [← mellinD_transform_finite _ (trigTest_smooth (k:=1) df b t) a d ((trigTest_support ..).trans supp) s sp]
      change mt (mellinD (trigTest b t h)) s=_
      rw [show mellinD (trigTest b t h)=fun u => h₁ u+c*h₂ u from funext (step_point (df.differentiable (by norm_num)) b t)]
      exact mt_linear c s hh₁ hh₂
    have one : 1≤‖1+s‖ := by
      have r := Complex.re_le_norm (1+s)
      simp only [add_re,one_re] at r
      linarith
    have im : |s.im|≤‖1+s‖ := by simpa using Complex.abs_im_le_norm (1+s)
    have cap := norm_add_le (mt h₁ s) ((c:ℂ)*mt h₂ s)
    rw [← e,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,ac] at cap
    let X := 1+|s.im|
    let Y := 1+|t|
    have xp : 0≤X := by dsimp [X]; positivity
    have yp : 0≤Y := by dsimp [Y]; positivity
    have A := ca b t s sp s1
    have B := ka (!b) t s sp s1
    change ‖mt h₁ s‖*X^k≤C*Y^k at A
    change ‖mt h₂ s‖*X^k≤K*Y^k at B
    have comb := add_le_add A (mul_le_mul_of_nonneg_left B (abs_nonneg t))
    have first := mul_le_mul_of_nonneg_right cap (pow_nonneg xp k)
    have den : X≤2*‖1+s‖ := by dsimp [X]; linarith
    have scale := mul_le_mul_of_nonneg_right den (mul_nonneg (norm_nonneg (mt (trigTest b t h) s)) (pow_nonneg xp k))
    change ‖mt (trigTest b t h) s‖*X^(k+1)≤2*(C+K)*Y^(k+1)
    have slack := mul_nonneg (pow_nonneg yp k) (add_nonneg kp.le (mul_nonneg cp.le (abs_nonneg t)))
    dsimp only [Y] at *
    rw [pow_succ,pow_succ]
    linarith only [scale,first,comb,slack]

/-- Compact real additive phases cost at most four powers of one plus
their physical frequency in the character sampling estimate. -/
theorem modulated_mellin_axis (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ (b : Bool) (t : ℝ) (s : ℂ), 0<s.re → s.re≤1 →
      ‖mellin (fun u => (companion (trigTest b t f) u:ℂ)) s‖≤
        C*(1+|t|)^4*lineWeight s.im := by
  have reg := (FiniteModel.companion_contDiff hf).of_le (by norm_num : (4:WithTop ℕ∞)≤6)
  obtain ⟨C,cp,all⟩ := polynomial_bound 4 (companion f) reg hf.lower hf.upper hf.lower_pos
    hf.upper_lt_one.le (FiniteModel.companion_support_subset hf)
  refine ⟨C,cp,fun b t s sp s1 => ?_⟩
  have eq : companion (trigTest b t f)=trigTest b t (companion f) := by
    funext u
    cases b <;> simp [trigTest,sinTest,cosTest,companion,mul_assoc]
  rw [eq]
  change ‖mt (trigTest b t (companion f)) s‖≤C*(1+|t|)^4*(1+|s.im|)⁻¹^4
  rw [inv_pow,← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  exact all b t s sp s1

#print axioms modulated_mellin_axis
end GoldbachSpectral435.CriticalCharacter
