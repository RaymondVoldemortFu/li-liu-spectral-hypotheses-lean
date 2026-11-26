module
public import Samples
public import Reflection
public import ConditionalGoldbach.Proofs.FiniteModelDouble
public import ConditionalGoldbach.Proofs.SpectralModelOperator

/-! The original continuous model on the first physical block. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.ReflectionModel

private lemma model_entry (N : ℕ) [NeZero N] {a : ℝ} (ap : 0<a) (ha : a<beta)
    (s z : ℂ) (hs : s∈strip a beta) (hz : z∈strip a beta) :
    weightedAnalyticKernel (continuedModel N) s z =
      paperInner (modelOperator ha N (evaluationVector z)) (evaluationVector s) := by
  obtain ⟨B,bp,G⟩ := continuedModel_uniform_power_bound
  obtain ⟨hk,hc⟩ := weightedAnalyticKernel_inputs_at ap ha (continuedModel N)
    (continuedModel_differentiableOn N (NeZero.pos N)) _ (by positivity) (G a ap ha N (NeZero.pos N))
  have herm : HermitianKernel (weightedAnalyticKernel (continuedModel N)) := by
    apply weightedAnalyticKernel_hermitian
    intro s z
    rw [continuedModel_conj,Complex.conj_conj,continuedModel_symmetric]
  exact kernelOperator_pairing_of_hardyColumns ha N _ herm hk hc s z hs hz

/-- On every real compact C6 weight in (0,1), the quadratic form of the
original model is the continuous reflection, with no GRH premise. -/
theorem smooth_model (N : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (ha : alpha N<beta) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let x := testVector N N (NeZero.pos N) f hf
    paperInner (modelOperator ha N x) x = -(FiniteModel.modelMass f * singularSeries N : ℝ) := by
  intro x
  let σ : ℝ := 1/9
  have sp : 0<σ := by dsimp [σ]; norm_num
  have su : σ≤1/9 := le_rfl
  have ab : σ∈Ioo (alpha N) beta := by
    have lg := (Real.lt_log_iff_exp_lt (by exact_mod_cast NeZero.pos N : 0<(N:ℝ))).mpr big
    constructor
    · change 1/Real.log N<1/9; exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
    · norm_num [σ,beta]
  let M := modelOperator ha N
  have rep := testVector_rep N N (NeZero.pos N) f hf σ sp ab
  have eqN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  rw [← FiniteModel.model_double_mellin N even (NeZero.pos N) f hf σ sp su]
  change paperInner (M x) x=_
  rw [← rep (M x)]
  unfold finiteFunctionalValue verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  let s := line σ t
  have st : s∈strip (alpha N) beta := by simpa [s,strip,line] using ab
  change (N:ℂ)^s*mellinWeight f s*(1+s)*fourierLaplace (M x) s=_
  rw [finite_functional_kernel_recovery N (NeZero.pos N) (companion f) σ ab x rep M
    (weightedAnalyticKernel (continuedModel N)) (model_entry N (large_alpha_pos big) ha) s st]
  unfold verticalMellin
  rw [mul_left_comm _ ((2*(Real.pi:ℂ))⁻¹),← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with t'
  let z := line σ t'
  have hd := mellin_betaDomain_line σ sp su t t'
  rw [← weighted_continuedModel_cancel N (NeZero.pos N) f s z hd]
  change (N:ℂ)^s*mellinWeight f s*(1+s)*((N:ℂ)^z*mellinWeight f z*(1+z)*
    weightedAnalyticKernel (continuedModel N) s (conj z))=_
  have nz (v : ℝ) : 1+line σ v ≠ 0 := by
    intro h
    have r := congrArg Complex.re h
    simp [line] at r
    linarith
  have ns : 1+s≠0 := nz t
  have nt : 1+z≠0 := nz t'
  simp only [weightedAnalyticKernel,conj_conj]
  rw [cpow_add _ _ eqN]
  field_simp

private lemma interior {N : ℕ} [NeZero N] (big : Real.exp 10<(N:ℝ)) :
    (1/9:ℝ)∈Ioo (alpha N) beta := by
  have lg := (Real.lt_log_iff_exp_lt (by exact_mod_cast NeZero.pos N : 0<(N:ℝ))).mpr big
  exact ⟨one_div_lt_one_div_of_lt (by norm_num) (by linarith),by norm_num [beta]⟩

/-- Sampling an original compact-weight Riesz vector on a monomial gives
the actual Mangoldt weight divided by the square root of the modulus. -/
theorem companion_sample (N n : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ))
    (ha : alpha N<beta) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    LocalPrimeForm.coefficient (testVector N N (NeZero.pos N) f hf) n = -(sampleValue N n f:ℂ) := by
  by_cases nz : n=0
  · simp [nz,LocalPrimeForm.coefficient,sampleValue,mangoldt]
  have hn := Nat.pos_of_ne_zero nz
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have mp : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  let x := testVector N N (NeZero.pos N) f hf
  let σ : ℝ := 1/9
  have ab := interior big
  have sp : 0<σ := by norm_num [σ]
  have rep := testVector_rep N N (NeZero.pos N) f hf σ sp ab (diagonalHardyVector n)
  have sample : inner ℂ x (diagonalHardyVector n)=(companion f (n/(N:ℝ)):ℂ) := by
    change paperInner (diagonalHardyVector n) x=_
    rw [← rep,FiniteModel.mellinWeight_inversion hf σ sp _ (div_pos np mp)]
    unfold finiteFunctionalValue verticalMellin
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    let s := line σ t
    have st : s∈strip (alpha N) beta := by simpa [s,strip,line,σ] using ab
    have ns : 1+s≠0 := by
      intro h; have v := congrArg Complex.re h; norm_num [s,line,σ] at v
    have nc : (N:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast NeZero.ne N))
    change (N:ℂ)^s*mellinWeight f s*(1+s)*fourierLaplace (diagonalHardyVector n) s=_
    rw [(diagonalHardyVector_spec ha (large_alpha_pos big).le n hn).1 s st]
    change (N:ℂ)^s*mellinWeight f s*(1+s)*diagonalVector n s=
      mellinWeight f s*((n/(N:ℝ):ℝ):ℂ)^(-s)
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg np.le mp.le]
    simp only [Complex.ofReal_natCast,Complex.cpow_neg,diagonalVector]
    field_simp
  change -(mangoldt n:ℂ)*(n:ℂ)^(-(1/2:ℂ))*inner ℂ x (diagonalHardyVector n)=_
  rw [sample,Complex.cpow_neg]
  have sq : (Real.sqrt (n:ℝ):ℂ)=(n:ℂ)^(1/2:ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow np.le]; norm_num
  rw [← sq]
  unfold companion sampleValue
  rw [Real.sqrt_div np.le]
  push_cast
  have sn : (Real.sqrt (n:ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr np).ne'
  field_simp

/-- The physical support of the original Riesz vector ends before the
right endpoint of its compactly supported Mellin weight. -/
theorem test_support (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) (f : ℝ→ℝ)
    (hf : FiniteModelWeight f) :
    let x := testVector N N (NeZero.pos N) f hf
    ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log N → x t=0 := by
  intro x
  let c : ℝ := (Real.sqrt (2*Real.pi))⁻¹
  let g : ℝ→ℝ := fun t => c*mellinD (companion f) (Real.exp (-t)/N)
  have cf : ContDiff ℝ 3 (companion f) := (FiniteModel.companion_contDiff hf).of_le (by norm_num)
  have sf := FiniteModel.companion_support_subset hf
  have cg : Continuous g := by
    apply Continuous.const_mul
    apply (mellinD_contDiff_finite 2 cf).continuous.comp
    fun_prop
  have gs : HasCompactSupport g :=
    (finite_derivativeDensity_hasCompactSupport N (NeZero.pos N) _ _ _ hf.lower_pos sf).mul_left
  let v := weightedTestVector (alpha N) beta g cg gs
  have eq : x=v := by
    apply ext_inner_right ℂ
    intro ψ
    change paperInner ψ x=paperInner ψ v
    rw [← testVector_rep N N (NeZero.pos N) f hf (1/9) (by norm_num) (interior big) ψ,
      finiteFunctionalValue_density N (NeZero.pos N) _ cf _ _ sf _ (by norm_num) (interior big)]
    dsimp only [v]
    rw [weightedTestVector_pairing]
    dsimp only [g,c]
    push_cast
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [eq]
  filter_upwards [(weighted_test_memLp (alpha N) beta g cg gs).coeFn_toLp] with t ht h
  have nr : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have one : 1≤Real.exp (-t)/N := by
    apply (le_div_iff₀ nr).mpr
    rw [one_mul,← Real.exp_log nr]
    exact Real.exp_le_exp.mpr (by linarith)
  have zero : mellinD (companion f) (Real.exp (-t)/N)=0 := by
    by_contra ne
    exact (not_lt_of_ge (mellinD_support_Icc sf ne).2) (hf.upper_lt_one.trans_le one)
  exact ht.trans (by simp [g,zero])

/-- The discrepancy between the reflected prime sum and its continuous
density on every compact C6 test of the original problem. -/
theorem smooth_residual (N : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let x := testVector N N (NeZero.pos N) f hf
    paperInner (residualOperator ha N x) x =
      ((FiniteModel.modelMass f*singularSeries N -
        ∑ n ∈ Finset.range N, if n.Coprime N then sampleValue N n f*sampleValue N (N-n) f else 0 : ℝ):ℂ) := by
  intro x
  change inner ℂ x (residualOperator ha N x)=_
  have supp := test_support N big f hf
  rw [Reflection.residual_first_block N even big grh ha x x supp supp,
    show inner ℂ x (modelOperator ha N x)=_ from smooth_model N even big ha f hf]
  have sums : Reflection.goldbachLine N x x =
      ((∑ n ∈ Finset.range N, if n.Coprime N then sampleValue N n f*sampleValue N (N-n) f else 0 : ℝ):ℂ) := by
    unfold Reflection.goldbachLine
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [x]
    by_cases cop : n.Coprime N
    · simp [ite_eq_left cop,companion_sample N _ big ha f hf]
    · simp [ite_eq_right cop]
  rw [sums,Complex.ofReal_sub]
  push_cast
  ring

#print axioms smooth_residual
#print axioms smooth_model
end GoldbachSpectral435.ReflectionModel
