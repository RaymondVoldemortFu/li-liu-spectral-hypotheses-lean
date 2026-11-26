module
public import FiniteDiscrepancy

/-! Reality of the mixed Hilbert and residual pairings on real Mellin tests. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PhysicalTests

lemma sample_line {N : ℕ} [NeZero N] (big : Real.exp 10<(N:ℝ)) : (1/9:ℝ)∈Ioo (alpha N) beta := by
  have lg := (Real.lt_log_iff_exp_lt (by exact_mod_cast NeZero.pos N : 0<(N:ℝ))).mpr big
  exact ⟨one_div_lt_one_div_of_lt (by norm_num) (by linarith),by norm_num [beta]⟩

theorem real_vector (N M : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) (mp : 0<M) (f : ℝ→ℝ)
    (hf : FiniteModelWeight f) :
    let x := testVector N M mp f hf
    ∀ᵐ t ∂hardyMeasure (alpha N) beta, conj (x t)=x t := by
  intro x
  let c : ℝ := (Real.sqrt (2*Real.pi))⁻¹
  let g : ℝ→ℝ := fun t => c*mellinD (companion f) (Real.exp (-t)/M)
  have cf : ContDiff ℝ 3 (companion f) := (FiniteModel.companion_contDiff hf).of_le (by norm_num)
  have sf := FiniteModel.companion_support_subset hf
  have cg : Continuous g := by
    apply Continuous.const_mul
    apply (mellinD_contDiff_finite 2 cf).continuous.comp
    fun_prop
  have gs : HasCompactSupport g :=
    (finite_derivativeDensity_hasCompactSupport M mp _ _ _ hf.lower_pos sf).mul_left
  let v := weightedTestVector (alpha N) beta g cg gs
  have eq : x=v := by
    apply ext_inner_right ℂ
    intro ψ
    change paperInner ψ x=paperInner ψ v
    rw [← testVector_rep N M mp f hf (1/9) (by norm_num) (sample_line big) ψ,
      finiteFunctionalValue_density M mp _ cf _ _ sf _ (by norm_num) (sample_line big)]
    dsimp only [v]
    rw [weightedTestVector_pairing]
    dsimp only [g,c]
    push_cast
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [eq]
  filter_upwards [(weighted_test_memLp (alpha N) beta g cg gs).coeFn_toLp] with t ht
  exact (congrArg conj ht).trans ((Complex.conj_ofReal _).trans ht.symm)

theorem inner_real (N M : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) (mp : 0<M) (f g : ℝ→ℝ)
    (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
    let x := testVector N M mp f hf
    let y := testVector N M mp g hg
    conj (inner ℂ x y)=inner ℂ x y := by
  intro x y
  rw [L2.inner_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [real_vector N M big mp f hf,real_vector N M big mp g hg] with t fx gy
  change conj (y t*conj (x t))=y t*conj (x t)
  rw [fx,map_mul,fx,gy]

theorem residual_real (N M : ℕ) [NeZero N] (mp : 0<M) (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
    let x := testVector N M mp f hf
    let y := testVector N M mp g hg
    conj (paperInner (residualOperator ha N y) x)=paperInner (residualOperator ha N y) x := by
  intro x y
  let σ : ℝ := 1/9
  have sp : 0<σ := by norm_num [σ]
  have ab := sample_line big
  obtain ⟨v,w,pair⟩ := mixed_kernel N M mp even big grh ha (companion f) (companion g)
    ((FiniteModel.companion_contDiff hf).of_le (by norm_num)) ((FiniteModel.companion_contDiff hg).of_le (by norm_num))
    hf.lower_pos hg.lower_pos (FiniteModel.companion_support_subset hf) (FiniteModel.companion_support_subset hg)
  obtain ⟨rv,rw',entry⟩ := pair σ sp ab
  have ex : v=x := by
    apply ext_inner_right ℂ
    intro ψ
    exact (rv ψ).symm.trans (testVector_rep N M mp f hf σ sp ab ψ)
  have ey : w=y := by
    apply ext_inner_right ℂ
    intro ψ
    exact (rw' ψ).symm.trans (testVector_rep N M mp g hg σ sp ab ψ)
  rw [ex,ey] at entry
  rw [entry]
  let K (s z : ℂ) := (M:ℂ)^(s+z)*mellinWeight f s*mellinWeight g z*residual N s z
  change conj (verticalMellin σ (fun s => verticalMellin σ (K s)))=_
  have realK (s z : ℂ) : conj (K (conj s) (conj z))=K s z := by
    have power := ofReal_cpow_conj (M:ℝ) (by exact_mod_cast mp) (conj s+conj z)
    simp only [Complex.ofReal_natCast,map_add,conj_conj] at power
    dsimp only [K]
    rw [map_mul,map_mul,map_mul,← power,← mellinWeight_conj,← mellinWeight_conj,residual_conj,conj_conj,conj_conj]
  rw [verticalMellin_conj]
  simp_rw [verticalMellin_conj,realK]
  rfl

#print axioms inner_real
#print axioms residual_real
end GoldbachSpectral435.PhysicalTests
