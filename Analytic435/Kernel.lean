module
public import ConditionalGoldbach.Proofs.FiniteQuadratic
public import ConditionalGoldbach.Proofs.HardyArithmeticTheorems
public import ConditionalGoldbach.Proofs.FiniteModelBasic
public import ConditionalGoldbach.Proofs.QuadraticNormChange

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Complex
open scoped ComplexConjugate
namespace GoldbachSpectral435
open ConditionalGoldbach

/-- The modulus of the L-functions and the scale of the two Mellin tests are
independent. Both vectors are constructed, and the operator is the arithmetic
operator of Li and Liu on its original Hardy strip. -/
theorem mixed_kernel (N M : ℕ) [NeZero N] (hM : 0 < M) (he : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (grh : GRH N) (ha : alpha N < beta)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    {A B C D : ℝ} (hA : 0 < A) (hC : 0 < C)
    (sf : Function.support f ⊆ Icc A B) (sg : Function.support g ⊆ Icc C D) :
    ∃ x y : HardySpace (alpha N) beta, ∀ σ : ℝ, 0 < σ → σ ∈ Ioo (alpha N) beta →
      (∀ ψ, finiteFunctionalValue M f σ ψ = paperInner ψ x) ∧
      (∀ ψ, finiteFunctionalValue M g σ ψ = paperInner ψ y) ∧
      paperInner (residualOperator ha N y) x = verticalMellin σ (fun s => verticalMellin σ (fun z =>
        (M:ℂ)^(s+z)*mellin (fun u => (f u:ℂ)) s*mellin (fun u => (g u:ℂ)) z*
          residual N s z)) := by
  obtain ⟨x,hx⟩ := finite_functional_riesz_exists (a := alpha N) M hM f hf A B hA sf
  obtain ⟨y,hy⟩ := finite_functional_riesz_exists (a := alpha N) M hM g hg C D hC sg
  refine ⟨x,y,fun σ hσ hs => ⟨hx σ hσ hs,hy σ hσ hs,?_⟩⟩
  have hM' : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← hx σ hσ hs]
  unfold finiteFunctionalValue verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let s := line σ t
  have hst : s ∈ strip (alpha N) beta := by simpa [s,strip,line] using hs
  change (M:ℂ)^s*mellin (fun u => (f u:ℂ)) s*(1+s)*fourierLaplace (residualOperator ha N y) s = _
  rw [finite_functional_kernel_recovery M hM g σ hs y (hy σ hσ hs) (residualOperator ha N)
    (weightedKernel N) (proposition_5_4_kernel_pairing N he hlarge grh ha) s hst]
  unfold verticalMellin
  rw [mul_left_comm _ ((2*(Real.pi:ℂ))⁻¹),← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t'
  let z := line σ t'
  have nz (r : ℝ) : 1+line σ r ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp [line] at h
    linarith
  change (M:ℂ)^s*mellin (fun u => (f u:ℂ)) s*(1+s)*
    ((M:ℂ)^z*mellin (fun u => (g u:ℂ)) z*(1+z)*weightedKernel N s (conj z)) = _
  simp only [weightedKernel,conj_conj]
  rw [cpow_add _ _ hM']
  have hs' : 1+s ≠ 0 := nz t
  have hz' : 1+z ≠ 0 := nz t'
  field_simp
  ring

/-- Exact norm for a finite-smooth weight of arbitrary compact support in
(0,1), with independent Mellin scale M and Hardy left endpoint a. -/
theorem mixed_vector_norm {a : ℝ} (M : ℕ) (hM : 0 < M) (φ : ℝ → ℝ)
    (smooth : FiniteModelWeight φ) (σ : ℝ) (hs : 0 < σ) (hab : σ ∈ Ioo a beta)
    (x : HardySpace a beta) (rep : ∀ ψ, finiteFunctionalValue M (companion φ) σ ψ = paperInner ψ x) :
    ‖x‖^2 = normFunctional M φ a := by
  let c : ℝ := (Real.sqrt (2*Real.pi))⁻¹
  let g : ℝ → ℝ := fun t => c*mellinD (companion φ) (Real.exp (-t)/M)
  have cf : ContDiff ℝ 3 (companion φ) := (FiniteModel.companion_contDiff smooth).of_le (by norm_num)
  have support := FiniteModel.companion_support_subset smooth
  have cg : Continuous g := by
    apply Continuous.const_mul
    apply (mellinD_contDiff_finite 2 cf).continuous.comp
    fun_prop
  have gs : HasCompactSupport g :=
    (finite_derivativeDensity_hasCompactSupport M hM _ _ _ smooth.lower_pos support).mul_left
  let v := weightedTestVector a beta g cg gs
  have same : x = v := by
    apply ext_inner_right ℂ
    intro ψ
    change paperInner ψ x = paperInner ψ v
    rw [← rep,finiteFunctionalValue_density M hM _ cf _ _ support σ hs hab]
    dsimp only [v]
    rw [weightedTestVector_pairing]
    dsimp [g,c]
    push_cast
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  rw [same,normFunctional_density_integral M hM φ a]
  dsimp only [v]
  rw [weightedTestVector_norm_sq]
  dsimp only [g]
  change (∫ t : ℝ, (c*derivativeWeight φ (Real.exp (-t)/M))^2 / hardyWeight a beta t) = _
  simp only [mul_pow,mul_div_assoc,integral_const_mul]
  congr 1
  dsimp [c]
  rw [inv_pow,Real.sq_sqrt (by positivity)]

/-- Both the matrix entry and both norms of its test vectors are calculated
on the published operator with no additional analytic hypotheses. -/
theorem mixed_kernel_norms (N M : ℕ) [NeZero N] (hM : 0 < M) (he : Even N)
    (hlarge : Real.exp 10 < (N:ℝ)) (grh : GRH N) (ha : alpha N < beta)
    (f g : ℝ → ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (σ : ℝ) (hs : 0 < σ) (hab : σ ∈ Ioo (alpha N) beta) :
    ∃ x y : HardySpace (alpha N) beta,
      ‖x‖^2 = normFunctional M f (alpha N) ∧ ‖y‖^2 = normFunctional M g (alpha N) ∧
      paperInner (residualOperator ha N y) x = verticalMellin σ (fun s => verticalMellin σ (fun z =>
        (M:ℂ)^(s+z)*mellinWeight f s*mellinWeight g z*residual N s z)) := by
  obtain ⟨x,y,rep⟩ := mixed_kernel N M hM he hlarge grh ha (companion f) (companion g)
    ((FiniteModel.companion_contDiff hf).of_le (by norm_num))
    ((FiniteModel.companion_contDiff hg).of_le (by norm_num)) hf.lower_pos hg.lower_pos
    (FiniteModel.companion_support_subset hf) (FiniteModel.companion_support_subset hg)
  obtain ⟨rx,ry,entry⟩ := rep σ hs hab
  exact ⟨x,y,mixed_vector_norm M hM f hf σ hs hab x rx,mixed_vector_norm M hM g hg σ hs hab y ry,entry⟩

#print axioms mixed_kernel_norms
#print axioms mixed_kernel
end GoldbachSpectral435
