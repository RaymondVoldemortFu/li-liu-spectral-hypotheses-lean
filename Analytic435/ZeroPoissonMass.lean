module
public import ConditionalGoldbach.Proofs.CharacterPoissonAnchor
public import ConditionalGoldbach.Proofs.SpectralPoissonConvolution

/-! The weighted mass of the Poisson zero sum stays bounded as the
vertical line approaches the critical axis. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set
namespace GoldbachSpectral435.CriticalCharacter
attribute [local instance] conductorNeZero

private lemma integrable_sum {ι : Type*} [Countable ι] {F : ι→ℝ→ℝ}
    (hi : ∀ i,Integrable (F i)) (hs : Summable (fun i => ∫ t : ℝ,‖F i t‖)) :
    Integrable (fun t : ℝ => ∑' i,F i t) := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hi i).1),?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun i => (hi i).1.enorm)]
  have eq (i : ι) : (∫⁻ t : ℝ, ‖F i t‖ₑ)=‖∫ t : ℝ,‖F i t‖‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi i).norm,ENNReal.coe_nnreal_eq,coe_nnnorm]
    change ENNReal.ofReal (∫ t,|F i t|)=ENNReal.ofReal ‖∫ t,|F i t|‖
    rw [Real.norm_of_nonneg (integral_nonneg (fun t => abs_nonneg (F i t)))]
  simp_rw [eq]
  exact lt_top_iff_ne_top.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hs.abs))

theorem zero_poisson_mass {q : ℕ} [NeZero q] (χ : Character q) (nc : χ≠1) (σ : ℝ) (sp : 0<σ) :
    Integrable (fun t => poissonKernelReal 1 t*zeroPoisson χ σ t) ∧
    (∫ t : ℝ,poissonKernelReal 1 t*zeroPoisson χ σ t)=zeroPoisson χ (1+σ) 0 := by
  let Z := ZeroIndex χ.primitiveCharacter
  let γ := fun p : Z => p.val.1.im
  let F := fun (p : Z) (t : ℝ) => Real.pi*(poissonKernelReal 1 t*poissonKernelReal σ (γ p-t))
  have pos (p : Z) (t : ℝ) : 0≤F p t := mul_nonneg Real.pi_pos.le
    (mul_nonneg (poissonKernelReal_bounds 1 zero_lt_one _).1 (poissonKernelReal_bounds σ sp _).1)
  have hi (p : Z) : Integrable (F p) := ((lemma_6_4_poisson_convolution σ sp (γ p)).1).const_mul _
  have per (p : Z) : (∫ t,F p t)=(1+σ)/((1+σ)^2+(0-γ p)^2) := by
    dsimp only [F]
    rw [integral_const_mul,← realConvolution,(lemma_6_4_poisson_convolution σ sp (γ p)).2.1]
    simp only [poissonKernelReal,zero_sub,even_two.neg_pow]
    field_simp
  have hs := primitive_zero_poisson_summable χ.primitiveCharacter (primitiveCharacter_ne_one_of_ne_one χ nc)
    χ.primitiveCharacter_isPrimitive (1+σ) 0 (by positivity)
  let _ : Countable Z := by
    apply Set.countable_univ_iff.mp
    convert hs.countable_support using 1
    ext p
    simp only [Set.mem_univ,Function.mem_support,true_iff]
    positivity
  have sn : Summable (fun p : Z => ∫ t,‖F p t‖) := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (pos _ _),per]
    exact hs
  have each (t : ℝ) : poissonKernelReal 1 t*zeroPoisson χ σ t=∑' p : Z,F p t := by
    unfold zeroPoisson
    rw [← tsum_mul_left]
    apply tsum_congr
    intro p
    dsimp only [F,γ,poissonKernelReal]
    rw [show (p.val.1.im-t)^2=(t-p.val.1.im)^2 by ring]
    field_simp
  simp only [each]
  refine ⟨integrable_sum hi sn,?_⟩
  rw [← integral_tsum_of_summable_integral_norm hi sn]
  exact tsum_congr per

theorem zero_poisson_mass_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : Character q), χ≠1 → ∀ σ : ℝ, 0<σ → σ≤1 →
      (∫ t : ℝ,poissonKernelReal 1 t*zeroPoisson χ σ t)≤C*Real.log (2*q) := by
  obtain ⟨C,cp,anchor⟩ := zeroPoisson_anchor_bound
  refine ⟨3*C,by positivity,?_⟩
  intro q inst χ nc σ sp s1
  have a : 0<1+σ := by positivity
  have summ (x : ℝ) (xp : 0<x) := primitive_zero_poisson_summable χ.primitiveCharacter
    (primitiveCharacter_ne_one_of_ne_one χ nc) χ.primitiveCharacter_isPrimitive x 0 xp
  have point (y : ℝ) : (1+σ)/((1+σ)^2+y^2)≤3*((3/2)/((3/2)^2+y^2)) := by
    rw [mul_div_assoc',div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [sq_nonneg σ,sq_nonneg y,sp,s1,mul_le_mul_of_nonneg_right s1 (sq_nonneg y)]
  rw [(zero_poisson_mass χ nc σ sp).2]
  have b : zeroPoisson χ (1+σ) 0≤3*zeroPoisson χ (3/2) 0 := by
    unfold zeroPoisson
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun p => point _) (summ _ a) ((summ _ (by norm_num : (0:ℝ)<3/2)).mul_left 3)
  have ref := anchor q inst χ nc 0
  simp only [abs_zero,zero_add] at ref
  rw [mul_comm (q:ℝ) 2] at ref
  linarith only [b,ref]

#print axioms zero_poisson_mass
#print axioms zero_poisson_mass_bound
end GoldbachSpectral435.CriticalCharacter
