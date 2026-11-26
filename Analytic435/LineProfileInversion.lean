module
public import ArchimedeanFrequencies
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The full integral of the limiting archimedean profile is the
ordinary convolution on the specified sum or difference line. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Complex Filter
open scoped Topology FourierTransform
namespace GoldbachSpectral435.GoldbachSieve

def realPartner (sign : Bool) (x u : ℝ) := if sign then x-u else u-x

def archimedeanLine (sign : Bool) (x : ℝ) (f g : ℝ→ℝ) :=
  ∫ u in (0:ℝ)..1, f u*g (realPartner sign x u)

private lemma profile_integral (sign : Bool) (f g : ℝ→ℝ) (hf : FiniteModelWeight f)
    (hg : FiniteModelWeight g) (x ξ : ℝ) :
    (∫ u,f u*(kernelWave g (realPartner sign x u) ξ).re)=
      frequencyProfile sign (angular ξ*x) (angular ξ) f g := by
  let t := angular ξ
  let C := unitIntegral (cosTest t g)
  let S := unitIntegral (sinTest t g)
  let s : ℝ := if sign then 1 else -1
  let A := Real.cos (t*x)*C+s*Real.sin (t*x)*S
  let B := Real.sin (t*x)*C-s*Real.cos (t*x)*S
  have per (u : ℝ) : f u*(kernelWave g (realPartner sign x u) ξ).re=
      A*cosTest t f u+B*sinTest t f u := by
    rw [kernelWave_real g hg]
    change f u*(Real.cos (t*realPartner sign x u)*C+Real.sin (t*realPartner sign x u)*S)=_
    cases sign <;> simp only [A,B,realPartner,Bool.false_eq_true,ite_false,ite_true,mul_sub,
      Real.cos_sub,Real.sin_sub,s,cosTest,sinTest] <;> ring
  simp_rw [per]
  have ci := (cosWeight hf t).continuous.integrable_of_hasCompactSupport (μ:=volume) (cosWeight hf t).hasCompactSupport
  have si := (sinWeight hf t).continuous.integrable_of_hasCompactSupport (μ:=volume) (sinWeight hf t).hasCompactSupport
  rw [integral_add (ci.const_mul A) (si.const_mul B),integral_const_mul,integral_const_mul,
    ← unitIntegral_eq (cosWeight hf t),← unitIntegral_eq (sinWeight hf t)]
  change A*unitIntegral (cosTest t f)+B*unitIntegral (sinTest t f)=phaseMix sign (t*x) _ _ _ _
  dsimp only [phaseMix,A,B,s,C,S,t]
  ring

theorem profile_inversion (sign : Bool) (f g : ℝ→ℝ) (hf : FiniteModelWeight f)
    (hg : FiniteModelWeight g) (x : ℝ) :
    let profile := fun ξ => frequencyProfile sign (angular ξ*x) (angular ξ) f g
    Integrable profile ∧ (∫ ξ,profile ξ)=archimedeanLine sign x f g := by
  intro profile
  let W := fun ξ u => f u*(kernelWave g (realPartner sign x u) ξ).re
  have fi := hf.continuous.integrable_of_hasCompactSupport (μ:=volume) hf.hasCompactSupport
  have gc := continuous_test_transform hg
  have joint : Integrable (Function.uncurry W) (volume.prod volume) := by
    apply ((integrable_test_transform hg).norm.mul_prod fi.norm).mono
    · apply Continuous.aestronglyMeasurable
      have fc := hf.continuous
      cases sign <;> change Continuous (fun z : ℝ×ℝ => _) <;>
        simp only [W,Function.uncurry,realPartner,Bool.false_eq_true,ite_false,ite_true,kernelWave,angular] <;> fun_prop
    · filter_upwards with ⟨ξ,u⟩
      change ‖f u*(kernelWave g (realPartner sign x u) ξ).re‖≤‖‖𝓕 (complexTest g) ξ‖*‖f u‖‖
      have b := Complex.abs_re_le_norm (kernelWave g (realPartner sign x u) ξ)
      simp only [kernelWave,norm_mul,norm_exp,Complex.mul_I_re,Complex.ofReal_im,neg_zero,Real.exp_zero,one_mul] at b
      rw [norm_mul,Real.norm_eq_abs ((kernelWave ..).re),Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),mul_comm ‖f u‖]
      exact mul_le_mul_of_nonneg_right b (norm_nonneg _)
  have eq (ξ : ℝ) : (∫ u,W ξ u)=profile ξ := profile_integral sign f g hf hg x ξ
  have expr : profile=(fun ξ => ∫ u,W ξ u) := funext fun ξ => (eq ξ).symm
  rw [expr]
  refine ⟨joint.integral_prod_left,?_⟩
  rw [integral_integral_swap joint]
  have per (u : ℝ) : (∫ ξ,W ξ u)=f u*g (realPartner sign x u) := by
    dsimp only [W]
    rw [integral_const_mul]
    congr 1
    have e := integral_re (integrable_kernelWave hg (realPartner sign x u))
    rw [kernelWave_inverse hg] at e
    exact e
  simp_rw [per]
  rw [archimedeanLine,intervalIntegral.integral_of_le zero_le_one]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u out
  have z : f u=0 := by by_contra h; exact out (Set.Ioo_subset_Ioc_self (hf.mem_support_unit h))
  simp [z]

#print axioms profile_inversion
end GoldbachSpectral435.GoldbachSieve
