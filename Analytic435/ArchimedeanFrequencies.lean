module
public import PrimeLineFrequencies
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Fourier inversion for the original real compact test functions. The
frequency variable here uses cycles per unit of physical length. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Complex Set
open scoped FourierTransform
namespace GoldbachSpectral435.GoldbachSieve

def complexTest (f : ℝ→ℝ) (u : ℝ) : ℂ := f u

def angular (ξ : ℝ) : ℝ := 2*Real.pi*ξ

lemma unitIntegral_eq {f : ℝ→ℝ} (hf : FiniteModelWeight f) : unitIntegral f=∫ u,f u := by
  rw [unitIntegral,intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u outside
  by_contra nonzero
  exact outside (Ioo_subset_Ioc_self (hf.mem_support_unit nonzero))

lemma complex_test_continuous {f : ℝ→ℝ} (hf : FiniteModelWeight f) : Continuous (complexTest f) :=
  Complex.continuous_ofReal.comp hf.continuous

lemma complex_test_support {f : ℝ→ℝ} (hf : FiniteModelWeight f) : HasCompactSupport (complexTest f) :=
  hf.hasCompactSupport.comp_left Complex.ofReal_zero

lemma complex_test_integrable {f : ℝ→ℝ} (hf : FiniteModelWeight f) : Integrable (complexTest f) :=
  (complex_test_continuous hf).integrable_of_hasCompactSupport (complex_test_support hf)

lemma continuous_test_transform {f : ℝ→ℝ} (hf : FiniteModelWeight f) : Continuous (𝓕 (complexTest f)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (complex_test_integrable hf)

theorem integrable_test_transform {f : ℝ→ℝ} (hf : FiniteModelWeight f) : Integrable (𝓕 (complexTest f)) := by
  let F := complexTest f
  have smooth : ContDiff ℝ 2 F := Complex.ofRealCLM.contDiff.comp (hf.smooth.of_le (by norm_num))
  have compact (n : ℕ) : HasCompactSupport (iteratedDeriv n F) := by
    induction n with
    | zero => simpa using complex_test_support hf
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have ints (k : ℕ) (hk : k≤2) : Integrable (iteratedDeriv k F) :=
    (smooth.continuous_iteratedDeriv k (by exact_mod_cast hk)).integrable_of_hasCompactSupport (compact k)
  let C := (∫ u, ‖F u‖)+(4*Real.pi^2)⁻¹*(∫ u, ‖iteratedDeriv 2 F u‖)
  have cp : 0≤C := by dsimp only [C]; positivity
  apply (integrable_inv_one_add_sq.const_mul C).mono (continuous_test_transform hf).aestronglyMeasurable
  filter_upwards with ξ
  have e := Real.one_add_sq_mul_norm_fourier_le smooth ints ξ
  change (1+ξ^2)*‖𝓕 F ξ‖≤C at e
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg cp (inv_nonneg.mpr (by positivity)))]
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity)).mpr (by linarith only [e])

theorem test_transform (f : ℝ→ℝ) (hf : FiniteModelWeight f) (ξ : ℝ) :
    𝓕 (complexTest f) ξ=(unitIntegral (cosTest (angular ξ) f):ℂ)-
      (unitIntegral (sinTest (angular ξ) f):ℂ)*I := by
  let t := angular ξ
  rw [Real.fourier_real_eq_integral_exp_smul,unitIntegral_eq (cosWeight hf _),unitIntegral_eq (sinWeight hf _)]
  have per (u : ℝ) : cexp ((↑(-2*Real.pi*u*ξ):ℂ)*I) • complexTest f u=
      complexTest (cosTest t f) u-complexTest (sinTest t f) u*I := by
    rw [show -2*Real.pi*u*ξ= -(t*u) by dsimp only [t,angular]; ring,Complex.exp_mul_I]
    rw [← Complex.ofReal_cos (-(t*u)),← Complex.ofReal_sin (-(t*u))]
    simp only [complexTest,cosTest,sinTest,smul_eq_mul,Real.cos_neg,Real.sin_neg,ofReal_neg,ofReal_mul]
    ring
  simp_rw [per]
  rw [integral_sub (complex_test_integrable (cosWeight hf t)) ((complex_test_integrable (sinWeight hf t)).mul_const I),
    integral_mul_const]
  simp only [complexTest,integral_complex_ofReal,t]

def kernelWave (f : ℝ→ℝ) (y ξ : ℝ) : ℂ :=
  cexp ((↑(angular ξ*y):ℂ)*I)*𝓕 (complexTest f) ξ

lemma integrable_kernelWave {f : ℝ→ℝ} (hf : FiniteModelWeight f) (y : ℝ) :
    Integrable (kernelWave f y) := by
  have ct := continuous_test_transform hf
  apply (integrable_test_transform hf).mono
  · apply Continuous.aestronglyMeasurable
    unfold kernelWave angular; fun_prop
  · filter_upwards with ξ
    simp [kernelWave,norm_exp]

theorem kernelWave_inverse {f : ℝ→ℝ} (hf : FiniteModelWeight f) (y : ℝ) :
    (∫ ξ,kernelWave f y ξ)=(f y:ℂ) := by
  have inv := (complex_test_integrable hf).fourierInv_fourier_eq (integrable_test_transform hf)
    (complex_test_continuous hf).continuousAt (v:=y)
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at inv
  apply Eq.trans _ inv
  apply integral_congr_ae
  filter_upwards with ξ
  unfold kernelWave angular
  rw [smul_eq_mul,show -2*Real.pi*ξ*(-y)=2*Real.pi*ξ*y by ring]

theorem kernelWave_real (f : ℝ→ℝ) (hf : FiniteModelWeight f) (y ξ : ℝ) :
    (kernelWave f y ξ).re=Real.cos (angular ξ*y)*unitIntegral (cosTest (angular ξ) f)+
      Real.sin (angular ξ*y)*unitIntegral (sinTest (angular ξ) f) := by
  rw [kernelWave,test_transform f hf,Complex.exp_mul_I,← Complex.ofReal_cos (angular ξ*y),
    ← Complex.ofReal_sin (angular ξ*y)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  ring

#print axioms kernelWave_inverse
end GoldbachSpectral435.GoldbachSieve
