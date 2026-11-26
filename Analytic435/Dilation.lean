module
public import ConditionalGoldbach.Proofs.FiniteModelDouble

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
namespace GoldbachSpectral435
open ConditionalGoldbach

/-- Mellin inversion of the original continued density at all dilations r ≥ 1. -/
theorem dilated_sampling (r : ℝ) (hr : 1≤r) (N : ℕ) (he : Even N) (hn : 0 < N)
    (φ : ℝ → ℝ) (smooth : FiniteModelWeight φ) (a : ℝ) (ha : 0 < a) :
    verticalMellin a (fun w => (r:ℂ)^w*continuedDensity N w*
      mellin (fun y => (signedConvolution φ y:ℂ)) w) =
      ∑' j : ℕ, (singularSeries ((j+1)*N):ℂ) * (signedConvolution φ (((j+1:ℕ):ℝ)/r):ℂ) := by
  have rp : 0<r := zero_lt_one.trans_le hr
  have rc : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr rp.ne'
  let J := signedConvolution φ
  let R := regularizedModelMellin N φ
  obtain ⟨b,D,hab,hb,hD,hgrowth⟩ := exists_mellin_comparison_line N a ha
  obtain ⟨C,hC,dec⟩ := FiniteModel.regularizedModelMellin_uniform_decay N φ smooth a b ha hab D hD hgrowth
  let V := fun w : ℂ => (r:ℂ)^w*R w
  have deriv (w : ℂ) (hw : w.re ∈ Icc a b) : DifferentiableAt ℂ V w :=
    (differentiableAt_id.const_cpow (Or.inl rc)).mul
      (FiniteModel.regularizedModelMellin_differentiableAt N φ smooth (ha.trans_le hw.1))
  have bound (x : ℝ) (hx : x ∈ Icc a b) (t : ℝ) :
      ‖V (line x t)‖ ≤ (r^b*C)*(1+|t|)⁻¹^2 := by
    have pow : ‖(r:ℂ)^(line x t)‖ = r^x := by
      simpa [line] using Complex.norm_cpow_eq_rpow_re_of_pos (x := r) (y := line x t) rp
    dsimp only [V,R]
    rw [norm_mul,pow]
    exact (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hr hx.2) (dec x hx t)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hae := FiniteModel.regularizedModelMellin_line_ae N φ smooth a
  have sh := verticalMellin_shift_of_ae_eq V
    (fun w => (r:ℂ)^w*continuedDensity N w*mellin (fun y => (J y:ℂ)) w) a b _
    hab deriv bound (by filter_upwards [hae] with t ht; dsimp [V,R,J]; rw [ht,mul_assoc])
  have su := (density_sampling_coeff_summable N he hn b hb).mul_right (r^b)
  have scaled : Summable (fun j : ℕ => ‖(singularSeries ((j+1)*N):ℂ)‖ *
      Real.rpow (((j+1:ℕ):ℝ)/r) (-b)) := by
    apply su.congr
    intro j
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow (by positivity : (0:ℝ) ≤ (j+1:ℕ)) rp.le,
      Real.rpow_neg rp.le b,div_inv_eq_mul]
    ring
  have raw := finite_mellin_inversion_hasSum J
    ((FiniteModel.signedConvolution_contDiff φ smooth).of_le (by norm_num)) _ _
    (FiniteModel.signedConvolution_support φ smooth) b (by linarith)
    (fun j : ℕ => ((j+1:ℕ):ℝ)/r) (fun j => (singularSeries ((j+1)*N):ℂ)) (fun j => by positivity) scaled
  change verticalMellin a (fun w => (r:ℂ)^w*continuedDensity N w*
    mellin (fun y => (J y:ℂ)) w) = _
  rw [sh.2,raw.tsum_eq]
  unfold verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let w := line b t
  have hw : 1 < w.re := by simpa [w,line] using hb
  have not1 : w ≠ 1 := by intro h; rw [h,one_re] at hw; linarith
  change (r:ℂ)^w*regularizedModelMellin N φ w = _
  rw [FiniteModel.regularizedModelMellin_eq N φ smooth not1,
    ← densitySeries_eq_continuedDensity N he hn hw,
    ← density_mellin_integrand_series N he hn J w hw, ← tsum_mul_left]
  apply tsum_congr
  intro j
  have pos : (0:ℝ) < (j+1:ℕ) := by positivity
  change (r:ℂ)^w * (_ * _ * (j+1:ℕ)^(-w)) = _ * _ * ((((j+1:ℕ):ℝ)/r:ℝ):ℂ)^(-w)
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg pos.le rp.le,
    Complex.ofReal_natCast, cpow_neg (r:ℂ),div_inv_eq_mul]
  ring

/-- Absolute convergence and the full two-variable inversion after dilation. -/
theorem dilated_double_sampling (r : ℝ) (hr : 1≤r) (N : ℕ) (he : Even N) (hn : 0 < N)
    (φ : ℝ → ℝ) (smooth : FiniteModelWeight φ) (σ : ℝ) (hs : 0 < σ) (hu : σ ≤ 1/9) :
    Integrable (fun p : ℝ × ℝ => (r:ℂ)^(line σ p.1+line σ p.2)*
      (mellinWeight φ (line σ p.1)*mellinWeight φ (line σ p.2)*continuedDensity N (line σ p.1+line σ p.2)*betaKernel (line σ p.1) (line σ p.2))) ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z => (r:ℂ)^(s+z) *
      (mellinWeight φ s * mellinWeight φ z * continuedDensity N (s+z) * betaKernel s z))) =
      ∑' j : ℕ, (singularSeries ((j+1)*N):ℂ) * (signedConvolution φ (((j+1:ℕ):ℝ)/r):ℂ) := by
  have rp : 0<r := zero_lt_one.trans_le hr
  have rc : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr rp.ne'
  let F := fun s z : ℂ => mellinWeight φ s * mellinWeight φ z * continuedDensity N (s+z) * betaKernel s z
  let G := fun s z : ℂ => (r:ℂ)^(s+z) * F s z
  have hi := FiniteModel.model_double_integrable N φ smooth σ hs hu
  have hc : Continuous (fun p : ℝ × ℝ => (r:ℂ)^(line σ p.1+line σ p.2)) :=
    Continuous.const_cpow (by unfold line; fun_prop) (Or.inl rc)
  have hb : ∀ᵐ p : ℝ × ℝ, ‖(r:ℂ)^(line σ p.1+line σ p.2)‖ ≤ r^(2*σ) := by
    filter_upwards [] with p
    have eqn := Complex.norm_cpow_eq_rpow_re_of_pos (x := r) (y := line σ p.1+line σ p.2) rp
    simpa [line,two_mul] using eqn.le
  have joint : Integrable (fun p : ℝ × ℝ => G (line σ p.1) (line σ p.2)) :=
    hi.bdd_mul hc.aestronglyMeasurable hb
  refine ⟨joint,?_⟩
  change verticalMellin σ (fun s => verticalMellin σ (fun z => G s z)) = _
  rw [double_verticalMellin_diagonal G σ joint, ← dilated_sampling r hr N he hn φ smooth (2*σ) (by linarith)]
  unfold verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let w := line (2*σ) t
  have hw : w.re = 2*σ := by simp [w,line]
  have inner := (FiniteModel.signedConvolution_mellin_beta φ smooth σ hs hu w hw).2
  have point (s : ℂ) : G s (w-s) = ((r:ℂ)^w*continuedDensity N w) *
      (mellinWeight φ s*mellinWeight φ (w-s)*betaKernel s (w-s)) := by
    dsimp [G,F]
    rw [add_sub_cancel]
    ring
  change (2*(Real.pi:ℂ))⁻¹ * (∫ u : ℝ, G (line σ u) (w-line σ u)) = _
  simp_rw [point]
  rw [integral_const_mul]
  change _ = ((r:ℂ)^w*continuedDensity N w)*mellin (fun y => (signedConvolution φ y:ℂ)) w
  rw [inner]
  unfold verticalMellin
  ring

#print axioms dilated_double_sampling
end GoldbachSpectral435
