module
public import ThresholdDiscrepancy
public import ReflectionEnergy
public import PhysicalCriterion

/-! A sufficient estimate for the unrestricted existence assertion, in
terms of a squared integral of the explicit rectangular discrepancy. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Filter
namespace GoldbachSpectral435.CumulativeKernel
open GoldbachPrimitive FiniteDiscrepancy

def factor (M : ℕ) (a u : ℝ) :=
  Real.sqrt (energyWeight M a u*(max u 0)^3)

def normalizedKernel (N k : ℕ) (p : ℝ×ℝ) :=
  signedKernel N k p/(factor (k*N) (alpha N) p.1*factor (k*N) (alpha N) p.2)

def kernelSize (N k : ℕ) :=
  Real.sqrt (∫ p, (normalizedKernel N k p)^2 ∂thresholds)

private lemma factor_cont (M : ℕ) {a : ℝ} (ab : a<beta) : Continuous (factor M a) :=
  Real.continuous_sqrt.comp ((energyWeight_continuous M ab).mul ((continuous_id.max continuous_const).pow 3))

private lemma factor_pos {M : ℕ} (mp : 0<M) (a : ℝ) {u : ℝ} (up : 0<u) : 0<factor M a u := by
  have r : 0<(M:ℝ) := by exact_mod_cast mp
  unfold factor
  rw [weight_eq mp up,max_eq_left up.le]
  positivity

private lemma physical_derivative {f : ℝ→ℝ} (hf : FiniteModelWeight f) {u : ℝ} (up : 0<u) :
    physicalDensity f u= -(u*Real.sqrt u*deriv (profile f) u) := by
  have su := Real.sqrt_pos.mpr up
  have d := ((hf.smooth.differentiable (by decide) u).hasDerivAt.div (Real.hasDerivAt_sqrt up.ne') su.ne').deriv
  unfold physicalDensity
  rw [show deriv (profile f) u=_ from d]
  field_simp
  rw [Real.sq_sqrt up.le]
  ring

/-- Energy identity in the threshold coordinate. -/
theorem derivative_norm (M : ℕ) (mp : 0<M) (a : ℝ) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    (∫ u, (factor M a u*deriv (profile f) u)^2 ∂unitMeasure)=2*Real.pi*normFunctional M f a := by
  rw [norm_integral M mp f hf a,intervalIntegral.integral_of_le zero_le_one]
  have c : 2*Real.pi≠0 := by positivity
  rw [← mul_assoc,mul_inv_cancel₀ c,one_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have up := hu.1
  have en : 0≤energyWeight M a u := by rw [weight_eq mp up]; positivity
  dsimp only [factor]
  rw [max_eq_left up.le,mul_pow,Real.sq_sqrt (mul_nonneg en (pow_nonneg up.le _)),physical_derivative hf up]
  rw [neg_sq,mul_pow,mul_pow,Real.sq_sqrt up.le]
  ring

private lemma cauchy {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α→ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x*g x ∂μ| ≤ Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (∫ x, g x^2 ∂μ) := by
  have hc : (2:ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have h := integral_mul_norm_le_Lp_mul_Lq hc
    (by simpa using hf : MemLp f (ENNReal.ofReal 2) μ)
    (by simpa using hg : MemLp g (ENNReal.ofReal 2) μ)
  simp only [Real.norm_eq_abs,Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow] at h
  apply le_trans _ h
  simpa only [Real.norm_eq_abs,abs_mul] using norm_integral_le_integral_norm (μ:=μ) (fun x => f x*g x)

private lemma unit_ae : ∀ᵐ p ∂thresholds, p.1∈Ioc (0:ℝ) 1 ∧ p.2∈Ioc (0:ℝ) 1 := by
  unfold thresholds
  have one : ∀ᵐ t ∂unitMeasure, t∈Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  filter_upwards [(Measure.quasiMeasurePreserving_fst (ν:=unitMeasure)).ae one,
    (Measure.quasiMeasurePreserving_snd (μ:=unitMeasure)).ae one] with p h j
  exact ⟨h,j⟩

/-- At every dilation, the square integral of the normalized arithmetic
kernel bounds the exact quadratic form on every real compact test. -/
theorem spectral_bound (N k : ℕ) [NeZero N] (kp : 0<k) (he : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta)
    (u2 : MemLp (normalizedKernel N k) 2 thresholds) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let x := testVector N (k*N) (Nat.mul_pos kp (NeZero.pos N)) f hf
    ‖paperInner (residualOperator ha N x) x‖≤2*Real.pi*kernelSize N k*‖x‖^2 := by
  intro x
  let M := k*N
  have mp : 0<M := Nat.mul_pos kp (NeZero.pos N)
  let g := fun u => factor M (alpha N) u*deriv (profile f) u
  let G := fun p : ℝ×ℝ => g p.1*g p.2
  have cg : Continuous g := (factor_cont M ha).mul ((profile_smooth hf).continuous_deriv (by decide))
  have i2 : Integrable (fun u => g u^2) unitMeasure := ((cg.pow 2).intervalIntegrable 0 1).1
  have ig : Integrable (fun p => G p^2) thresholds := by
    simpa only [G,mul_pow,thresholds] using i2.mul_prod i2
  have cm : Continuous G := (cg.comp continuous_fst).mul (cg.comp continuous_snd)
  have gm : MemLp G 2 thresholds := (memLp_two_iff_integrable_sq_norm cm.aestronglyMeasurable).mpr
      (by simpa only [Real.norm_eq_abs,sq_abs] using ig)
  have eq : (fun p => derivativePair f p*signedKernel N k p)=ᵐ[thresholds] (fun p => G p*normalizedKernel N k p) := by
    filter_upwards [unit_ae] with p hp
    have l := (factor_pos mp (alpha N) hp.1.1).ne'
    have r := (factor_pos mp (alpha N) hp.2.1).ne'
    change deriv (profile f) p.1*deriv (profile f) p.2*signedKernel N k p=
      ((factor M (alpha N) p.1*deriv (profile f) p.1)*(factor M (alpha N) p.2*deriv (profile f) p.2))*
      (signedKernel N k p/(factor M (alpha N) p.1*factor M (alpha N) p.2))
    field_simp
  have square : (∫ p, G p^2 ∂thresholds)=(∫ u, g u^2 ∂unitMeasure)^2 := by
    unfold G thresholds
    simp_rw [mul_pow]
    rw [integral_prod_mul (fun u => g u^2) (fun u => g u^2),pow_two]
  have pos : 0≤∫ u, g u^2 ∂unitMeasure := integral_nonneg (fun u => sq_nonneg _)
  have bound := cauchy _ gm u2
  rw [square,Real.sqrt_sq pos] at bound
  have h := (exact_form N k kp he big grh ha f hf).1
  rw [exact_kernel N k kp he big grh ha f hf,Complex.norm_real,Real.norm_eq_abs,integral_congr_ae eq,h]
  apply bound.trans_eq
  change (∫ u, (factor M (alpha N) u*deriv (profile f) u)^2 ∂unitMeasure)*kernelSize N k=_
  rw [derivative_norm M mp _ f hf]
  dsimp only [M]
  ring

/-- A uniform little-o bound on this explicit two-dimensional integral
implies the full existential Hypothesis S on all eligible even moduli. -/
theorem existence_of_kernel_decay
    (decay : ∀ ε : ℝ, 0<ε → EvenEventually (fun N => ∀ [NeZero N], GRH N →
      ∀ k : ℕ, 0<k → MemLp (normalizedKernel N k) 2 thresholds ∧
        2*Real.pi*kernelSize N k≤ε*singularSeries N)) : ∃ h, HypothesisS h := by
  apply FiniteDiscrepancy.some_S_iff.mpr
  intro ε ep
  obtain ⟨K,s⟩ := (decay ε ep).and evenEventually_large
  refine ⟨K,fun N hn he inst grh k kp f hf => ?_⟩
  obtain ⟨all,big⟩ := s N hn he
  have ha := (large_parameters big).2.2
  obtain ⟨m,d⟩ := all grh k kp
  obtain ⟨nrm,val⟩ := exact_form N k kp he big grh ha f hf
  rw [← val,← nrm]
  exact (spectral_bound N k kp he big grh ha m f hf).trans (mul_le_mul_of_nonneg_right d (sq_nonneg _))

#print axioms spectral_bound
#print axioms existence_of_kernel_decay
end GoldbachSpectral435.CumulativeKernel
