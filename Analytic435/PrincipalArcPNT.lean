module
public import RationalPrimeArcs
public import WeightedPrimeLimit
public import MathlibNt.AnalyticNumberTheory.LargeSieve.PrincipalPNTSourceFromMediumPNT

/-! A principal major-arc approximation with a uniform logarithmic error
for the oscillatory archimedean test. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Finset Filter ConditionalGoldbach MeasureTheory Chebyshev Set
namespace GoldbachSpectral435.CriticalCharacter
open GoldbachSieve AnalyticNumberTheory.LargeSieve

lemma real_prefix_error (A : ℝ) (ap : 0<A) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ M : ℕ in atTop, ∀ x : ℝ, 0≤x → x≤M →
      |psi x-x|≤K*M/(Real.log M)^A+1 := by
  obtain ⟨K,kp,est⟩ := principalLambdaPrefixMaxError_one_eventually_le A ap
  refine ⟨K,kp,?_⟩
  filter_upwards [est] with M bound
  intro x xp xm
  let n := ⌊x⌋₊
  have lower : (n:ℝ)≤x := Nat.floor_le xp
  have upper : x<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have nm : n≤M := by exact_mod_cast lower.trans xm
  have m : n∈range (M+1) := mem_range.mpr (by omega)
  rw [principalLambdaPrefixMaxError_one_eq_psi_prefixMax] at bound
  have atn := (Finset.le_max' _ _ (mem_image_of_mem (fun y : ℕ => |psi (y:ℝ)-(y:ℝ)|) m)).trans bound
  nth_rw 1 [psi_eq_psi_coe_floor x]
  apply (abs_sub_le (psi (n:ℝ)) (n:ℝ) x).trans
  rw [abs_of_nonpos (sub_nonpos.mpr lower)]
  linarith

private lemma derivative_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ D : ℝ, 0<D ∧ ∀ (b : Bool) (t u : ℝ), u∈Icc (0:ℝ) 1 →
      |deriv (trigTest b t f) u|≤D*(1+|t|) := by
  have dc := hf.smooth.continuous_deriv (by decide)
  obtain ⟨J,j⟩ := isCompact_Icc (a:=(0:ℝ)) (b:=1) |>.exists_bound_of_continuousOn dc.continuousOn
  obtain ⟨F,h⟩ := isCompact_Icc (a:=(0:ℝ)) (b:=1) |>.exists_bound_of_continuousOn hf.continuous.continuousOn
  let D := |F|+|J|+1
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro b t u loc
  have cap : |f u|≤D := (h u loc).trans (by dsimp [D]; linarith [le_abs_self F,abs_nonneg J])
  have der : |deriv f u|≤D := (j u loc).trans (by dsimp [D]; linarith [le_abs_self J,abs_nonneg F])
  have id' : HasDerivAt (fun v : ℝ => t*v) t u := by simpa using (hasDerivAt_id u).const_mul t
  have df := (hf.smooth.differentiable (by decide) u).hasDerivAt
  have sine := df.mul ((Real.hasDerivAt_sin _).comp u id')
  have cosine := df.mul ((Real.hasDerivAt_cos _).comp u id')
  change HasDerivAt (sinTest t f) _ u at sine
  change HasDerivAt (cosTest t f) _ u at cosine
  have mulcap (x y : ℝ) (ax : |x|≤1) (ay : |y|≤1) :
      |deriv f u*x+f u*(y*t)|≤D*(1+|t|) := by
    apply (abs_add_le ..).trans
    simp only [abs_mul]
    have a := (mul_le_of_le_one_right (abs_nonneg _) ax).trans der
    have c := (mul_le_of_le_one_right (abs_nonneg _) ay).trans cap
    rw [← mul_assoc (|f u|)]
    linarith only [a,mul_le_mul_of_nonneg_right c (abs_nonneg t)]
  cases b
  · change |deriv (cosTest t f) u|≤_
    rw [cosine.deriv]
    exact mulcap _ _ (Real.abs_cos_le_one _) (by simpa only [abs_neg] using Real.abs_sin_le_one (t*u))
  · change |deriv (sinTest t f) u|≤_
    rw [sine.deriv]
    exact mulcap _ _ (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)

lemma abel_error (M : ℕ) (mp : 0<M) (f : ℝ→ℝ) (hf : FiniteModelWeight f) (D V : ℝ)
    (dcap : ∀ u∈Icc (0:ℝ) 1, |deriv f u|≤D) (pcap : ∀ x : ℝ, 0≤x → x≤M → |psi x-x|≤V) :
    |primeSum M f-(M:ℝ)*unitIntegral f|≤D*V := by
  have mr : 0<(M:ℝ) := Nat.cast_pos.mpr mp
  let a := fun u : ℝ => psi (M*u)/M
  have mono : Monotone a := fun u v h => div_le_div_of_nonneg_right (psi_mono (mul_le_mul_of_nonneg_left h mr.le)) mr.le
  have dc := hf.smooth.continuous_deriv (by decide)
  have ia : IntervalIntegrable (fun u => deriv f u*a u) volume 0 1 :=
    (mono.intervalIntegrable ..).continuousOn_mul dc.continuousOn
  have ib : IntervalIntegrable (fun u : ℝ => deriv f u*u) volume 0 1 :=
    (dc.mul continuous_id).intervalIntegrable (μ:=volume) 0 1
  have eq : primeSum M f/M-unitIntegral f= -(∫ u in (0:ℝ)..1,deriv f u*(a u-u)) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub ia ib,primeSum_integral M mp f hf,integral_by_parts f hf,unitIntegral]
    dsimp only [a]
    ring
  have norm := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1)
    (f:=fun u => deriv f u*(a u-u)) (C:=D*(V/(M:ℝ))) (by
      intro u hu
      rw [uIoc_of_le zero_le_one] at hu
      have p := pcap ((M:ℝ)*u) (mul_nonneg mr.le hu.1.le) (mul_le_of_le_one_right mr.le hu.2)
      have ub : |a u-u|≤V/(M:ℝ) := by
        have rew : a u-u=(psi (M*u)-M*u)/M := by dsimp only [a]; field_simp
        rw [rew,abs_div,abs_of_pos mr]
        exact div_le_div_of_nonneg_right p mr.le
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (dcap u ⟨hu.1.le,hu.2⟩) ub (abs_nonneg _) ((abs_nonneg _).trans (dcap u ⟨hu.1.le,hu.2⟩)))
  simp only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] at norm
  have bound : |primeSum M f/M-unitIntegral f|≤D*(V/(M:ℝ)) := by rwa [eq,abs_neg]
  have id : primeSum M f-(M:ℝ)*unitIntegral f=(primeSum M f/M-unitIntegral f)*M := by field_simp
  rw [id,abs_mul,abs_of_pos mr]
  exact (mul_le_mul_of_nonneg_right bound mr.le).trans_eq (by field_simp)

theorem oscillatory_pnt (f : ℝ→ℝ) (hf : FiniteModelWeight f) (A : ℝ) (ap : 0<A) :
    ∃ D K : ℝ, 0<D ∧ 0<K ∧ ∀ᶠ M : ℕ in atTop, ∀ (b : Bool) (t : ℝ),
      |primeSum M (trigTest b t f)-(M:ℝ)*unitIntegral (trigTest b t f)|≤
        D*(1+|t|)*(K*M/(Real.log M)^A+1) := by
  obtain ⟨D,dp,der⟩ := derivative_bound f hf
  obtain ⟨K,kp,bound⟩ := real_prefix_error A ap
  refine ⟨D,K,dp,kp,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ),bound] with M mp est
  exact fun b t => abel_error M mp _ (trigWeight hf b t) _ _ (der b t) est

#print axioms oscillatory_pnt
end GoldbachSpectral435.CriticalCharacter
