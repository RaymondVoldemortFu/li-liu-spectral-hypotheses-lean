module
public import PrimeCorrelations
public import ConditionalGoldbach.Proofs.SpectralDiagonalVector

/-! Support of the monomial Hardy vectors and cancellation below half the modulus. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex MeasureTheory Filter Set
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PhysicalSupport
open GoldbachSpectral435.PerronApproximation

def profile (n : ℕ) : ℝ → ℂ :=
  (Iic (-Real.log n)).indicator (fun t : ℝ => (Real.exp t:ℂ))

private lemma profile_mem {a : ℝ} (ap : 0≤a) (n : ℕ) :
    MemLp (profile n) 2 (hardyMeasure a beta) := by
  have meas : Measurable (profile n) :=
    (Complex.continuous_ofReal.comp Real.continuous_exp).measurable.indicator measurableSet_Iic
  apply (memLp_two_iff_integrable_sq_norm meas.aestronglyMeasurable).mpr
  change Integrable _ (volume.withDensity (fun t => ENNReal.ofReal (hardyWeight a beta t)))
  rw [integrable_withDensity_iff (hardyWeight_continuous a beta).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have h1 := integrableOn_exp_mul_Iic (by linarith : 0<2*(1+a)) (-Real.log n)
  have h2 := integrableOn_exp_mul_Iic (by norm_num [beta] : 0<2*(1+beta)) (-Real.log n)
  apply ((h1.add h2).integrable_indicator measurableSet_Iic).congr
  filter_upwards with t
  simp only [profile,ENNReal.toReal_ofReal (hardyWeight_pos a beta t).le]
  by_cases ht : t ∈ Iic (-Real.log n)
  · simp only [indicator_of_mem ht,Pi.add_apply,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),hardyWeight,← Real.exp_nat_mul,Nat.cast_ofNat]
    rw [show 2*(1+a)*t=2*a*t+2*t by ring,show 2*(1+beta)*t=2*beta*t+2*t by ring,
      Real.exp_add,Real.exp_add]
    ring
  · simp [indicator_of_notMem ht]

private lemma profile_transform {a : ℝ} (ap : 0≤a) {n : ℕ} (np : 0<n)
    {s : ℂ} (hs : s ∈ strip a beta) :
    (∫ t : ℝ, (profile_mem ap n).toLp (profile n) t * Complex.exp (s*t)) =
      ((n:ℂ)⁻¹)*(diagonalVector n s) := by
  have ae := (volume_absolutelyContinuous_hardyMeasure a beta).ae_eq (profile_mem ap n).coeFn_toLp
  have eq : (∫ t : ℝ, (profile_mem ap n).toLp (profile n) t * Complex.exp (s*t)) =
      ∫ t in Iic (-Real.log n), Complex.exp ((1+s)*t) := by
    rw [← integral_indicator measurableSet_Iic]
    apply integral_congr_ae
    filter_upwards [ae] with t ht
    rw [ht]
    by_cases mem : t ∈ Iic (-Real.log n)
    · simp only [profile,indicator_of_mem mem,Complex.ofReal_exp,← Complex.exp_add,add_mul,one_mul]
    · simp [profile,indicator_of_notMem mem]
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have nc : (n:ℂ)≠0 := by exact_mod_cast np.ne'
  have pos : 0<(1+s).re := by simp; linarith [hs.1]
  rw [eq,integral_exp_mul_complex_Iic pos]
  have power : Complex.exp ((1+s)*((-Real.log n:ℝ):ℂ)) = (n:ℂ)^(-1-s) := by
    rw [Complex.cpow_def_of_ne_zero nc,Complex.ofReal_neg,Complex.ofReal_log nr.le,Complex.ofReal_natCast]
    congr 1; ring
  rw [power,show (-1-s:ℂ)=(-1)+(-s) by ring,Complex.cpow_add _ _ nc,Complex.cpow_neg_one]
  unfold diagonalVector
  ring

/-- In the original weighted Fourier realization the monomial has a
one-sided exponential density ending at minus the logarithm of its index. -/
theorem diagonal_profile {a : ℝ} (ap : 0≤a) (ab : a<beta) {n : ℕ} (np : 0<n) :
    (diagonalHardyVector (a:=a) n : ℝ → ℂ) =ᵐ[hardyMeasure a beta]
      fun t => ((Real.sqrt (2*Real.pi):ℂ)*(n:ℂ))*profile n t := by
  let u := (profile_mem ap n).toLp (profile n)
  let C : ℂ := (Real.sqrt (2*Real.pi):ℂ)*(n:ℂ)
  have id : diagonalHardyVector (a:=a) n = C • u := by
    apply fourierLaplace_injective_strip ab
    intro s hs
    rw [(diagonalHardyVector_spec ab ap n np).1 s hs,fourierLaplace_smul C u hs]
    unfold fourierLaplace
    rw [show (∫ t : ℝ, u t*Complex.exp (s*t))=_ from profile_transform ap np hs]
    have k : (Real.sqrt (2*Real.pi):ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0<2*Real.pi)).ne'
    have nc : (n:ℂ)≠0 := by exact_mod_cast np.ne'
    dsimp only [C]
    field_simp
  rw [id]
  filter_upwards [Lp.coeFn_smul C u,(profile_mem ap n).coeFn_toLp] with t h j
  exact h.trans (by simp only [Pi.smul_apply,smul_eq_mul,C,u,j])

/-- A time-domain vector supported strictly above the monomial endpoint
has zero pairing with that monomial. -/
theorem inner_zero {a : ℝ} (ap : 0≤a) (ab : a<beta) {n : ℕ} (np : 0<n)
    (f : HardySpace a beta) (supp : ∀ᵐ t ∂hardyMeasure a beta, t≤ -Real.log n → f t=0) :
    inner ℂ f (diagonalHardyVector n)=0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [supp,diagonal_profile ap ab np] with t hf hd
  by_cases h : t≤ -Real.log n
  · simp [hf h]
  · have mem : t ∉ Iic (-Real.log n) := h
    rw [hd,profile,indicator_of_notMem mem,mul_zero,inner_zero_right]
    rfl

/-- Odd-character orthogonality cancels the full off-diagonal form on a
physical interval, at every polynomial length. -/
theorem short_pairs_zero {N Y : ℕ} (yp : 0<Y) (short : 2*Y≤N) (m : ℕ)
    (ap : 0≤alpha N) (ab : alpha N<beta) (f : HardySpace (alpha N) beta)
    (supp : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → f t=0) :
    primePairForm N m f=0 := by
  have vanish (n : ℕ) (hi : Y≤n) : testCoefficient N m n f=0 := by
    have bound := Real.log_le_log (by exact_mod_cast yp : 0<(Y:ℝ)) (Nat.cast_le.mpr hi)
    have gone := inner_zero ap ab (yp.trans_le hi) f (supp.mono (fun t h ht => h (by linarith)))
    simp only [testCoefficient,gone,mul_zero]
  have z : testCoefficient N m 0 f=0 := by simp [testCoefficient,mangoldt]
  unfold primePairForm
  apply Finset.sum_eq_zero
  intro n _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hn : Y≤n
  · simp [vanish n hn]
  by_cases hj : Y≤j
  · simp [vanish j hj]
  by_cases zn : n=0
  · simp [zn,z]
  by_cases zj : j=0
  · simp [zj,z]
  obtain ⟨a,b⟩ := residue_diagonals (by omega : 0<N) (by omega : 0<n) (by omega : n<N)
    (by omega : 0<j) (by omega : j<N)
  have no : n+j≠N := by omega
  have sign : offDiagonalSign N n j=0 := by
    unfold offDiagonalSign residueSign
    simp only [a,b,no,ite_false,sub_zero]
    by_cases eq : n=j
    · subst j; simp [Nat.coprime_mul_iff_left]
    · simp [eq]
  rw [sign,mul_zero]

/-- On the original strip, all unit vectors supported above minus the
logarithm of half the modulus have a uniformly small arithmetic remainder. -/
theorem short_arithmetic_bound :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
    Real.exp 10<(N:ℝ) → GRH N → ∀ (ha : alpha N<beta) (Y : ℕ), 0<Y → 2*Y≤N →
    ∀ f : HardySpace (alpha N) beta,
      (∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → f t=0) →
      ‖inner ℂ f ((arithmeticOperator ha N-diagonalOperator ha N) f)‖ ≤
      C/(Real.log N)^16*‖f‖^2 := by
  obtain ⟨C,cp,err⟩ := prime_pair_error
  refine ⟨C,cp,?_⟩
  intro N inst even large g ha Y yp ys f supp
  have e := err N inst even large g ha f
  rw [short_pairs_zero yp ys _ (large_alpha_pos large).le ha f supp,zero_sub,
    residualOperator_components_at _ N (large_alpha_pos large) (large_parameters large).1 g ha,
    sub_apply,inner_sub_right,sub_neg_eq_add,sub_add_cancel] at e
  exact e

#print axioms short_arithmetic_bound
end GoldbachSpectral435.PhysicalSupport
