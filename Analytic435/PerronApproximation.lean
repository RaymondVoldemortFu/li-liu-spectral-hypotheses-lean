module
public import ConditionalGoldbach.Proofs.CharacterAverage
public import ConditionalGoldbach.Proofs.CharacterPoissonAnchor

/-! Explicit finite Dirichlet polynomials for the odd-character correlations on
the moving Li–Liu strip. The cutoff is independent of character and height. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex MeasureTheory Filter Set
open scoped Topology ComplexConjugate
namespace GoldbachSpectral435.PerronApproximation
attribute [local instance] ConditionalGoldbach.conductorNeZero

/-- Uniform tail of any finite Euler factor, using only that its prime is at
most the modulus. A logarithmic cutoff retains the first m geometric terms. -/
private theorem geometric_tail (q : ℂ) {L X : ℝ} (hL : 0 ≤ L) (hq : ‖q‖ ≤ 4/5)
    (hX : 1<X) (p m : ℕ) (hp : 1 ≤ p) (cut : ((p^m : ℕ) : ℝ) ≤ Real.sqrt X) :
    ‖∑' k : ℕ, (L:ℂ)*q^(k+1) * (1-(smoothedPerronWeight X (p^(k+1)) : ℂ))‖ ≤
      (4/5:ℝ)^m*(4*L) := by
  let a (k : ℕ) := (L:ℂ)*q^(k+1)
  let e (k : ℕ) := a k * (1-(smoothedPerronWeight X (p^(k+1)) : ℂ))
  have hA := geometric_coefficients_norm_sum q hq hL
  have cap (k : ℕ) : ‖e k‖ ≤ ‖a k‖ := by
    have w := smoothedPerronWeight_nonneg_le_one hX (p^(k+1))
    have n : ‖(1:ℂ)-(smoothedPerronWeight X (p^(k+1)):ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub, Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr w.2)]
      linarith [w.1]
    exact (norm_mul _ _).le.trans (mul_le_of_le_one_right (norm_nonneg _) n)
  have es : Summable (fun k => ‖e k‖) := hA.1.of_nonneg_of_le (fun _ => norm_nonneg _) cap
  have pref : ∑ k ∈ Finset.range m, e k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have small : ((p^(k+1):ℕ):ℝ) ≤ Real.sqrt X :=
      (by exact_mod_cast pow_le_pow_right₀ hp (Finset.mem_range.mp hk) : ((p^(k+1):ℕ):ℝ) ≤ ((p^m:ℕ):ℝ)).trans cut
    have w : smoothedPerronWeight X (p^(k+1)) = 1 := ite_eq_left small
    simp [e,w]
  have tailBound (k : ℕ) : ‖e (k+m)‖ ≤ (4/5:ℝ)^m*‖a k‖ := by
    apply (cap (k+m)).trans
    rw [show a (k+m) = q^m*a k by dsimp [a]; rw [show k+m+1=m+(k+1) by omega,pow_add]; ring,
      norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hq m) (norm_nonneg _)
  change ‖∑' k, e k‖ ≤ _
  rw [← es.of_norm.sum_add_tsum_nat_add m,pref,zero_add]
  calc
    _ ≤ ∑' k, ‖e (k+m)‖ := norm_tsum_le_tsum_norm ((summable_nat_add_iff m).mpr es)
    _ ≤ ∑' k, (4/5:ℝ)^m * ‖a k‖ := Summable.tsum_le_tsum tailBound
      ((summable_nat_add_iff m).mpr es) (hA.1.mul_left _)
    _ ≤ _ := by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hA.2 (by positivity)

/-- A retained local Euler series agrees with the original factor up to an
exponentially small error in the number of retained prime powers. -/
private theorem local_euler_tail {d : ℕ} [NeZero d] (χ : Character d) {p : ℕ}
    (hp : p.Prime) {u : ℂ} (hu : 1/2 ≤ u.re) {X : ℝ} (hX : 1<X)
    (m : ℕ) (cut : ((p^m : ℕ) : ℝ) ≤ Real.sqrt X) :
    let f := fun v : ℂ => χ p*(Real.log p : ℂ)/((p:ℂ)^(u+v)-χ p)
    ‖f 0 - ∫ t : ℝ, f (line 1 (2*Real.pi*t)) *
      smoothedPerronKernel X (line 1 (2*Real.pi*t))‖ ≤ (4/5:ℝ)^m*(4*Real.log p) := by
  intro f
  let q := χ p/(p:ℂ)^u
  let a := fun k : ℕ => (Real.log p:ℂ)*q^(k+1)
  have lp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hq := euler_geometric_ratio_norm_le χ hp hu
  have hA := (geometric_coefficients_norm_sum q hq lp).1
  have value : ∑' k : ℕ, a k = f 0 := by
    simpa [a,q,f] using euler_correction_geometric_series χ hp hu (v := 0) (by simp)
  have weighted := (perron_summable_coefficients hX (by norm_num : (0:ℝ)<1)
    a (fun k => p^(k+1)) (fun k => pow_pos hp.pos _) hA).2.1
  have eqv (t : ℝ) := euler_correction_geometric_series χ hp hu (v := line 1 (2*Real.pi*t))
    (by norm_num [line])
  change (∫ t : ℝ, (∑' k : ℕ, a k*((p^(k+1):ℕ):ℂ)^(-line 1 (2*Real.pi*t))) *
    smoothedPerronKernel X (line 1 (2*Real.pi*t))) = _ at weighted
  simp_rw [show ∀ t : ℝ, (∑' k : ℕ, a k*((p^(k+1):ℕ):ℂ)^(-line 1 (2*Real.pi*t))) =
    f (line 1 (2*Real.pi*t)) from eqv] at weighted
  rw [← value,weighted]
  have aw : Summable (fun k => a k * (smoothedPerronWeight X (p^(k+1)) : ℂ)) := by
    apply Summable.of_norm
    apply hA.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    have w := smoothedPerronWeight_nonneg_le_one hX (p^(k+1))
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg w.1]
    exact mul_le_of_le_one_right (norm_nonneg _) w.2
  rw [← hA.of_norm.tsum_sub aw]
  simpa only [a,mul_sub,mul_one] using geometric_tail q lp hq hX p m hp.one_le cut

private theorem euler_tail {N : ℕ} [NeZero N] (χ : Character N) {u : ℂ}
    (hu : 1/2 ≤ u.re) {X : ℝ} (hX : 1<X) (m : ℕ)
    (cut : ((N^m:ℕ):ℝ) ≤ Real.sqrt X) :
    ‖eulerCorrection χ u - ∫ t : ℝ, eulerCorrection χ (u+line 1 (2*Real.pi*t)) *
      smoothedPerronKernel X (line 1 (2*Real.pi*t))‖ ≤ (4/5:ℝ)^m*(4*Real.log N) := by
  classical
  let f (p : ℕ) (v : ℂ) := if ¬p ∣ χ.conductor then
    χ.primitiveCharacter p*(Real.log p : ℂ)/((p:ℂ)^(u+v)-χ.primitiveCharacter p) else 0
  let K (t : ℝ) := smoothedPerronKernel X (line 1 (2*Real.pi*t))
  have integr (p : ℕ) (hp : p ∈ N.primeFactors) :
      Integrable (fun t : ℝ => f p (line 1 (2*Real.pi*t)) * K t) := by
    by_cases h : p ∣ χ.conductor
    · simp [f,h]
    · simpa [f,h,K] using (euler_correction_term_perron χ.primitiveCharacter
        (Nat.prime_of_mem_primeFactors hp) hu hX (by norm_num : (0:ℝ)<1)).1
  have eqv (v : ℂ) : eulerCorrection χ (u+v) = ∑ p ∈ N.primeFactors, f p v := rfl
  rw [show eulerCorrection χ u = ∑ p ∈ N.primeFactors, f p 0 by simpa using eqv 0]
  simp_rw [eqv,Finset.sum_mul]
  rw [integral_finsetSum _ integr,← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ N.primeFactors, ((4/5:ℝ)^m*4)*Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have prime := Nat.prime_of_mem_primeFactors hp
      by_cases h : p ∣ χ.conductor
      · simp [f,h]
        positivity
      · have size := Nat.le_of_dvd (NeZero.pos N) (Nat.dvd_of_mem_primeFactors hp)
        have pc : ((p^m:ℕ):ℝ) ≤ Real.sqrt X :=
          (show ((p^m:ℕ):ℝ) ≤ ((N^m:ℕ):ℝ) by exact_mod_cast Nat.pow_le_pow_left size m).trans cut
        simpa [f,h,K,mul_assoc] using local_euler_tail χ.primitiveCharacter prime hu hX m pc
    _ = _ * (∑ p ∈ N.primeFactors, Real.log p) := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (sum_log_primeFactors_le_log _ (NeZero.pos _)) (by positivity)

private theorem gamma_tail {X : ℝ} (hX : 1<X) {u : ℂ} (hu : 1/2 ≤ u.re) :
    ‖∫ t : ℝ, smoothedPerronKernel X (line 1 (2*Real.pi*t)) *
      ((logDeriv Gamma ((u+line 1 (2*Real.pi*t)+1)/2)-logDeriv Gamma ((u+1)/2))/2)‖ ≤
      4 / (Real.sqrt X * Real.log (Real.sqrt X)) := by
  rw [(gamma_perron_integral_eq hX (by norm_num : (0:ℝ)<1) hu).2,norm_neg]
  have hx : 1<Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hX)
  have logp := Real.log_pos hx
  let B := 2/(Real.sqrt X * Real.log (Real.sqrt X))
  have bp : 0≤B := by dsimp [B]; positivity
  have bound (k : ℕ) : ‖smoothedPerronKernel X (-(u+1+2*(k:ℂ)))‖ ≤ B*(1/((k:ℝ)+1)^2) := by
    let a := u+1+2*(k:ℂ)
    have ha : (k:ℝ)+1 ≤ a.re := by simp [a]; linarith [Nat.cast_nonneg (α:=ℝ) k]
    have hn := ha.trans (Complex.re_le_norm a)
    have hn1 : 1 ≤ a.re := by linarith [Nat.cast_nonneg (α:=ℝ) k]
    have sx : Real.sqrt X ≤ X := Real.sqrt_le_self_iff.mpr (Or.inr hX.le)
    have major (y : ℝ) (hy : Real.sqrt X ≤ y) : y^((-a).re) ≤ (Real.sqrt X)⁻¹ := by
      apply (Real.rpow_le_rpow_of_exponent_le (hx.le.trans hy)
        (show (-a).re ≤ (-1:ℝ) by simp; linarith)).trans
      rw [Real.rpow_neg_one]
      exact inv_anti₀ (by positivity) hy
    have num : ‖(X:ℂ)^(-a)-(Real.sqrt X:ℂ)^(-a)‖ ≤ (Real.sqrt X)⁻¹+(Real.sqrt X)⁻¹ :=
      (norm_sub_le ((X:ℂ)^(-a)) ((Real.sqrt X:ℂ)^(-a))).trans
      (add_le_add (by rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0<X)]; exact major X sx)
        (by rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0<Real.sqrt X)]; exact major _ le_rfl))
    change ‖smoothedPerronKernel X (-a)‖ ≤ _
    rw [smoothedPerronKernel,norm_div,norm_mul,norm_pow,norm_neg,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos logp]
    have den := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn 2) logp.le
    apply (div_le_div₀ (by positivity : 0 ≤ (Real.sqrt X)⁻¹+(Real.sqrt X)⁻¹) num
      (by positivity : 0 < ((k:ℝ)+1)^2*Real.log (Real.sqrt X)) den).trans_eq
    dsimp [B]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hs : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^2) 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by decide : 1<2))
  have ts := (hs.mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _) bound
  have h2 : (∑' n : ℕ, 1/((n:ℝ)+1)^2) ≤ 2 := by
    apply le_of_tendsto hs.hasSum.tendsto_sum_nat
    exact Eventually.of_forall (fun n => (sum_one_div_nat_add_one_sq_le n).trans
      (by linarith [show 0≤2/((n:ℝ)+1) by positivity]))
  apply (norm_tsum_le_tsum_norm ts).trans
  apply (ts.tsum_le_tsum bound (hs.mul_left B)).trans
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left h2 bp).trans_eq (by dsimp [B]; ring)

/-- Exact Perron decomposition with decaying errors from both the trivial
zeros and the imprimitive Euler factors. The contour identity follows the
decomposition in `SpectralPerronTruncation`. -/
theorem approximation_error {N : ℕ} [NeZero N] (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) {X σ : ℝ}
    (hX : 1 < X) (hσ : 0 < σ) (t : ℝ) (m : ℕ)
    (cut : ((N^m:ℕ):ℝ) ≤ Real.sqrt X) :
    ‖-logDerivative χ (line σ t)-smoothedDirichletPolynomial χ X (1/2+line σ t)‖ ≤
      perronZeroCoefficient X σ * zeroPoisson χ σ t +
      4 / (Real.sqrt X * Real.log (Real.sqrt X)) + (4/5:ℝ)^m*(4*Real.log N) := by
  let s := line σ t
  let v : ℝ → ℂ := fun τ => line 1 (2*Real.pi*τ)
  let K : ℝ → ℂ := fun τ => smoothedPerronKernel X (v τ)
  let Z : ℝ → ℂ := fun τ => zeroDifference χ.primitiveCharacter (1/2+s+v τ) (1/2+s)
  let G : ℝ → ℂ := fun τ =>
    (logDeriv Gamma ((1/2+s+v τ+1)/2)-logDeriv Gamma ((1/2+s+1)/2))/2
  let E : ℝ → ℂ := fun τ => eulerCorrection χ (1/2+s+v τ)
  have hu : 1/2 ≤ (1/2+s).re := by simp [s,line]; exact hσ.le
  have hχn := odd_character_ne_one χ (Finset.mem_filter.mp hχ).2
  have hKi : Integrable K := (smoothedPerronKernel_integral hX (by norm_num : (0:ℝ)<1)).1
  have hKv : (∫ τ : ℝ, K τ) = 1 := (smoothedPerronKernel_integral hX (by norm_num : (0:ℝ)<1)).2
  have hZi : Integrable (fun τ => K τ * Z τ) :=
    (perron_zeroDifference_integral hGRH χ hχn hX (by norm_num) hσ t).1
  have hZv : (∫ τ : ℝ, K τ * Z τ) = ∑' p : ZeroIndex χ.primitiveCharacter,
      smoothedPerronKernel X (p.val.1-(1/2+s)) :=
    (perron_zeroDifference_integral hGRH χ hχn hX (by norm_num) hσ t).2
  have hEi : Integrable (fun τ => E τ * K τ) :=
    (eulerCorrection_perron_integral χ hu hX (by norm_num : (0:ℝ)<1)).1
  have hEi0 := hKi.const_mul (eulerCorrection χ (1/2+s))
  have hgi0 := hKi.const_mul (-logDerivative χ s)
  have he (τ : ℝ) : -logDerivative χ (s+v τ) * K τ =
      (-logDerivative χ s)*K τ - K τ*Z τ + K τ*G τ - E τ*K τ +
        eulerCorrection χ (1/2+s)*K τ := by
    have hh := logDerivative_difference_zero_expansion hGRH χ hχ s (v τ)
      (by simpa [s,line] using hσ) (by simp [s,v,line]; linarith)
    dsimp [Z,G,E]
    linear_combination -K τ*hh
  have hp := smoothedPolynomial_perron_initial χ hX (by norm_num : (0:ℝ)<1)
    (1/2+s) (by simp [s,line]; linarith)
  have hp' : (∫ τ : ℝ, -logDerivative χ (s+v τ)*K τ) =
      smoothedDirichletPolynomial χ X (1/2+s) := by
    convert hp using 1
    congr 1
    funext τ
    congr 2
    dsimp [v]
    ring_nf
  have hGi := (gamma_perron_integral_eq hX (by norm_num : (0:ℝ)<1) hu).1
  have hGi' : Integrable (fun τ => K τ * G τ) := hGi
  have h₁ : Integrable (fun τ => (-logDerivative χ s)*K τ-K τ*Z τ) := hgi0.sub hZi
  have h₂ : Integrable (fun τ => (-logDerivative χ s)*K τ-K τ*Z τ+K τ*G τ) := h₁.add hGi'
  have h₃ : Integrable (fun τ => (-logDerivative χ s)*K τ-K τ*Z τ+K τ*G τ-E τ*K τ) := h₂.sub hEi
  simp_rw [he] at hp'
  rw [integral_add h₃ hEi0, integral_sub h₂ hEi,
    integral_add h₁ hGi', integral_sub hgi0 hZi,
    integral_const_mul, integral_const_mul, hKv, mul_one, mul_one, hZv] at hp'
  have herror : -logDerivative χ s-smoothedDirichletPolynomial χ X (1/2+s) =
      ((∑' p : ZeroIndex χ.primitiveCharacter, smoothedPerronKernel X (p.val.1-(1/2+s))) -
        ∫ τ : ℝ, K τ*G τ) +
      ((∫ τ : ℝ, E τ*K τ)-eulerCorrection χ (1/2+s)) := by
    linear_combination hp'
  change ‖-logDerivative χ s-smoothedDirichletPolynomial χ X (1/2+s)‖ ≤ _
  rw [herror]
  apply (norm_add_le _ _).trans
  have hZb := (smoothedPerron_nontrivial_zero_sum_bound hGRH χ hχn hX hσ (t := t)).2
  have hEb := euler_tail χ hu hX m cut
  rw [norm_sub_rev] at hEb
  exact add_le_add ((norm_sub_le _ _).trans (add_le_add hZb (gamma_tail hX hu))) hEb

/-- Uniform control of the zero term at a shrinking horizontal shift. -/
private theorem poisson_scale {N : ℕ} [NeZero N] (χ : Character N) (hc : χ ≠ 1)
    {σ : ℝ} (hp : 0<σ) (hu : σ≤1) (t : ℝ) :
    σ * zeroPoisson χ σ t ≤ (3/2) * zeroPoisson χ (3/2) t := by
  have summ := primitive_zero_poisson_summable χ.primitiveCharacter
    (primitiveCharacter_ne_one_of_ne_one χ hc) χ.primitiveCharacter_isPrimitive
  unfold zeroPoisson
  rw [← tsum_mul_left,← tsum_mul_left]
  apply Summable.tsum_le_tsum _ ((summ σ t hp).mul_left _) ((summ (3/2) t (by norm_num)).mul_left _)
  intro p
  let d := t-p.val.1.im
  change σ*(σ/(σ^2+d^2)) ≤ (3/2:ℝ)*((3/2)/((3/2)^2+d^2))
  rw [← mul_div_assoc,← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp.le (show σ≤3/2 by linarith) 2) (sq_nonneg d)
  nlinarith only [h]

/-- A uniform bound for each odd character. The constant is absolute. -/
theorem uniform_error : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), GRH N →
    ∀ χ ∈ oddCharacters N, ∀ (X σ t : ℝ) (m : ℕ), 1<X → 0<σ → σ≤1 →
    ((N^m:ℕ):ℝ) ≤ Real.sqrt X →
    ‖-logDerivative χ (line σ t)-smoothedDirichletPolynomial χ X (1/2+line σ t)‖ ≤
      perronZeroCoefficient X σ * (C*Real.log ((N:ℝ)*(|t|+2))/σ) +
      4/(Real.sqrt X*Real.log (Real.sqrt X))+(4/5:ℝ)^m*(4*Real.log N) := by
  obtain ⟨D,hD,anchor⟩ := zeroPoisson_anchor_bound
  refine ⟨(3/2)*D,by positivity,?_⟩
  intro N inst g χ hc X σ t m hX hp hu cut
  have hn := odd_character_ne_one χ (Finset.mem_filter.mp hc).2
  have scale := (poisson_scale χ hn hp hu t).trans
    (mul_le_mul_of_nonneg_left (anchor N inst χ hn t) (by norm_num))
  have q : zeroPoisson χ σ t ≤ ((3/2)*D)*Real.log ((N:ℝ)*(|t|+2))/σ := by
    apply (le_div_iff₀ hp).mpr
    linarith only [scale]
  exact (approximation_error g χ hc hX hp t m cut).trans
    (add_le_add_left (add_le_add_left (mul_le_mul_of_nonneg_left q
      (perronZeroCoefficient_nonneg hX hp)) _) _)

/-- At conductor power length the error falls geometrically in the exponent,
uniformly on the entire moving strip and at every height. -/
theorem conductor_power_error : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    1 ≤ Real.log N → GRH N → ∀ χ ∈ oddCharacters N, ∀ (σ t : ℝ) (m : ℕ),
    1≤m → (Real.log N)⁻¹ ≤ σ → σ≤1 →
    ‖-logDerivative χ (line σ t) -
      smoothedDirichletPolynomial χ (((N:ℝ)^m)^2) (1/2+line σ t)‖ ≤
      (4/5:ℝ)^m * (2*C*Real.log N*Real.log ((N:ℝ)*(|t|+2)) + 4 + 4*Real.log N) := by
  obtain ⟨C,hC,U⟩ := uniform_error
  refine ⟨C,hC,?_⟩
  intro N inst hL g χ hc σ t m hm hσ σ1
  let y := (N:ℝ)^m
  let r := (4/5:ℝ)^m
  have hn : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have hNr : 1<(N:ℝ) := (Real.log_pos_iff hn.le).mp (by linarith)
  have hL0 := Real.log_pos hNr
  have m1 : (1:ℝ)≤m := by exact_mod_cast hm
  have y1 : 1<y := one_lt_pow₀ hNr (by omega)
  have hy : 0<y := lt_trans zero_lt_one y1
  have X1 : 1<y^2 := one_lt_pow₀ y1 (by decide)
  have root : Real.sqrt (y^2) = y := Real.sqrt_sq hy.le
  have logy : Real.log y = (m:ℝ)*Real.log N := Real.log_pow _ _
  have Ly : 1≤Real.log y := by rw [logy]; nlinarith only [mul_le_mul m1 hL (by norm_num) (Nat.cast_nonneg m)]
  have hp : 0<σ := lt_of_lt_of_le (inv_pos.mpr hL0) hσ
  have sl : 1≤σ*Real.log N := (inv_le_iff_one_le_mul₀ hL0).mp hσ
  have siglog : (m:ℝ) ≤ Real.log y * σ := by
    rw [logy]
    nlinarith only [mul_le_mul_of_nonneg_left sl (Nat.cast_nonneg m)]
  have decay : y^(-σ) ≤ r := by
    rw [Real.rpow_def_of_pos hy]
    apply (Real.exp_le_exp.mpr (show Real.log y*(-σ) ≤ (m:ℝ)*(-1) by linarith)).trans
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    rw [Real.exp_neg,inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith [Real.add_one_le_exp (1:ℝ)])
  have coeff : perronZeroCoefficient (y^2) σ ≤ 2*r := by
    rw [perronZeroCoefficient,root]
    have yy : y≤y^2 := by nlinarith [mul_nonneg hy.le (sub_nonneg.mpr y1.le)]
    have a := Real.rpow_le_rpow_of_nonpos hy yy (neg_nonpos.mpr hp.le)
    apply (div_le_iff₀ (mul_pos hp (by linarith : 0<Real.log y))).mpr
    have d1 : 1 ≤ σ*Real.log y := by linarith
    have rr : 0≤r := by dsimp [r]; positivity
    nlinarith only [decay,a,mul_le_mul_of_nonneg_left d1 (show 0≤2*r by positivity)]
  have invy : y⁻¹ ≤ r := by
    rw [show y⁻¹ = y^(-1:ℝ) by rw [Real.rpow_neg_one]]
    exact (Real.rpow_le_rpow_of_exponent_le y1.le (by linarith : (-1:ℝ)≤ -σ)).trans decay
  have gam : 4/(y*Real.log y) ≤ 4*r := by
    have yl := mul_le_mul_of_nonneg_left Ly hy.le
    calc
      _ ≤ 4/y := div_le_div_of_nonneg_left (by norm_num) hy (by linarith only [yl])
      _ ≤ _ := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left invy (by norm_num : (0:ℝ)≤4)
  have logpos : 0 ≤ Real.log ((N:ℝ)*(|t|+2)) := Real.log_nonneg (by nlinarith [abs_nonneg t])
  have q : C*Real.log ((N:ℝ)*(|t|+2))/σ ≤ C*Real.log ((N:ℝ)*(|t|+2))*Real.log N := by
    apply (div_le_iff₀ hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_left sl (mul_nonneg hC.le logpos)]
  have h := U N inst g χ hc (y^2) σ t m X1 hp σ1 (by rw [root]; simp [y])
  rw [root] at h
  apply h.trans
  have bnd := mul_le_mul coeff q (div_nonneg (mul_nonneg hC.le logpos) hp.le)
    (show 0≤2*r by dsimp [r]; positivity)
  dsimp only [r] at *
  linarith only [bnd,gam,show (4/5:ℝ)^m * (2*C*Real.log N*Real.log ((N:ℝ)*(|t|+2)) + 4 + 4*Real.log N) =
    2*(4/5:ℝ)^m*(C*Real.log ((N:ℝ)*(|t|+2))*Real.log N) + 4*(4/5:ℝ)^m +
    (4/5:ℝ)^m*(4*Real.log N) by ring]

/-- A single integer exponent suffices for every height and every
horizontal shift on the moving strip. -/
theorem logarithmic_accuracy : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    1≤Real.log N → GRH N → ∀ χ ∈ oddCharacters N, ∀ (σ t : ℝ) (m : ℕ),
    1≤m → 100*Real.log (Real.log N) ≤ m → (Real.log N)⁻¹ ≤ σ → σ≤1 →
    ‖-logDerivative χ (line σ t) -
      smoothedDirichletPolynomial χ (((N:ℝ)^m)^2) (1/2+line σ t)‖ ≤
      C*(1+Real.log (|t|+2))/(Real.log N)^18 := by
  obtain ⟨C,hC,U⟩ := conductor_power_error
  refine ⟨2*C+8,by positivity,?_⟩
  intro N inst hL g χ hc σ t m hm hml hσ hu
  let L := Real.log N
  let H := Real.log (|t|+2)
  have lp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hH : 0≤H := Real.log_nonneg (by linarith [abs_nonneg t])
  have h := U N inst hL g χ hc σ t m hm hσ hu
  have fact : Real.log ((N:ℝ)*(|t|+2)) = L+H := Real.log_mul (by exact_mod_cast NeZero.ne N) (by positivity)
  rw [fact] at h
  have r : (4/5:ℝ)^m ≤ (L^20)⁻¹ := by
    calc
      _ ≤ (Real.exp (-(1/5:ℝ)))^m := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (-(1/5:ℝ))]) m
      _ = Real.exp ((m:ℝ)*(-(1/5:ℝ))) := (Real.exp_nat_mul ..).symm
      _ ≤ Real.exp (-(20*Real.log L)) := Real.exp_le_exp.mpr (by dsimp [L]; linarith only [hml])
      _ = _ := by rw [Real.exp_neg,show (20:ℝ)*Real.log L = Real.log (L^20) by rw [Real.log_pow]; norm_num,
                        Real.exp_log (by positivity)]
  have L1 : 1≤L := hL
  have L2 : L≤L^2 := by nlinarith only [mul_nonneg lp.le (sub_nonneg.mpr L1)]
  have geom : 2*C*L*(L+H)+4+4*L ≤ ((2*C+8)*(1+H))*L^2 := by
    have diff : 0≤L^2*H-L*H := sub_nonneg.mpr (mul_le_mul_of_nonneg_right L2 hH)
    nlinarith only [mul_nonneg hC.le diff,L2,L1,mul_nonneg (sq_nonneg L) hH]
  apply h.trans
  change (4/5:ℝ)^m*(2*C*L*(L+H)+4+4*L) ≤ (2*C+8)*(1+H)/L^18
  exact (mul_le_mul r geom (by positivity) (by positivity)).trans_eq (by field_simp)

#print axioms logarithmic_accuracy

end GoldbachSpectral435.PerronApproximation
