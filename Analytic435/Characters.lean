module
public import ConditionalGoldbach.Proofs.FiniteMellinProjection
public import ConditionalGoldbach.Proofs.FiniteCharacterShift
public import ConditionalGoldbach.Proofs.MellinMoment

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Complex
open scoped Topology
namespace GoldbachSpectral435
open ConditionalGoldbach

private def coeff {q : ℕ} (χ : Character q) (i : ℕ) : ℂ :=
  (mangoldt (i+1):ℂ)*χ (i+1)/(i+1:ℕ)^(1/2:ℂ)

private theorem summable_scaled {q : ℕ} [NeZero q] (χ : Character q)
    (M : ℕ) (hM : 0 < M) (σ : ℝ) (hs : 1/2 < σ) :
    Summable (fun i => ‖coeff χ i‖ * Real.rpow ((i+1:ℕ)/(M:ℝ)) (-σ)) := by
  have su := (summable_logDerivative_terms χ (s := (σ:ℂ)) (by simpa using hs)).norm
  apply (((summable_nat_add_iff 1).2 su).mul_left ‖(M:ℂ)^(σ:ℂ)‖).congr
  intro i
  have id := congrArg norm (mellin_dirichlet_rescale (i+1) M (by omega) hM (σ:ℂ)
    ((mangoldt (i+1):ℂ)*χ (i+1)))
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),norm_mul] at id
  simpa only [coeff,neg_re,ofReal_re,Real.rpow_eq_pow,Nat.cast_add,Nat.cast_one] using id.symm

private theorem expanded {q : ℕ} [NeZero q] (χ : Character q)
    (M : ℕ) (hM : 0 < M) (f : ℝ → ℝ) (s : ℂ) (hs : 1/2 < s.re) :
    (∑' i, coeff χ i * mellin (fun u => (f u:ℂ)) s *
      (((i+1:ℕ)/(M:ℝ):ℝ):ℂ)^(-s)) =
        -((M:ℂ)^s*mellin (fun u => (f u:ℂ)) s*logDerivative χ s) := by
  rw [logDerivative_eq_neg_tsum χ hs,mul_neg,neg_neg,(summable_logDerivative_terms χ hs).tsum_eq_zero_add]
  simp only [mangoldt,ArithmeticFunction.map_zero,ofReal_zero,zero_mul,zero_div,zero_add]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  unfold coeff
  calc
    _ = mellin (fun u => (f u:ℂ)) s * (((mangoldt (i+1):ℂ)*χ (i+1)/(i+1:ℕ)^(1/2:ℂ)) *
        (((i+1:ℕ)/(M:ℝ):ℝ):ℂ)^(-s)) := by ring
    _ = _ := by
      rw [mellin_dirichlet_rescale (i+1) M (by omega) hM]
      push_cast
      ring

/-- Power saving on every nonprincipal character at an independent averaging
scale. The constant is uniform in the modulus, character and averaging scale. -/
theorem smooth_character_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) {a b : ℝ}
    (sf : Function.support f ⊆ Icc a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q], 4 ≤ q → GRH q →
      ∀ χ : Character q, χ ≠ 1 → ∀ M : ℕ, 0 < M →
      ‖∑' i : ℕ, ((mangoldt (i+1):ℂ)*χ (i+1)/(i+1:ℕ)^(1/2:ℂ)) *
        (f ((i+1:ℕ)/(M:ℝ)):ℂ)‖ ≤ C*(M:ℝ)^(1/4:ℝ)*q^2 := by
  obtain ⟨A,hA,growth⟩ := logDerivative_uniform_bound (1/4) 1 (by norm_num) (by norm_num)
  obtain ⟨B,hB,dec⟩ := compact_mellin_finite_decay 4 f hf a b sf (1/4) 1 (by norm_num) (by norm_num)
  let W : ℝ → ℝ := fun t => (1+|t|)⁻¹^2
  have wi : Integrable W := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
    convert h using 1
    ext t
    simp [W,Real.norm_eq_abs,Real.rpow_neg (by positivity : 0 ≤ 1+|t|)]
  have wp : 0 ≤ ∫ t, W t := integral_nonneg (fun t => sq_nonneg _)
  let K := 4*A*B
  have kp : 0 < K := by dsimp [K]; positivity
  let c := ‖((2*(Real.pi:ℂ))⁻¹)‖
  refine ⟨1+c*K*(∫ t,W t),by have := norm_nonneg ((2*(Real.pi:ℂ))⁻¹); dsimp [c]; positivity,?_⟩
  intro q inst hq grh χ hχ M hM
  let F : ℂ → ℂ := fun s => (M:ℂ)^s*mellin (fun u => (f u:ℂ)) s*logDerivative χ s
  have mp : (0:ℝ) < M := by exact_mod_cast hM
  have m1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have fd (s : ℂ) (hs : s.re ∈ Icc (1/4:ℝ) 1) : DifferentiableAt ℂ F s := by
    have pos : 0 < s.re := by linarith [hs.1]
    have hpow : Differentiable ℂ (fun s : ℂ => (M:ℂ)^s) :=
      differentiable_id.const_cpow (Or.inl (by exact_mod_cast hM.ne'))
    exact (hpow.differentiableAt.mul (compact_mellin_regular f hf.continuous a b sf s pos).2).mul
      (logDerivative_analyticAt_of_GRH grh χ hχ pos).differentiableAt
  have bound (x : ℝ) (hx : x ∈ Icc (1/4:ℝ) 1) (t : ℝ) :
      ‖F (line x t)‖ ≤ (M:ℝ)^x*q^2*K*W t := by
    have hg := (growth q inst hq grh χ hχ x hx t).trans
      (mul_le_mul_of_nonneg_left (log_square_polynomial_bound q hq t) hA.le)
    have hb := dec (line x t) (by simpa [line] using hx)
    have ht : (line x t).im = t := by simp [line]
    rw [ht] at hb
    unfold F
    rw [norm_mul,norm_mul,← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos mp]
    have xr : (line x t).re = x := by simp [line]
    rw [xr]
    calc
      _ ≤ ((M:ℝ)^x*(B*(1+|t|)⁻¹^4))*(A*(4*(q:ℝ)^2*(1+|t|)^2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg mp.le _)) hg (norm_nonneg _)
          (by positivity)
      _ = _ := by dsimp [K,W]; field_simp
  have full (x : ℝ) (hx : x ∈ Icc (1/4:ℝ) 1) (t : ℝ) :
      ‖F (line x t)‖ ≤ ((M:ℝ)*q^2*K)*W t := by
    have le : (M:ℝ)^x ≤ M := by simpa using Real.rpow_le_rpow_of_exponent_le m1 hx.2
    exact (bound x hx t).trans (by gcongr)
  have cont (x : ℝ) (hx : x ∈ Icc (1/4:ℝ) 1) : Continuous (fun t : ℝ => F (line x t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (fd (line x t) (by simpa [line] using hx)).continuousAt.comp (by unfold line; fun_prop)
  have int (x : ℝ) (hx : x ∈ Icc (1/4:ℝ) 1) : Integrable (fun t : ℝ => F (line x t)) :=
    integrable_of_uniform_vertical_decay _ _ _ (cont x hx) (full x hx)
  have lo : (1/4:ℝ) ∈ Icc (1/4:ℝ) 1 := by constructor <;> norm_num
  have hi : (1:ℝ) ∈ Icc (1/4:ℝ) 1 := by constructor <;> norm_num
  have sh := verticalMellin_eq_of_uniform_decay F (1/4) 1 _ (by norm_num) fd (int _ lo) (int _ hi) full
  have raw := finite_mellin_inversion_hasSum f (hf.of_le (by norm_num)) a b sf 1 (by norm_num)
    (fun i : ℕ => (i+1:ℕ)/(M:ℝ)) (coeff χ) (fun i => by positivity)
    (summable_scaled χ M hM 1 (by norm_num))
  have eqn : (∑' i : ℕ, coeff χ i*(f ((i+1:ℕ)/(M:ℝ)):ℂ)) = -verticalMellin (1/4) F := by
    rw [sh,raw.tsum_eq]
    unfold verticalMellin
    simp_rw [expanded χ M hM f _ (by simp [line]; norm_num : (1/2:ℝ) < (line 1 _).re)]
    rw [integral_neg,mul_neg]
  change ‖∑' i : ℕ, coeff χ i*(f ((i+1:ℕ)/(M:ℝ)):ℂ)‖ ≤ _
  rw [eqn,norm_neg]
  unfold verticalMellin
  rw [norm_mul]
  have iB := integral_mono (int _ lo).norm (wi.const_mul ((M:ℝ)^(1/4:ℝ)*q^2*K)) (bound _ lo)
  rw [integral_const_mul] at iB
  calc
    _ ≤ c*(((M:ℝ)^(1/4:ℝ)*q^2*K)*(∫ t,W t)) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans iB) (norm_nonneg _)
    _ ≤ _ := by have hp := Real.rpow_nonneg mp.le (1/4:ℝ); nlinarith [mul_nonneg hp (sq_nonneg (q:ℝ))]
/-- Exact shifted Mellin inversion on every nonprincipal character. -/
theorem nonprincipal_sampling {q : ℕ} [NeZero q] (hq : 4 ≤ q) (grh : GRH q)
    (χ : Character q) (nonpr : χ≠1) (M : ℕ) (hm : q ≤ M)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) {a b : ℝ} (support : Function.support f ⊆ Icc a b)
    (σ : ℝ) (hs : 0 < σ) (hu : σ ≤ 1) :
    let F := fun s : ℂ => (M:ℂ)^s*mellin (fun u => (f u:ℂ)) s*logDerivative χ s
    Integrable (fun t : ℝ => F (line σ t)) ∧ verticalMellin σ F =
      -(∑' i : ℕ, ((mangoldt (i+1):ℂ)*χ (i+1)/(i+1:ℕ)^(1/2:ℂ))*(f ((i+1:ℕ)/(M:ℝ)):ℂ)) := by
  intro F
  have mp : 0 < M := by omega
  obtain ⟨A,hA,B⟩ := logDerivative_uniform_bound σ 1 hs hu
  have grow (x : ℝ) (hx : x ∈ Icc σ 1) (t : ℝ) :
      ‖logDerivative χ (line x t)‖ ≤ A*Real.log (M*(|t|+2))^2 := by
    apply (B q inferInstance hq grh χ nonpr x hx t).trans
    apply mul_le_mul_of_nonneg_left _ hA.le
    have q1 : (1:ℝ) ≤ q := by exact_mod_cast (show 1≤q by omega)
    have tp : (1:ℝ) ≤ |t|+2 := by linarith [abs_nonneg t]
    have base : 1 ≤ (q:ℝ)*(|t|+2) := one_le_mul_of_one_le_of_one_le q1 tp
    apply pow_le_pow_left₀ (Real.log_nonneg base)
    apply Real.log_le_log (zero_lt_one.trans_le base)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by positivity)
  obtain ⟨C,_,bound⟩ := finite_mellin_character_uniform_bound M (by omega) f hf a b support σ A hs hu hA.le _ grow
  have hd (s : ℂ) (hx : s.re ∈ Icc σ 1) : DifferentiableAt ℂ F s := by
    have sp := hs.trans_le hx.1
    exact ((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast mp.ne' : (M:ℂ)≠0))).mul
      (compact_mellin_regular f hf.continuous a b support s sp).2).mul
        (logDerivative_analyticAt_of_GRH grh χ nonpr sp).differentiableAt
  have integr (x : ℝ) (hx : x ∈ Icc σ 1) : Integrable (fun t : ℝ => F (line x t)) := by
    apply integrable_of_uniform_vertical_decay _ _ C _ (bound x hx)
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hd _ (by simpa [line] using hx)).continuousAt.comp (by unfold line; fun_prop)
  have lo := integr σ ⟨le_rfl,hu⟩
  refine ⟨lo,?_⟩
  rw [verticalMellin_eq_of_uniform_decay F σ 1 C hu hd lo (integr 1 ⟨hu,le_rfl⟩) bound]
  have raw := finite_mellin_inversion_hasSum f (hf.of_le (by norm_num)) a b support 1 (by norm_num)
    (fun i : ℕ => (i+1:ℕ)/(M:ℝ)) (coeff χ) (fun i => by positivity) (summable_scaled χ M mp 1 (by norm_num))
  change verticalMellin 1 F = -(∑' i : ℕ, coeff χ i*(f ((i+1:ℕ)/(M:ℝ)):ℂ))
  rw [raw.tsum_eq]
  unfold verticalMellin
  simp_rw [expanded χ M mp f _ (by norm_num [line] : (1/2:ℝ) < (line 1 _).re)]
  rw [integral_neg,mul_neg,neg_neg]

/-- Exact inversion at the low Hardy contour. The physical scale M may be
any integer at least the modulus of the character. -/
theorem character_sampling {q : ℕ} [NeZero q] (hq : 4 ≤ q) (grh : GRH q)
    (χ : Character q) (hc : χ ∈ oddCharacters q) (M : ℕ) (hm : q ≤ M)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) {a b : ℝ} (support : Function.support f ⊆ Icc a b)
    (σ : ℝ) (hs : 0 < σ) (hu : σ ≤ 1) :
    let F := fun s : ℂ => (M:ℂ)^s*mellin (fun u => (f u:ℂ)) s*logDerivative χ s
    Integrable (fun t : ℝ => F (line σ t)) ∧ verticalMellin σ F =
      -(∑' i : ℕ, ((mangoldt (i+1):ℂ)*χ (i+1)/(i+1:ℕ)^(1/2:ℂ))*(f ((i+1:ℕ)/(M:ℝ)):ℂ)) := by
  exact nonprincipal_sampling hq grh χ (odd_character_ne_one χ (Finset.mem_filter.mp hc).2) M hm f hf support σ hs hu

def characterSample {q : ℕ} (χ : Character q) (M : ℕ) (f : ℝ → ℝ) : ℂ :=
  ∑' i : ℕ, ((mangoldt (i+1):ℂ)*χ (i+1)/(i+1:ℕ)^(1/2:ℂ))*(f ((i+1:ℕ)/(M:ℝ)):ℂ)

/-- Mixed double integral of the arithmetic character kernel. No relation
between the two weights is assumed. -/
theorem character_gram {q : ℕ} [NeZero q] (hq : 4 ≤ q) (grh : GRH q)
    (M : ℕ) (hm : q ≤ M) (f g : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g)
    {a b c d : ℝ} (sf : Function.support f ⊆ Icc a b) (sg : Function.support g ⊆ Icc c d)
    (σ : ℝ) (hs : 0 < σ) (hu : σ ≤ 1) :
    Integrable (fun p : ℝ × ℝ => (M:ℂ)^(line σ p.1+line σ p.2)*
      mellin (fun u => (f u:ℂ)) (line σ p.1)*mellin (fun u => (g u:ℂ)) (line σ p.2)*characterKernel q (line σ p.1) (line σ p.2)) ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z => (M:ℂ)^(s+z)*
      mellin (fun u => (f u:ℂ)) s*mellin (fun u => (g u:ℂ)) z*characterKernel q s z)) =
      (2/(q.totient:ℂ))*∑ χ ∈ oddCharacters q, characterSample χ M f * characterSample (star χ) M g := by
  let L := fun (v : ℝ → ℝ) (χ : Character q) (s : ℂ) => (M:ℂ)^s*mellin (fun u => (v u:ℂ)) s*logDerivative χ s
  have fct (s z : ℂ) : (M:ℂ)^(s+z)*mellin (fun u => (f u:ℂ)) s*mellin (fun u => (g u:ℂ)) z*
      characterKernel q s z = (2/(q.totient:ℂ))*∑ χ ∈ oddCharacters q, L f χ s * L g (star χ) z := by
    have hp : (M:ℂ) ≠ 0 := by exact_mod_cast (show M≠0 by omega)
    rw [cpow_add _ _ hp,characterKernel_eq_star_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    dsimp [L]; ring
  simp_rw [fct]
  have Hf := fun χ (hc : χ ∈ oddCharacters q) => character_sampling hq grh χ hc M hm f hf sf σ hs hu
  have Hg := fun χ (hc : χ ∈ oddCharacters q) => character_sampling hq grh (star χ) ((star_mem_oddCharacters χ).mpr hc) M hm g hg sg σ hs hu
  refine ⟨(integrable_finsetSum _ (fun χ hχ => (Hf χ hχ).1.mul_prod (Hg χ hχ).1)).const_mul _,?_⟩
  rw [double_verticalMellin_finset_prod _ σ _ _ _ (fun χ hχ => (Hf χ hχ).1) (fun χ hχ => (Hg χ hχ).1)]
  congr 1
  apply Finset.sum_congr rfl
  intro χ hc
  rw [(Hf χ hc).2,(Hg χ hc).2,neg_mul_neg]
  rfl
#print axioms character_gram
#print axioms smooth_character_bound
end GoldbachSpectral435
