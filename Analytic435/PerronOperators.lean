module
public import PerronHardy
public import ConditionalGoldbach.Proofs.SpectralDiagonalVector
public import ConditionalGoldbach.Proofs.SpectralQuantitative

/-! An explicit finite Gram operator made from prime powers and diagonal
Hardy vectors. Its approximation is in operator norm. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex MeasureTheory Filter Set InnerProductSpace
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PerronApproximation

def polyVector {N : ℕ} (χ : Character N) (m : ℕ) : HardySpace (alpha N) beta :=
  ∑ n ∈ Finset.range (⌊cutoff N m⌋₊+1),
    (-(mangoldt n:ℂ) * χ n * (n:ℂ)^(-(1/2:ℂ)) * smoothedPerronWeight (cutoff N m) n) •
      diagonalHardyVector n

theorem polyVector_spec {N : ℕ} (χ : Character N) (m : ℕ) (ha : alpha N < beta)
    (ap : 0≤alpha N) (s : ℂ) (hs : s∈strip (alpha N) beta) :
    fourierLaplace (polyVector χ m) s = polynomialFunction χ m s := by
  rw [polyVector,← hardyEvaluationFunctional_apply hs,map_sum]
  unfold polynomialFunction smoothedDirichletPolynomial
  rw [← Finset.sum_neg_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  rw [hardyEvaluationFunctional_apply hs,fourierLaplace_smul _ _ hs]
  by_cases hz : n=0
  · subst n
    simp [mangoldt]
  · rw [(diagonalHardyVector_spec ha ap n (by omega)).1 s hs,diagonalVector]
    have nz : (n:ℂ)≠0 := by exact_mod_cast hz
    rw [show -(1/2+s) = -(1/2:ℂ) + -s by ring,Complex.cpow_add _ _ nz]
    ring

def primeGram (N m : ℕ) [NeZero N] :
    HardySpace (alpha N) beta →L[ℂ] HardySpace (alpha N) beta :=
  ∑ χ : {χ : Character N // χ ∈ oddCharacters N},
    let v := (Real.sqrt (2/(N.totient:ℝ)) : ℂ) • polyVector χ.val m
    rankOne ℂ v v

private theorem rank_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v w : H) {b d : ℝ} (b0 : 0≤b) (d0 : 0≤d) (dist : ‖v-w‖≤b*d) :
    ‖rankOne ℂ v v - rankOne ℂ w w‖ ≤ d*(b^2+‖v‖^2)+b^2*d^2 := by
  have decomp : rankOne ℂ v v-rankOne ℂ w w =
      rankOne ℂ (v-w) v + rankOne ℂ w (v-w) := by
    rw [map_sub,sub_apply,map_sub]
    abel
  rw [decomp]
  apply (norm_add_le _ _).trans
  rw [norm_rankOne,norm_rankOne]
  have vw : ‖w‖ ≤ ‖v‖+b*d := by
    calc
      _ ≤ ‖v‖+‖w-v‖ := by simpa only [add_sub_cancel] using norm_add_le v (w-v)
      _ ≤ _ := by rw [norm_sub_rev]; linarith only [dist]
  have A := mul_le_mul_of_nonneg_right dist (norm_nonneg v)
  have B := mul_le_mul vw dist (norm_nonneg (v-w)) (by positivity)
  nlinarith only [A,B,mul_nonneg d0 (sq_nonneg (b-‖v‖))]

/-- An actual Gram representation together with the sum of its squared
column norms. The trace identity uses the finite-rank Gram representation. -/
private theorem character_columns (N : ℕ) [NeZero N] (hlarge : Real.exp 10<(N:ℝ))
    (hGRH : GRH N) (ha : alpha N<beta) :
    ∃ v : {χ : Character N // χ ∈ oddCharacters N} → HardySpace (alpha N) beta,
      (∀ χ s, s∈strip (alpha N) beta → fourierLaplace (v χ) s =
        (Real.sqrt (2/(N.totient:ℝ)):ℂ)*characterHardyFunction χ.val s) ∧
      arithmeticOperator ha N = ∑ χ, rankOne ℂ (v χ) (v χ) ∧
      ∑ χ, ‖v χ‖^2 = positiveTrace (arithmeticOperator ha N) := by
  classical
  let ι := {χ : Character N // χ ∈ oddCharacters N}
  have hgex (χ : ι) := characterHardyFunction_representation N hlarge hGRH ha χ.val χ.property
  choose g hg hgl hgr using hgex
  let c : ℝ := 2 / N.totient
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let v : ι → HardySpace (alpha N) beta := fun χ => (Real.sqrt c : ℂ) • g χ
  let f : ι → ℂ → ℂ := fun χ s => (Real.sqrt c : ℂ) * characterHardyFunction χ.val s
  have hvf (χ : ι) (s : ℂ) (hs : s ∈ strip (alpha N) beta) : fourierLaplace (v χ) s = f χ s := by
    dsimp only [v]
    rw [fourierLaplace_smul _ _ hs, hg χ s hs]
  have hvl (χ : ι) : (boundaryTraces ha (v χ)).1 =ᵐ[volume] fun t => f χ (line (alpha N) t) := by
    dsimp only [v]
    rw [boundaryTraces_smul]
    filter_upwards [Lp.coeFn_smul (Real.sqrt c : ℂ) (boundaryTraces ha (g χ)).1, hgl χ] with t ht hg
    change ((Real.sqrt c : ℂ) • (boundaryTraces ha (g χ)).1) t = _
    rw [ht, Pi.smul_apply, smul_eq_mul, hg]
  have hvr (χ : ι) : (boundaryTraces ha (v χ)).2 =ᵐ[volume] fun t => f χ (line beta t) := by
    dsimp only [v]
    rw [boundaryTraces_smul]
    filter_upwards [Lp.coeFn_smul (Real.sqrt c : ℂ) (boundaryTraces ha (g χ)).2, hgr χ] with t ht hg
    change ((Real.sqrt c : ℂ) • (boundaryTraces ha (g χ)).2) t = _
    rw [ht, Pi.smul_apply, smul_eq_mul, hg]
  have hc_cast : (c : ℂ) = (2 : ℂ) / N.totient := by dsimp [c]; push_cast; rfl
  have hc_sq : (Real.sqrt c : ℂ) ^ 2 = (c : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hc]
  have hgram (s z : ℂ) : weightedAnalyticKernel (characterKernel N) s z = ∑ χ : ι, f χ s * conj (f χ z) := by
    dsimp only [f, weightedAnalyticKernel, characterHardyFunction]
    rw [Finset.sum_coe_sort (oddCharacters N) (fun χ : Character N =>
      (Real.sqrt c : ℂ) * (logDerivative χ s / (1 + s)) *
        conj ((Real.sqrt c : ℂ) * (logDerivative χ z / (1 + z))))]
    simp only [characterKernel, Complex.conj_conj]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [map_mul, Complex.conj_ofReal, map_div₀, map_add, map_one]
    calc
      (2 / (N.totient : ℂ) * (logDerivative χ s * conj (logDerivative χ z))) /
          ((1 + s) * (1 + conj z)) =
        (Real.sqrt c : ℂ) ^ 2 * (logDerivative χ s / (1 + s)) *
          (conj (logDerivative χ z) / (1 + conj z)) := by
          rw [hc_sq, hc_cast]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
      _ = _ := by ring
  have hrep := hardyFiniteGram_represents ha N v f (weightedAnalyticKernel (characterKernel N)) hvf hvl hvr hgram
  have he : arithmeticOperator ha N = ∑ χ : ι, rankOne ℂ (v χ) (v χ) :=
    kernelOperator_eq_of_represents ha N hrep
  have ht := rankOne_tsum_positiveTraceClass v (hasSum_fintype (fun χ : ι => ‖v χ‖ ^ 2)).summable
    (Classical.choice (hardySpace_exists_nat_hilbertBasis (alpha N) beta))
  rw [tsum_fintype, tsum_fintype] at ht
  exact ⟨v,hvf,he,by rw [he,ht.2]⟩

/-- The finite prime-power Gram approximation is uniform in operator norm
on the original Hilbert space, at every sufficiently large even level. -/
theorem operator_error : ∃ K : ℝ, 0<K ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
    Real.exp 10 < (N:ℝ) → GRH N → ∀ (ha : alpha N<beta) (m : ℕ),
    1≤m → 100*Real.log (Real.log N) ≤ m →
    ‖arithmeticOperator ha N - primeGram N m‖ ≤ K/(Real.log N)^16 := by
  classical
  obtain ⟨D,hD,H⟩ := hardy_error
  obtain ⟨A,hA,M⟩ := lemma_6_4
  refine ⟨D*(1+4*A)+D^2,by positivity,?_⟩
  intro N inst even big g ha m hm hcut
  obtain ⟨four,hlog,_⟩ := large_parameters big
  have one : 1≤Real.log N := by
    have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
    linarith [(Real.lt_log_iff_exp_lt np).mpr big]
  let ι := {χ : Character N // χ ∈ oddCharacters N}
  let c := 2/(N.totient:ℝ)
  let b := Real.sqrt c
  let L := Real.log N
  let d := D/L^18
  have c0 : 0≤c := by dsimp [c]; positivity
  have bs : b^2=c := Real.sq_sqrt c0
  have b0 : 0≤b := Real.sqrt_nonneg _
  have d0 : 0≤d := (div_pos hD (pow_pos hlog _)).le
  have lp : 0<L := hlog
  obtain ⟨v,vf,op,tr⟩ := character_columns N big g ha
  let w : ι → HardySpace (alpha N) beta := fun χ => (b:ℂ) • polyVector χ.val m
  have error (χ : ι) : ‖v χ - w χ‖ ≤ b*d := by
    obtain ⟨e,ef,bd⟩ := H N inst big g χ.val χ.property m hm hcut
    have eqv : v χ-w χ = (b:ℂ) • e := by
      apply fourierLaplace_injective_strip ha
      intro s hs
      rw [← hardyEvaluationFunctional_apply hs,map_sub,hardyEvaluationFunctional_apply hs,
        hardyEvaluationFunctional_apply hs,vf χ s hs]
      dsimp only [w]
      rw [fourierLaplace_smul _ _ hs,fourierLaplace_smul _ _ hs,ef s hs,
        polyVector_spec _ _ ha (large_alpha_pos big).le s hs]
      change (b:ℂ)*_-(b:ℂ)*_ = (b:ℂ)*(_-_)
      ring
    rw [eqv,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg b0]
    exact mul_le_mul_of_nonneg_left bd b0
  have mass : ∑ _χ : ι, b^2 = 1 := by
    rw [bs,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    simpa [ι,c,mul_comm] using odd_character_average_mass N even four
  have bound := (arithmeticOperator_trace_bound_of_average N big g ha A hA.le
    (fun x xp xb => (M N inst even big g x xp xb).2)).2.2
  have trace : ∑ χ, ‖v χ‖^2 ≤ 4*A*L^2 := by
    rw [tr]
    simpa [L,alpha,one_div] using bound.trans_eq (by simp [alpha,one_div]; ring)
  have sumsq : ∑ _χ : ι, b^2*d^2 = d^2 := by rw [← Finset.sum_mul,mass,one_mul]
  have gram : primeGram N m = ∑ χ : ι, rankOne ℂ (w χ) (w χ) := rfl
  rw [op,gram,← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ χ : ι, (d*(b^2+‖v χ‖^2)+b^2*d^2) :=
      Finset.sum_le_sum (fun χ _ => rank_error _ _ b0 d0 (error χ))
    _ ≤ d*(1+4*A*L^2)+d^2 := by
      rw [Finset.sum_add_distrib,sumsq,← Finset.mul_sum,Finset.sum_add_distrib,mass]
      gcongr
    _ ≤ _ := by
      have pow16 := pow_le_pow_right₀ one (by decide : 16≤18)
      have pow36 := pow_le_pow_right₀ one (by decide : 16≤36)
      have small : d ≤ D/L^16 := div_le_div_of_nonneg_left hD.le (by positivity) pow16
      have smallsq : d^2 ≤ D^2/L^16 := by
        dsimp [d]
        rw [div_pow,← pow_mul]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) pow36
      have eqv : d*(4*A*L^2) = D*(4*A)/L^16 := by dsimp [d]; field_simp
      change d*(1+4*A*L^2)+d^2 ≤ (D*(1+4*A)+D^2)/L^16
      rw [mul_add,mul_one,eqv,add_div,mul_add,mul_one,add_div]
      linarith only [small,smallsq]

#print axioms operator_error

end GoldbachSpectral435.PerronApproximation
