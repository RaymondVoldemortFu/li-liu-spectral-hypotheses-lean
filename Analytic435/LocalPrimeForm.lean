module
public import PhysicalSupport
public import Mathlib.Analysis.Normed.Group.Tannery

/-! Exact finite prime correlations on finite intervals in the Fourier
realization of the original strip. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex InnerProductSpace
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.LocalPrimeForm
open GoldbachSpectral435.PerronApproximation

private lemma cutoff_large {N : ℕ} (hN : 1<(N:ℝ)) (Y : ℕ) :
    ∀ᶠ m : ℕ in atTop, (Y:ℝ) ≤ Real.sqrt (cutoff N m) := by
  have growth := (tendsto_pow_atTop_atTop_of_one_lt hN).eventually_ge_atTop (Y:ℝ)
  filter_upwards [growth] with m h
  simpa only [cutoff,Real.sqrt_sq (pow_nonneg (Nat.cast_nonneg N) m)] using h

private lemma weight_one {N : ℕ} (hN : 1<(N:ℝ)) (n : ℕ) :
    ∀ᶠ m : ℕ in atTop, smoothedPerronWeight (cutoff N m) n=1 :=
  (cutoff_large hN n).mono (fun _ h => ite_eq_left h)

/-- Norm convergence to the actual diagonal at each fixed modulus. -/
theorem diagonal_limit (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) (ha : alpha N<beta) :
    Tendsto (primeDiagonal N) atTop (𝓝 (diagonalOperator ha N)) := by
  let R (j : ℕ) := rankOne ℂ (diagonalRankVector (a:=alpha N) N j) (diagonalRankVector (a:=alpha N) N j)
  let P (m j : ℕ) := ((smoothedPerronWeight (cutoff N m) (j+1):ℂ)^2) • R j
  have ns : 1<(N:ℝ) := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<10)).trans big
  have ap := large_alpha_pos big
  have sum : Summable (fun j => ‖R j‖) := by
    simpa only [R,norm_rankOne,pow_two] using diagonalRankVector_summable ha ap N
  have term (j : ℕ) : Tendsto (fun m => P m j) atTop (𝓝 (R j)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [weight_one ns (j+1)] with m eq
    simp [P,eq]
  have grow (m : ℕ) (hm : 1≤m) : 1<cutoff N m := one_lt_pow₀ (one_lt_pow₀ ns (by omega)) (by decide)
  have major : ∀ᶠ m : ℕ in atTop, ∀ j, ‖P m j‖≤‖R j‖ := by
    filter_upwards [eventually_ge_atTop 1] with m hm j
    obtain ⟨np,one⟩ := smoothedPerronWeight_nonneg_le_one (grow m hm) (j+1)
    simp only [P,norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg np]
    exact mul_le_of_le_one_left (norm_nonneg _) (by nlinarith only [one,mul_nonneg np (sub_nonneg.mpr one)])
  have limit := tendsto_tsum_of_dominated_convergence sum term major
  rw [diagonalOperator_eq_rankSeries ha ap N]
  change Tendsto _ _ (𝓝 (∑' j, R j))
  apply limit.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  change (∑' j, P m j)=∑ j ∈ Finset.range ⌊cutoff N m⌋₊, P m j
  apply tsum_eq_sum
  intro j hj
  have lt : cutoff N m<((j+1:ℕ):ℝ) := (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast
    (show ⌊cutoff N m⌋₊+1≤j+1 by rw [Finset.mem_range] at hj; omega))
  have rt := Real.sqrt_le_self_iff.mpr (Or.inr (grow m hm).le)
  have ww : smoothedPerronWeight (cutoff N m) (j+1)=0 := by
    simp only [smoothedPerronWeight,ite_eq_right (not_le.mpr (rt.trans_lt lt)),ite_eq_right (not_le.mpr lt)]
  simp [P,ww]

private lemma column_limit {N : ℕ} [NeZero N] (big : Real.exp 10<(N:ℝ)) (g : GRH N)
    (ha : alpha N<beta) (χ : {χ : Character N // χ∈oddCharacters N})
    (v : HardySpace (alpha N) beta) (b : ℝ) (bp : 0≤b)
    (rep : ∀ s ∈ strip (alpha N) beta, fourierLaplace v s=(b:ℂ)*characterHardyFunction χ.val s) :
    Tendsto (fun m : ℕ => (b:ℂ) • polyVector χ.val m) atTop (𝓝 v) := by
  obtain ⟨D,dp,E⟩ := hardy_geometric
  let z (m : ℕ) := (b:ℂ) • polyVector χ.val m
  have ratio : Tendsto (fun m : ℕ => (4/5:ℝ)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa only [mul_zero] using ratio.const_mul (b*(D*Real.log N^2)))
  filter_upwards [eventually_ge_atTop 1] with m hm
  obtain ⟨e,ef,eb⟩ := E N inferInstance big g χ.val χ.property m hm
  have eq : v-z m=(b:ℂ) • e := by
    apply fourierLaplace_injective_strip ha
    intro s hs
    rw [← hardyEvaluationFunctional_apply hs,map_sub,hardyEvaluationFunctional_apply hs,
      hardyEvaluationFunctional_apply hs,rep s hs]
    dsimp only [z]
    rw [fourierLaplace_smul _ _ hs,fourierLaplace_smul _ _ hs,ef s hs,
      polyVector_spec _ _ ha (large_alpha_pos big).le s hs]
    change (b:ℂ)*_-(b:ℂ)*_=(b:ℂ)*(_-_)
    ring
  rw [norm_sub_rev,eq,norm_smul,Complex.norm_real,Real.norm_of_nonneg bp]
  exact (mul_le_mul_of_nonneg_left eb bp).trans_eq (by ring)

private lemma rank_cont {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Continuous (fun p : H × H => rankOne ℂ p.1 p.2) :=
  ((ContinuousLinearMap.toSpanSingletonLIE ℂ H).continuous.comp continuous_fst).clm_comp
    ((innerSL ℂ).continuous.comp continuous_snd)

private lemma rank_self_cont {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Continuous (fun x : H => rankOne ℂ x x) := by
  have diagonal : Continuous (fun x : H => (x,x)) := continuous_id.prodMk continuous_id
  have result := (rank_cont (H:=H)).comp diagonal
  exact result

/-- At each fixed eligible modulus the full operator-norm limit of the
finite odd-character Gram operators is the original arithmetic operator. -/
theorem gram_limit (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) (g : GRH N) (ha : alpha N<beta) :
    Tendsto (fun m : ℕ => primeGram N m) atTop (𝓝 (arithmeticOperator ha N)) := by
  classical
  have ⟨v,rep,op,_⟩ := character_columns N big g ha
  let ι := {χ : Character N // χ∈oddCharacters N}
  let H := HardySpace (alpha N) beta
  let b := Real.sqrt (2/(N.totient:ℝ))
  let z (χ : ι) (m : ℕ) : H := (b:ℂ) • polyVector χ.val m
  let Q (x : H) : H →L[ℂ] H := rankOne ℂ x x
  have cont : Continuous Q := rank_self_cont (H:=H)
  have term (χ : ι) : Tendsto (fun m : ℕ => Q (z χ m)) atTop (𝓝 (Q (v χ))) :=
    cont.continuousAt.tendsto.comp (column_limit big g ha χ (v χ) b (Real.sqrt_nonneg _) (rep χ))
  have total := tendsto_finsetSum (f:=fun χ m => Q (z χ m)) (a:=fun χ => Q (v χ))
    (Finset.univ : Finset ι) (fun χ _ => term χ)
  have target : (∑ χ : ι, Q (v χ))=arithmeticOperator ha N := op.symm
  rw [target] at total
  apply total.congr'
  exact Eventually.of_forall (fun _ => rfl)

def coefficient {N : ℕ} (f : HardySpace (alpha N) beta) (n : ℕ) : ℂ :=
  -(mangoldt n:ℂ)*(n:ℂ)^(-(1/2:ℂ))*inner ℂ f (diagonalHardyVector n)

def localPairs (N Y : ℕ) (f : HardySpace (alpha N) beta) : ℂ :=
  ∑ n ∈ Finset.range Y, ∑ j ∈ Finset.range Y,
    coefficient f n*conj (coefficient f j)*offDiagonalSign N n j

private lemma local_eventual {N Y : ℕ} (big : Real.exp 10<(N:ℝ)) (ha : alpha N<beta)
    (yp : 0<Y) (f : HardySpace (alpha N) beta)
    (supp : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → f t=0) :
    ∀ᶠ m : ℕ in atTop, primePairForm N m f=localPairs N Y f := by
  have ns : 1<(N:ℝ) := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<10)).trans big
  have vanish (n : ℕ) (hi : Y≤n) : coefficient f n=0 := by
    have bound := Real.log_le_log (by exact_mod_cast yp : 0<(Y:ℝ)) (Nat.cast_le.mpr hi)
    have gone := PhysicalSupport.inner_zero (large_alpha_pos big).le ha (yp.trans_le hi) f
      (supp.mono (fun t h ht => h (by linarith)))
    simp only [coefficient,gone,mul_zero]
  filter_upwards [cutoff_large ns Y,eventually_ge_atTop 1] with m low hm
  have grow : 1<cutoff N m := one_lt_pow₀ (one_lt_pow₀ ns (by omega)) (by decide)
  have YX : (Y:ℝ)≤cutoff N m := low.trans (Real.sqrt_le_self_iff.mpr (Or.inr grow.le))
  let I := Finset.range Y
  let J := Finset.range (⌊cutoff N m⌋₊+1)
  have sub : I⊆J := Finset.range_mono (by have := Nat.le_floor YX; omega)
  have coeff (n : ℕ) : testCoefficient N m n f=coefficient f n := by
    have id : testCoefficient N m n f=coefficient f n*(smoothedPerronWeight (cutoff N m) n:ℂ) := by
      dsimp [testCoefficient,coefficient]; ring
    rw [id]
    by_cases hi : Y≤n
    · simp [vanish n hi]
    · have sm : smoothedPerronWeight (cutoff N m) n=1 :=
        ite_eq_left ((Nat.cast_le.mpr (Nat.le_of_lt (lt_of_not_ge hi))).trans low)
      simp [sm]
  let W (n j : ℕ) := coefficient f n*conj (coefficient f j)*offDiagonalSign N n j
  unfold primePairForm
  simp_rw [coeff]
  change ∑ n ∈ J, ∑ j ∈ J, W n j=∑ n ∈ I, ∑ j ∈ I, W n j
  calc
    _ = ∑ n ∈ I, ∑ j ∈ J, W n j := (Finset.sum_subset sub (fun n _ hn => by
        have hi : Y≤n := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
        simp [W,vanish n hi])).symm
    _ = _ := Finset.sum_congr rfl (fun n _ => (Finset.sum_subset sub (fun j _ hj => by
      have hi : Y≤j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
      simp [W,vanish j hi])).symm)

/-- On every finite time window, the unmodified infinite arithmetic form
is exactly the signed sum over pairs below the endpoint. -/
theorem exact_local_pairs (N Y : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (yp : 0<Y) (f : HardySpace (alpha N) beta)
    (supp : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → f t=0) :
    inner ℂ f ((arithmeticOperator ha N-diagonalOperator ha N) f)=localPairs N Y f := by
  have diff := (gram_limit N big g ha).sub (diagonal_limit N big ha)
  have cont : Continuous (fun A : HardySpace (alpha N) beta →L[ℂ] HardySpace (alpha N) beta =>
    inner ℂ f (A f)) := by fun_prop
  have lim := cont.continuousAt.tendsto.comp diff
  apply tendsto_nhds_unique lim
  apply tendsto_const_nhds.congr'
  filter_upwards [local_eventual big ha yp f supp] with m hm
  change localPairs N Y f=inner ℂ f ((primeGram N m-primeDiagonal N m) f)
  rw [off_diagonal_quadratic N m even (large_parameters big).1 f,hm]

/-- The entire original arithmetic compression vanishes exactly when
both indices lie below half the modulus. -/
theorem short_arithmetic_zero (N Y : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (yp : 0<Y) (ys : 2*Y≤N) (f : HardySpace (alpha N) beta)
    (supp : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → f t=0) :
    inner ℂ f ((arithmeticOperator ha N-diagonalOperator ha N) f)=0 := by
  rw [exact_local_pairs N Y even big g ha yp f supp]
  obtain ⟨m,eq⟩ := (local_eventual big ha yp f supp).exists
  exact eq.symm.trans (PhysicalSupport.short_pairs_zero yp ys m (large_alpha_pos big).le ha f supp)

#print axioms short_arithmetic_zero
#print axioms exact_local_pairs
end GoldbachSpectral435.LocalPrimeForm
