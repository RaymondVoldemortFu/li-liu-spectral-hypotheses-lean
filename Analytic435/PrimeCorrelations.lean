module
public import PrimeResidual
public import ConditionalGoldbach.Proofs.CharacterShortPolynomial

/-! Signed residue correlations for every unit test of the arithmetic
operator. All coefficients are finite prime-power sums. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex MeasureTheory Filter Set InnerProductSpace
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PerronApproximation

def testCoefficient (N m n : ℕ) (f : HardySpace (alpha N) beta) : ℂ :=
  -(mangoldt n:ℂ)*(n:ℂ)^(-(1/2:ℂ))*smoothedPerronWeight (cutoff N m) n *
    inner ℂ f (diagonalHardyVector n)

private lemma coefficient_transform (N m : ℕ) (χ : Character N) (f : HardySpace (alpha N) beta) :
    inner ℂ f (polyVector χ m) = ∑ n ∈ Finset.range (⌊cutoff N m⌋₊+1),
      testCoefficient N m n f * χ n := by
  rw [polyVector,inner_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [inner_smul_right]
  unfold testCoefficient
  ring

def residueSign (N n j : ℕ) : ℂ :=
  if Nat.Coprime (n*j) N then
    (if (n:ZMod N)=j then (1:ℂ) else 0) - (if (n:ZMod N)=-(j:ZMod N) then 1 else 0) else 0

private lemma rank_test {N : ℕ} (f v : HardySpace (alpha N) beta) :
    inner ℂ f (rankOne ℂ v v f) = ((‖inner ℂ f v‖^2:ℝ):ℂ) := by
  rw [rankOne_apply,inner_smul_right,← inner_conj_symm v f,Complex.sq_norm,Complex.normSq_eq_conj_mul_self]

theorem gram_quadratic (N m : ℕ) [NeZero N] (he : Even N) (four : 4≤N)
    (f : HardySpace (alpha N) beta) :
    inner ℂ f (primeGram N m f) =
      ∑ n ∈ Finset.range (⌊cutoff N m⌋₊+1), ∑ j ∈ Finset.range (⌊cutoff N m⌋₊+1),
        testCoefficient N m n f * conj (testCoefficient N m j f) * residueSign N n j := by
  classical
  let w : ℝ := 2/(N.totient:ℝ)
  have wp : 0≤w := by dsimp [w]; positivity
  let I := Finset.range (⌊cutoff N m⌋₊+1)
  let c := fun n => testCoefficient N m n f

  have val (χ : Character N) :
      inner ℂ f (rankOne ℂ ((Real.sqrt w:ℂ) • polyVector χ m) ((Real.sqrt w:ℂ) • polyVector χ m) f) =
      ((w*‖∑ n ∈ I, c n * χ n‖^2 : ℝ):ℂ) := by
    rw [rank_test,inner_smul_right,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt wp,
      coefficient_transform]
  unfold primeGram
  rw [sum_apply,inner_sum]
  change (∑ χ : {χ : Character N // χ ∈ oddCharacters N}, inner ℂ f
    (rankOne ℂ ((Real.sqrt w:ℂ) • polyVector χ.val m) ((Real.sqrt w:ℂ) • polyVector χ.val m) f)) = _
  simp_rw [val]
  rw [Finset.sum_coe_sort (oddCharacters N) (fun χ : Character N => ((w*‖∑ n ∈ I, c n * χ n‖^2:ℝ):ℂ)),
    ← Complex.ofReal_sum,← Finset.mul_sum]
  exact odd_character_quadratic_complex N he four I c

private lemma coefficient_energy (N m n : ℕ) (hn : 0<n) (f : HardySpace (alpha N) beta) :
    ‖testCoefficient N m n f‖^2 =
      (mangoldt n)^2/(n:ℝ) * (smoothedPerronWeight (cutoff N m) n)^2 * ‖inner ℂ f (diagonalHardyVector n)‖^2 := by
  unfold testCoefficient
  simp only [norm_mul,mul_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Complex.norm_natCast_cpow_of_pos hn,neg_re,div_ofNat_re,one_re]
  have poweq : ((n:ℝ)^(-(1/2:ℝ)))^2 = (n:ℝ)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num [Real.rpow_neg_one]
  rw [poweq]
  ring

theorem diagonal_quadratic (N m : ℕ) (f : HardySpace (alpha N) beta) :
    inner ℂ f (primeDiagonal N m f) =
      ∑ n ∈ Finset.range (⌊cutoff N m⌋₊+1),
        if Nat.Coprime n N then ((‖testCoefficient N m n f‖^2:ℝ):ℂ) else 0 := by
  classical
  rw [primeDiagonal,sum_apply,inner_sum,Finset.sum_range_succ']
  have z : testCoefficient N m 0 f = 0 := by simp [testCoefficient,mangoldt]
  simp only [z,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,Complex.ofReal_zero,ite_self,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_apply,inner_smul_right,rank_test,diagonalRankVector,inner_smul_right,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (diagonalCoefficient_nonneg N j),
    coefficient_energy N m (j+1) (by omega) f]
  unfold diagonalCoefficient
  split_ifs <;> push_cast <;> ring

/-- Only distinct indices in a common or opposite unit residue class
contribute after subtraction of the diagonal. -/
def offDiagonalSign (N n j : ℕ) : ℂ :=
  residueSign N n j - if n=j ∧ n.Coprime N then 1 else 0

def primePairForm (N m : ℕ) (f : HardySpace (alpha N) beta) : ℂ :=
  ∑ n ∈ Finset.range (⌊cutoff N m⌋₊+1), ∑ j ∈ Finset.range (⌊cutoff N m⌋₊+1),
    testCoefficient N m n f * conj (testCoefficient N m j f) * offDiagonalSign N n j

theorem off_diagonal_quadratic (N m : ℕ) [NeZero N] (he : Even N) (four : 4≤N)
    (f : HardySpace (alpha N) beta) :
    inner ℂ f ((primeGram N m-primeDiagonal N m) f) = primePairForm N m f := by
  classical
  let I := Finset.range (⌊cutoff N m⌋₊+1)
  let c := fun n => testCoefficient N m n f
  have diag (n : ℕ) (hn : n∈I) :
      (∑ j ∈ I, c n*conj (c j)*(if n=j ∧ n.Coprime N then 1 else 0)) =
      if n.Coprime N then ((‖c n‖^2:ℝ):ℂ) else 0 := by
    by_cases cp : n.Coprime N
    · simp only [mul_ite,mul_one,mul_zero]
      rw [Finset.sum_eq_single n]
      · simp [Complex.mul_conj,Complex.sq_norm]
      · intro j _ ne
        simp [Ne.symm ne]
      · simp [hn]
    · simp [cp]
  rw [sub_apply,inner_sub_right,gram_quadratic N m he four,diagonal_quadratic]
  change _ - (∑ n ∈ I, if n.Coprime N then ((‖c n‖^2:ℝ):ℂ) else 0) = _
  rw [← Finset.sum_congr rfl diag,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [offDiagonalSign,c,mul_sub]

/-- A single signed prime-pair sum controls the quadratic form of the
original residual, uniformly for all test vectors at a given level. -/
theorem prime_pair_error : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
    Real.exp 10<(N:ℝ) → GRH N → ∀ (ha : alpha N<beta) (f : HardySpace (alpha N) beta),
    ‖inner ℂ f (residualOperator ha N f) -
      (primePairForm N (exponent N) f-inner ℂ f (modelOperator ha N f))‖ ≤
      C/(Real.log N)^16*‖f‖^2 := by
  obtain ⟨C,cp,err⟩ := residual_error
  refine ⟨C,cp,?_⟩
  intro N inst he big g ha f
  rw [← off_diagonal_quadratic N _ he (large_parameters big).1 f,← inner_sub_right,← inner_sub_right]
  change ‖inner ℂ f ((residualOperator ha N-primeResidual N ha) f)‖ ≤ _
  apply (norm_inner_le_norm _ _).trans
  have cap := ((residualOperator ha N-primeResidual N ha).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (err N inst he big g ha) (norm_nonneg _))
  exact (mul_le_mul_of_nonneg_left cap (norm_nonneg _)).trans_eq (by ring)

#print axioms prime_pair_error
#print axioms gram_quadratic
#print axioms diagonal_quadratic
end GoldbachSpectral435.PerronApproximation
