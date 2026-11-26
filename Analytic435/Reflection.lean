module
public import LocalPrimeForm

/-! The first Goldbach line in the arithmetic operator on the original strip. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex InnerProductSpace
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.Reflection
open GoldbachSpectral435.PerronApproximation GoldbachSpectral435.LocalPrimeForm

private lemma subtract_diagonal (p q e r : Prop) [Decidable p] [Decidable q] [Decidable e] [Decidable r]
    (same : e → (p ↔ q)) (reflected : r → (p ↔ q)) :
    ((if p ∧ q then (if e then (1:ℂ) else 0)-(if r then 1 else 0) else 0)-
      (if e ∧ p then 1 else 0)) = if p ∧ r then -1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases he : e <;> by_cases hr : r <;>
    simp_all

private lemma sign_first {N n j : ℕ} (np : 0<n) (nb : n<N) (jp : 0<j) (jb : j<N) :
    offDiagonalSign N n j = if n.Coprime N ∧ j=N-n then (-1:ℂ) else 0 := by
  obtain ⟨eq,neg⟩ := residue_diagonals (by omega : 0<N) np nb jp jb
  have refl : n+j=N ↔ j=N-n := by omega
  unfold offDiagonalSign residueSign
  simp only [Nat.coprime_mul_iff_left,eq,neg,refl]
  apply subtract_diagonal
  · rintro rfl
    rfl
  · rintro rfl
    exact (Nat.coprime_self_sub_left nb.le).symm

/-- Below the modulus, subtracting the diagonal leaves one reflection.
The coefficients may be arbitrary complex numbers. -/
theorem finite_reflection (N : ℕ) (a b : ℕ → ℂ) (az : a 0=0) (bz : b 0=0) :
    (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range N, a n*conj (b j)*offDiagonalSign N n j)=
      -(∑ n ∈ Finset.range N, if n.Coprime N then a n*conj (b (N-n)) else 0) := by
  classical
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases nz : n=0
  · simp [nz,az]
  have np : 0<n := by omega
  have nb := Finset.mem_range.mp hn
  have row (j : ℕ) (hj : j∈Finset.range N) :
      a n*conj (b j)*offDiagonalSign N n j =
        if j=N-n then -(if n.Coprime N then a n*conj (b (N-n)) else 0) else 0 := by
    by_cases jz : j=0
    · subst j; simp [bz,show 0≠N-n by omega]
    rw [sign_first np nb (by omega : 0<j) (Finset.mem_range.mp hj)]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl row]
  simp [Finset.sum_ite_eq',show N-n<N by omega]

def goldbachLine (N : ℕ) (f g : HardySpace (alpha N) beta) : ℂ :=
  ∑ n ∈ Finset.range N, if n.Coprime N then coefficient f n*conj (coefficient g (N-n)) else 0

private lemma coefficient_zero {N : ℕ} (f : HardySpace (alpha N) beta) : coefficient f 0=0 := by
  simp [coefficient,mangoldt]

/-- The exact arithmetic quadratic form on the whole first physical block
of the infinite Hardy space, including nonsmooth and complex vectors. -/
theorem first_block (N : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (f : HardySpace (alpha N) beta)
    (supp : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log N → f t=0) :
    inner ℂ f ((arithmeticOperator ha N-diagonalOperator ha N) f) = -goldbachLine N f f := by
  rw [exact_local_pairs N N even big g ha (NeZero.pos N) f supp]
  exact finite_reflection N _ _ (coefficient_zero f) (coefficient_zero f)

private def factor (n : ℕ) : ℂ := -(mangoldt n:ℂ)*(n:ℂ)^(-(1/2:ℂ))

def pairSum (N Y : ℕ) (f g : HardySpace (alpha N) beta) : ℂ :=
  ∑ n ∈ Finset.range Y, ∑ j ∈ Finset.range Y,
    coefficient f n*conj (coefficient g j)*offDiagonalSign N n j

private def pairOperator (N Y : ℕ) :
    HardySpace (alpha N) beta →L[ℂ] HardySpace (alpha N) beta :=
  ∑ n ∈ Finset.range Y, ∑ j ∈ Finset.range Y,
    (factor n*conj (factor j)*offDiagonalSign N n j) •
      rankOne ℂ (diagonalHardyVector n) (diagonalHardyVector j)

private lemma pair_entry (N Y : ℕ) (f g : HardySpace (alpha N) beta) :
    inner ℂ f (pairOperator N Y g)=pairSum N Y f g := by
  classical
  unfold pairOperator pairSum
  simp only [sum_apply,inner_sum,smul_apply,rankOne_apply,inner_smul_right,coefficient,factor,map_mul]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_conj_symm (diagonalHardyVector j) g]
  ring

private lemma sum_support {N Y : ℕ} {x y : HardySpace (alpha N) beta} (z : ℂ)
    (hx : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → x t=0)
    (hy : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → y t=0) :
    ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → (x+z • y) t=0 := by
  filter_upwards [Lp.coeFn_add x (z • y),Lp.coeFn_smul z y,hx,hy] with t a b c d ht
  exact a.trans (by change x t+(z • y) t=0; rw [b]; simp [c ht,d ht])

/-- The two inputs of the original infinite arithmetic operator may have
independent complex phases on any finite physical interval. -/
theorem mixed_local_pairs (N Y : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (yp : 0<Y) (x y : HardySpace (alpha N) beta)
    (hx : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → x t=0)
    (hy : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → y t=0) :
    inner ℂ x ((arithmeticOperator ha N-diagonalOperator ha N) y)=pairSum N Y x y := by
  let A := arithmeticOperator ha N-diagonalOperator ha N
  let T := A-pairOperator N Y
  have q (u : HardySpace (alpha N) beta)
      (hu : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → u t=0) : inner ℂ u (T u)=0 := by
    change inner ℂ u (A u-pairOperator N Y u)=0
    rw [inner_sub_right,pair_entry,show inner ℂ u (A u)=_ from exact_local_pairs N Y even big grh ha yp u hu]
    exact sub_self _
  have bil (z : ℂ) :
      z*inner ℂ x (T y)+conj z*inner ℂ y (T x)=0 := by
    have h := q _ (sum_support z hx hy)
    simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,q x hx,q y hy,
      mul_zero,zero_add,add_zero] at h
    linear_combination h
  have a := bil 1
  have b := bil Complex.I
  simp only [map_one,one_mul] at a
  simp only [Complex.conj_I,neg_mul] at b
  have zero : inner ℂ x (T y)=0 := by
    linear_combination (norm := (ring_nf; rw [Complex.I_sq]; ring)) a/2-Complex.I*b/2
  change inner ℂ x (A y-pairOperator N Y y)=0 at zero
  rw [inner_sub_right,pair_entry] at zero
  exact sub_eq_zero.mp zero

/-- The full first physical block consists of the single reflection
n ↦ N−n for arbitrary nonsmooth complex input and output tests. -/
theorem mixed_first_block (N : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (x y : HardySpace (alpha N) beta)
    (hx : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log N → x t=0)
    (hy : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log N → y t=0) :
    inner ℂ x ((arithmeticOperator ha N-diagonalOperator ha N) y) = -goldbachLine N x y := by
  rw [mixed_local_pairs N N even big grh ha (NeZero.pos N) x y hx hy]
  exact finite_reflection N _ _ (coefficient_zero x) (coefficient_zero y)

lemma widen {N U V : ℕ} (up : 0<U) (le : U≤V) (x : HardySpace (alpha N) beta)
    (h : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log U → x t=0) :
    ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log V → x t=0 := by
  have lt := Real.log_le_log (by exact_mod_cast up : 0<(U:ℝ)) (Nat.cast_le.mpr le)
  exact h.mono (fun t ht e => ht (by linarith))

lemma sample_zero {N U n : ℕ} (up : 0<U) (le : U≤n) (ap : 0≤alpha N)
    (ha : alpha N<beta) (x : HardySpace (alpha N) beta)
    (h : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log U → x t=0) : coefficient x n=0 := by
  rw [coefficient,PhysicalSupport.inner_zero ap ha (up.trans_le le) x (widen up le x h),mul_zero]

/-- The mixed arithmetic compression vanishes throughout Y+Z≤N. The two
physical windows can have arbitrarily different lengths. -/
theorem triangle_zero (N Y Z : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (yp : 0<Y) (zp : 0<Z) (total : Y+Z≤N)
    (x y : HardySpace (alpha N) beta)
    (hx : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → x t=0)
    (hy : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Z → y t=0) :
    inner ℂ x ((arithmeticOperator ha N-diagonalOperator ha N) y)=0 := by
  rw [mixed_first_block N even big grh ha x y (widen yp (by omega) x hx) (widen zp (by omega) y hy)]
  suffices goldbachLine N x y=0 by simp [this]
  unfold goldbachLine
  apply Finset.sum_eq_zero
  intro n _
  by_cases h : Y≤n
  · simp [sample_zero yp h (large_alpha_pos big).le ha x hx]
  · simp [sample_zero zp (by omega : Z≤N-n) (large_alpha_pos big).le ha y hy]

/-- On the first block, the original spectral discrepancy is exactly the
reflection sum plus the continuous model, with their original signs. -/
theorem residual_first_block (N : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (x y : HardySpace (alpha N) beta)
    (hx : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log N → x t=0)
    (hy : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log N → y t=0) :
    inner ℂ x (residualOperator ha N y) =
      -goldbachLine N x y-inner ℂ x (modelOperator ha N y) := by
  rw [residualOperator_components_at _ N (large_alpha_pos big) (large_parameters big).1 grh ha,
    sub_apply,inner_sub_right,mixed_first_block N even big grh ha x y hx hy]

#print axioms triangle_zero
#print axioms residual_first_block
#print axioms mixed_first_block
#print axioms first_block
end GoldbachSpectral435.Reflection
