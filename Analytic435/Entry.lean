module
public import Gram

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex Set
namespace GoldbachSpectral435

private def Dfin (N M : ℕ) (f : ℝ → ℝ) : ℂ := ∑ i ∈ Finset.range M,
  diagCoeff N i*(companion f ((i+1:ℕ)/(M:ℝ)):ℂ)^2
private def Bfin (N : ℕ) (f : ℝ → ℝ) : ℂ := ∑ j ∈ Finset.range 4,
  (singularSeries ((j+1)*N):ℂ)*(signedConvolution f (((j+1:ℕ):ℝ)/2):ℂ)

private theorem diag_trunc (N M : ℕ) (hm : 0<M) (f : ℝ → ℝ) (s : FiniteModelWeight f) :
    (∑' i : ℕ, diagCoeff N i*(companion f ((i+1:ℕ)/(M:ℝ)):ℂ)^2) = Dfin N M f := by
  apply tsum_eq_sum
  intro i hi
  have le : M ≤ i := by simpa using hi
  have mp : 0<(M:ℝ) := by exact_mod_cast hm
  have large : 1≤(i+1:ℕ)/(M:ℝ) := (one_le_div mp).mpr (by exact_mod_cast (by omega : M ≤ i+1))
  have z : f ((i+1:ℕ)/(M:ℝ))=0 := by by_contra nf; exact (not_lt_of_ge large) (s.mem_support_unit nf).2
  simp only [companion,z,mul_zero,Complex.ofReal_zero,zero_pow (by decide : 2≠0)]

private theorem beta_trunc (N : ℕ) (f : ℝ → ℝ) (s : FiniteModelWeight f) :
    (∑' j : ℕ, (singularSeries ((j+1)*N):ℂ)*(signedConvolution f (((j+1:ℕ):ℝ)/2):ℂ)) = Bfin N f := by
  apply tsum_eq_sum
  intro j hj
  have big : (4:ℝ)≤j := by exact_mod_cast (show 4≤j by simpa using hj)
  have z : signedConvolution f (((j+1:ℕ):ℝ)/2)=0 := by
    by_contra nf
    have hi := (FiniteModel.signedConvolution_support f s nf).2
    push_cast at hi
    linarith [s.upper_lt_one]
  rw [z,Complex.ofReal_zero,mul_zero]

def weights (M : ℕ) (f : ℝ → ℝ) : ℕ → ℂ := fun n => (sampleValue M n f:ℂ)

private theorem fin_quadratic (N : ℕ) [NeZero N] (he : Even N) (lar : Real.exp 10 < (N:ℝ))
    (grh : GRH N) (ha : alpha N < beta) (f : ℝ → ℝ) (s : FiniteModelWeight f)
    (σ : ℝ) (hs : 0<σ) (hab : σ ∈ Ioo (alpha N) beta) (hu : σ ≤ 1/9) :
    let M := 2*N
    let x := testVector N M (by have := NeZero.pos N; change 0<2*N; omega) f s
    paperInner (residualOperator ha N x) x =
      projected N M (weights M f) (weights M f) - Dfin N M f - Bfin N f := by
  intro M x
  have mp : 0<M := by have := NeZero.pos N; dsimp [M]; omega
  have e := (doubled_quadratic N he lar grh ha f s σ hs hab hu).2
  exact e.trans (congrArg₂ (· - ·) (congrArg₂ (· - ·)
    (gram_projected N M he (large_parameters lar).1 mp f f s s) (diag_trunc N M mp f s)) (beta_trunc N f s))

/-- The separated matrix observable is bounded by the actual norm times
the two exact Hardy norms. All three arithmetic kernels have been evaluated. -/
theorem opposite_entry_bound (N : ℕ) [NeZero N] (he : Even N) (lar : Real.exp 10 < (N:ℝ))
    (grh : GRH N) (ha : alpha N < beta) (f g : ℝ → ℝ)
    (F : FiniteModelWeight f) (G : FiniteModelWeight g) (A : FiniteModelWeight (f+g))
    (sf : Function.support f ⊆ Ioo (0:ℝ) (1/8)) (sg : Function.support g ⊆ Ioo (3/8:ℝ) (5/8))
    (refl : ∀ u, g (1-u)=g u) (σ : ℝ) (hs : 0<σ) (hab : σ ∈ Ioo (alpha N) beta) (hu : σ ≤ 1/9) :
    let M := 2*N
    ‖∑ m ∈ Finset.range M, weights M f m *
      (if m.Coprime N then weights M g (N+m)-weights M g (N-m) else 0)‖ ≤
      ‖residualOperator ha N‖*Real.sqrt (normFunctional M f (alpha N))*Real.sqrt (normFunctional M g (alpha N)) := by
  intro M
  have mp : 0<M := by have := NeZero.pos N; dsimp [M]; omega
  have pr : 0<(M:ℝ) := by exact_mod_cast mp
  let T := residualOperator ha N
  let x := testVector N M mp f F
  let y := testVector N M mp g G
  let U := weights M f
  let V := weights M g
  have addW : weights M (f+g) = U+V := by
    funext n
    simp [U,V,weights,sampleValue,mul_add,add_div]
  have dis (u : ℝ) : f u*g u=0 := by
    by_contra h
    obtain ⟨hf,hg⟩ := mul_ne_zero_iff.mp h
    linarith [(sf hf).2,(sg hg).1]
  have de : Dfin N M (f+g) = Dfin N M f+Dfin N M g := by
    unfold Dfin
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => diagonal_separated N M f g dis j)
  have be : Bfin N (f+g) = Bfin N f+Bfin N g := by
    unfold Bfin
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [half_cross_vanish f g F G A sf sg refl,Complex.ofReal_add,mul_add]
  have qx := fin_quadratic N he lar grh ha f F σ hs hab hu
  have qy := fin_quadratic N he lar grh ha g G σ hs hab hu
  have qa := fin_quadratic N he lar grh ha (f+g) A σ hs hab hu
  change paperInner (T (testVector N M mp (f+g) A)) (testVector N M mp (f+g) A) = _ at qa
  rw [testVector_add N M mp f g F G A σ hs hab,addW,projected_add N M he (large_parameters lar).1,de,be] at qa
  change paperInner (T x) x = projected N M U U - Dfin N M f - Bfin N f at qx
  change paperInner (T y) y = projected N M V V - Dfin N M g - Bfin N g at qy
  change paperInner (T (x+y)) (x+y) = _ at qa
  simp only [paperInner,map_add,inner_add_right,inner_add_left] at qa qx qy
  have eqn : inner ℂ x (T y) + inner ℂ y (T x) = 2*projected N M U V := by linear_combination qa-qx-qy
  have low (m : ℕ) (h : U m ≠ 0) : 0<m ∧ 4*m<N := by
    have nz : f (m/(M:ℝ))≠0 := by intro z; apply h; simp [U,weights,sampleValue,z]
    obtain ⟨lo,hi⟩ := sf nz
    have l := (lt_div_iff₀ pr).mp lo
    have r := (div_lt_iff₀ pr).mp hi
    dsimp [M] at r
    push_cast at r
    exact ⟨by exact_mod_cast (by linarith : (0:ℝ)<m),
      by exact_mod_cast (by linarith : 4*(m:ℝ)<N)⟩
  have high (n : ℕ) (h : V n ≠ 0) : 3*N<4*n ∧ 4*n<5*N := by
    have nz : g (n/(M:ℝ))≠0 := by intro z; apply h; simp [V,weights,sampleValue,z]
    obtain ⟨lo,hi⟩ := sg nz
    have l := (lt_div_iff₀ pr).mp lo
    have r := (div_lt_iff₀ pr).mp hi
    dsimp [M] at l r
    push_cast at l r
    exact ⟨by exact_mod_cast (by linarith : 3*(N:ℝ)<4*(n:ℝ)),
      by exact_mod_cast (by linarith : 4*(n:ℝ)<5*(N:ℝ))⟩
  have norm (v w : HardySpace (alpha N) beta) : ‖inner ℂ v (T w)‖ ≤ ‖T‖*‖v‖*‖w‖ := by
    exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left (T.le_opNorm w) (norm_nonneg v)).trans_eq (by ring))
  have n := norm_add_le (inner ℂ x (T y)) (inner ℂ y (T x))
  rw [eqn,norm_mul,Complex.norm_ofNat] at n
  have target : ‖projected N M U V‖ ≤ ‖T‖*‖x‖*‖y‖ := by nlinarith only [n,norm x y,norm y x]
  have xnorm := (doubled_quadratic N he lar grh ha f F σ hs hab hu).1
  have ynorm := (doubled_quadratic N he lar grh ha g G σ hs hab hu).1
  change ‖x‖^2 = normFunctional M f (alpha N) at xnorm
  change ‖y‖^2 = normFunctional M g (alpha N) at ynorm
  rw [← xnorm,← ynorm,Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  rw [projected_shifts N he (large_parameters lar).1 U V low high] at target
  exact target

#print axioms opposite_entry_bound
end GoldbachSpectral435

