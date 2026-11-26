module
public import TestCombinations
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! An exact norm criterion in terms of finite prime sums and finite
singular-series samples of real compact weights. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.FiniteDiscrepancy
open GoldbachSpectral435.PhysicalTests

def UniformBound (N : ℕ) (B : ℝ) : Prop :=
  ∀ k : ℕ, 0<k → ∀ f : ℝ→ℝ, FiniteModelWeight f →
    ‖arithmetic N (k*N) f-continuousModel N k f‖ ≤ B*normFunctional (k*N) f (alpha N)

private lemma split_i {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (x y : H) (same : inner ℂ y (A x)=inner ℂ x (A y)) :
    inner ℂ (x+Complex.I • y) (A (x+Complex.I • y))=inner ℂ x (A x)+inner ℂ y (A y) := by
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_right,inner_smul_left,Complex.conj_I,same]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma real_splits (N : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (x y : HardySpace (alpha N) beta) (hx : x∈tests N) (hy : y∈tests N) :
    let T := residualOperator ha N
    inner ℂ (x+Complex.I • y) (T (x+Complex.I • y))=inner ℂ x (T x)+inner ℂ y (T y) ∧
      ‖x+Complex.I • y‖^2=‖x‖^2+‖y‖^2 := by
  intro T
  obtain ⟨k,kp,⟨f,hf,ex⟩,j,hj,ey⟩ := common_scale N big hx hy
  have ap := large_alpha_pos big
  have sym := (residualOperator_spec_at _ N ap (large_parameters big).1 g ha).2.2.2.1.isSymmetric
  have r1 : conj (inner ℂ x (T y))=inner ℂ x (T y) := by
    rw [ex,ey]; exact residual_real N _ _ even big g ha f j hf hj
  have r2 : conj (inner ℂ x y)=inner ℂ x y := by
    rw [ex,ey]; exact inner_real N _ big _ f j hf hj
  have eq1 : inner ℂ y (T x)=inner ℂ x (T y) :=
    (sym y x).symm.trans ((inner_conj_symm (T y) x).symm.trans r1)
  refine ⟨split_i T x y eq1,?_⟩
  have eq2 : inner ℂ y x=inner ℂ x y := (inner_conj_symm y x).symm.trans r2
  have id := split_i (ContinuousLinearMap.id ℂ _) x y eq2
  change inner ℂ (x+Complex.I • y) (x+Complex.I • y)=inner ℂ x x+inner ℂ y y at id
  simp only [inner_self_eq_norm_sq_to_K] at id
  exact_mod_cast id

/-- The finite discrepancy bound on individual real C6 weights, uniformly
over all dilations, is equivalent to the full complex operator norm bound
at each eligible modulus. The best constants agree. -/
theorem norm_iff (N : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (B : ℝ) (bp : 0≤B) :
    ‖residualOperator ha N‖≤B ↔ UniformBound N B := by
  let T := residualOperator ha N
  constructor
  · intro cap k kp f hf
    obtain ⟨norm,entry⟩ := exact_form N k kp even big g ha f hf
    rw [← entry,← norm]
    let x := testVector N (k*N) (Nat.mul_pos kp (NeZero.pos N)) f hf
    change ‖inner ℂ x (T x)‖≤B*‖x‖^2
    exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left ((T.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right cap (norm_nonneg x))) (norm_nonneg x)).trans_eq (by ring))
  · intro finite
    have realcap (x : HardySpace (alpha N) beta) (hx : x∈tests N) :
        ‖inner ℂ x (T x)‖≤B*‖x‖^2 := by
      obtain ⟨k,kp,f,hf,rfl⟩ := hx
      obtain ⟨norm,entry⟩ := exact_form N k kp even big g ha f hf
      change ‖paperInner (T _) _‖≤_
      rw [entry,norm]
      exact finite k kp f hf
    have cap (z : HardySpace (alpha N) beta) : ‖inner ℂ z (T z)‖≤B*‖z‖^2 := by
      apply (closure_minimal (t:={v | ‖inner ℂ v (T v)‖≤B*‖v‖^2}) ?_ ?_) ((dense_complexification N big) z)
      · rintro _ ⟨x,hx,y,hy,rfl⟩
        change ‖inner ℂ (x+Complex.I • y) (T (x+Complex.I • y))‖≤B*‖x+Complex.I • y‖^2
        obtain ⟨form,norm⟩ := real_splits N even big g ha x y hx hy
        rw [form,norm,mul_add]
        exact (norm_add_le _ _).trans (add_le_add (realcap x hx) (realcap y hy))
      · apply isClosed_le <;> fun_prop
    have sym := (residualOperator_spec_at _ N (large_alpha_pos big) (large_parameters big).1 g ha).2.2.2.1.isSymmetric
    rw [T.norm_eq_iSup_rayleighQuotient sym]
    apply ciSup_le
    intro z
    by_cases zero : z=0
    · simpa [zero] using bp
    change |(inner ℂ (T z) z).re/‖z‖^2|≤B
    rw [abs_div,abs_of_nonneg (sq_nonneg ‖z‖)]
    apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr zero) _)).mpr
    exact (Complex.abs_re_le_norm _).trans ((congrArg norm (sym z z)).le.trans (cap z))

/-- Some original admissible h satisfies Hypothesis S exactly when these
explicit finite discrepancies have a uniform little-o bound at the
original boundary. The weights and dilations are chosen after the modulus. -/
theorem some_S_iff :
    (∃ h, HypothesisS h) ↔ ∀ ε : ℝ, 0<ε →
      EvenEventually (fun N => ∀ [NeZero N], GRH N → UniformBound N (ε*singularSeries N)) := by
  rw [some_actual_S_iff]
  constructor
  · intro lim ε ep
    obtain ⟨K,both⟩ := (lim ε ep).and evenEventually_large
    refine ⟨K,fun N hn he inst g => ?_⟩
    obtain ⟨b,big⟩ := both N hn he
    have ha := (large_parameters big).2.2
    rw [eligibleNorm_spec N ha g] at b
    exact (norm_iff N he big g ha _ (mul_nonneg ep.le (singularSeries_pos N).le)).mp b
  · intro lim ε ep
    obtain ⟨K,both⟩ := (lim ε ep).and evenEventually_large
    refine ⟨K,fun N hn he => ?_⟩
    obtain ⟨b,big⟩ := both N hn he
    obtain ⟨four,_,ha⟩ := large_parameters big
    let inst : NeZero N := ⟨by omega⟩
    have pos := mul_nonneg ep.le (singularSeries_pos N).le
    by_cases g : GRH N
    · rw [eligibleNorm_spec N ha g]
      exact (norm_iff N he big g ha _ pos).mpr (b g)
    · simpa [eligibleNorm,g] using pos

#print axioms norm_iff
#print axioms some_S_iff
end GoldbachSpectral435.FiniteDiscrepancy
