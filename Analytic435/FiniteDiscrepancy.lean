module
public import Gram
public import ReflectionModel

/-! A finite signed-prime discrepancy for all integral dilations of the
original critical-strip operator. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Complex Finset
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.FiniteDiscrepancy
open GoldbachSpectral435.PerronApproximation

def arithmetic (N M : ℕ) (f : ℝ→ℝ) : ℂ :=
  ∑ n ∈ range M, ∑ j ∈ range M,
    (sampleValue M n f:ℂ)*(sampleValue M j f:ℂ)*offDiagonalSign N j n

def continuousModel (N k : ℕ) (f : ℝ→ℝ) : ℂ :=
  ∑ j ∈ range (2*k), (singularSeries ((j+1)*N):ℂ)*(signedConvolution f ((j+1:ℕ)/(k:ℝ)):ℂ)

private lemma finite_model (N k : ℕ) (kp : 0<k) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    (∑' j : ℕ, (singularSeries ((j+1)*N):ℂ)*(signedConvolution f ((j+1:ℕ)/(k:ℝ)):ℂ))=
      continuousModel N k f := by
  apply tsum_eq_sum
  intro j hj
  have le : 2*k≤j := Nat.le_of_not_gt (fun h => hj (mem_range.mpr h))
  have kr : 0<(k:ℝ) := by exact_mod_cast kp
  have upper : (2:ℝ)≤((j+1:ℕ):ℝ)/k := (le_div_iff₀ kr).mpr (by exact_mod_cast (show 2*k≤j+1 by omega))
  have zero : signedConvolution f ((j+1:ℕ)/(k:ℝ))=0 := by
    by_contra nz
    have u := (FiniteModel.signedConvolution_support f hf nz).2
    linarith [hf.upper_lt_one]
  rw [zero,Complex.ofReal_zero,mul_zero]

private lemma diagonal_term (N M n : ℕ) (mp : 0<M) (np : 0<n) (f : ℝ→ℝ) :
    (if n.Coprime N then (mangoldt n:ℂ)^2/n else 0)*(companion f (n/(M:ℝ)):ℂ)^2 =
      if n.Coprime N then (sampleValue M n f:ℂ)^2 else 0 := by
  by_cases cp : n.Coprime N
  · simp only [ite_eq_left cp,companion,sampleValue]
    have qr : 0≤(n:ℝ)/M := by positivity
    have rq : (mangoldt n)^2/(n:ℝ)*(Real.sqrt (n/(M:ℝ))*f (n/(M:ℝ)))^2 =
        (mangoldt n*f (n/(M:ℝ))/Real.sqrt M)^2 := by
      rw [mul_pow,Real.sq_sqrt qr,div_pow,Real.sq_sqrt (Nat.cast_nonneg M)]
      have n0 : (n:ℝ)≠0 := by exact_mod_cast np.ne'
      have m0 : (M:ℝ)≠0 := by exact_mod_cast mp.ne'
      field_simp
    exact_mod_cast rq
  · simp [ite_eq_right cp]

private lemma diagonal_sum (N M : ℕ) (mp : 0<M) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    (∑' i : ℕ, diagCoeff N i*(companion f ((i+1:ℕ)/(M:ℝ)):ℂ)^2) =
      ∑ n ∈ range M, if n.Coprime N then (sampleValue M n f:ℂ)^2 else 0 := by
  let g (n : ℕ) : ℂ := if n.Coprime N then (sampleValue M n f:ℂ)^2 else 0
  have term (i : ℕ) : diagCoeff N i*(companion f ((i+1:ℕ)/(M:ℝ)):ℂ)^2=g (i+1) :=
    diagonal_term N M _ mp (Nat.succ_pos _) f
  have large (n : ℕ) (hn : n∉range M) : g n=0 := by
    have nm : M≤n := Nat.le_of_not_gt (fun h => hn (mem_range.mpr h))
    have one : 1≤(n:ℝ)/M := (le_div_iff₀ (by exact_mod_cast mp : 0<(M:ℝ))).mpr (by rw [one_mul]; exact_mod_cast nm)
    have z : f (n/(M:ℝ))=0 := by
      by_contra nz
      exact (not_lt_of_ge one) (hf.mem_support_unit nz).2
    simp [g,sampleValue,z]
  have sum : Summable g := summable_of_ne_finset_zero (s:=range M) large
  have eq : (∑' n : ℕ, g n)=∑ n ∈ range M, g n := tsum_eq_sum large
  rw [sum.tsum_eq_zero_add] at eq
  have z : g 0=0 := by simp [g,sampleValue,mangoldt]
  rw [tsum_congr term]
  simpa only [z,zero_add] using eq

private lemma off_sum (N M : ℕ) [NeZero N] (even : Even N) (n4 : 4≤N)
    (f : ℝ→ℝ) : projected N M (fun n => (sampleValue M n f:ℂ)) (fun n => (sampleValue M n f:ℂ)) -
      (∑ n ∈ range M, if n.Coprime N then (sampleValue M n f:ℂ)^2 else 0)=arithmetic N M f := by
  let c (n : ℕ) : ℂ := sampleValue M n f
  have diag (n : ℕ) (hn : n∈range M) :
      (∑ j ∈ range M, c n*c j*(if j=n ∧ j.Coprime N then (1:ℂ) else 0)) =
        if n.Coprime N then (c n)^2 else 0 := by
    have term (j : ℕ) : c n*c j*(if j=n ∧ j.Coprime N then (1:ℂ) else 0)=
        if j=n then (if n.Coprime N then c n^2 else 0) else 0 := by
      by_cases e : j=n
      · subst j
        by_cases h : n.Coprime N <;> simp [h,pow_two]
      · simp [e]
    simp_rw [term]
    simp [Finset.sum_ite_eq',hn]
  unfold projected arithmetic
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  change (∑ j ∈ range M, c n*c j*selectOdd N j n)-(if n.Coprime N then c n^2 else 0)=_
  rw [← diag n hn,← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  have eq : selectOdd N j n=residueSign N j n := lemma_3_1_odd_orthogonality N even n4 j n
  simp only [eq,offDiagonalSign,c,mul_sub]

/-- At every integral dilation k, the exact original residual is a difference
of finite prime-pair and singular-series sums. Both the weight and the
dilation may depend on the modulus. -/
theorem exact_form (N k : ℕ) [NeZero N] (kp : 0<k) (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let M := k*N
    let x := testVector N M (Nat.mul_pos kp (NeZero.pos N)) f hf
    ‖x‖^2=normFunctional M f (alpha N) ∧
      paperInner (residualOperator ha N x) x=arithmetic N M f-continuousModel N k f := by
  intro M x
  have nr : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have lg := (Real.lt_log_iff_exp_lt nr).mpr big
  have ab : (1/9:ℝ)∈Ioo (alpha N) beta :=
    ⟨one_div_lt_one_div_of_lt (by norm_num) (by linarith),by norm_num [beta]⟩
  obtain ⟨norm,entry⟩ := multiple_quadratic k kp N even big grh ha f hf (1/9) (by norm_num) ab le_rfl
  refine ⟨norm,?_⟩
  rw [gram_projected N _ even (large_parameters big).1 (Nat.mul_pos kp (NeZero.pos N)) f f hf hf,
    diagonal_sum N _ (Nat.mul_pos kp (NeZero.pos N)) f hf,off_sum N _ even (large_parameters big).1 f,
    finite_model N k kp f hf] at entry
  exact entry

#print axioms exact_form
end GoldbachSpectral435.FiniteDiscrepancy
