module
public import Characters
public import Diagonal
public import BetaCross
public import Kernel
public import ConditionalGoldbach.Proofs.MellinResidual

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory ConditionalGoldbach Complex Set
namespace GoldbachSpectral435

/-- The same test vector at every interior integration line. -/
def testVector (N M : ℕ) (hm : 0 < M) (f : ℝ → ℝ) (s : FiniteModelWeight f) :
    HardySpace (alpha N) beta := Classical.choose
    (finite_functional_riesz_exists (a := alpha N) M hm (companion f)
      ((FiniteModel.companion_contDiff s).of_le (by norm_num)) _ _ s.lower_pos (FiniteModel.companion_support_subset s))

theorem testVector_rep (N M : ℕ) (hm : 0 < M) (f : ℝ → ℝ) (s : FiniteModelWeight f)
    (σ : ℝ) (hs : 0 < σ) (hab : σ ∈ Ioo (alpha N) beta) (ψ : HardySpace (alpha N) beta) :
    finiteFunctionalValue M (companion f) σ ψ = paperInner ψ (testVector N M hm f s) :=
  Classical.choose_spec (finite_functional_riesz_exists (a := alpha N) M hm (companion f)
    ((FiniteModel.companion_contDiff s).of_le (by norm_num)) _ _ s.lower_pos (FiniteModel.companion_support_subset s)) σ hs hab ψ

/-- Exact quadratic identity with the progression modulus N, a physical
sampling scale 2N, and the half-integer samples of the continued beta model. -/
theorem doubled_quadratic (N : ℕ) [NeZero N] (he : Even N) (lar : Real.exp 10 < (N:ℝ))
    (grh : GRH N) (ha : alpha N < beta) (f : ℝ → ℝ) (sf : FiniteModelWeight f)
    (σ : ℝ) (hs : 0<σ) (hab : σ ∈ Ioo (alpha N) beta) (hu : σ ≤ 1/9) :
    let M := 2*N
    let x := testVector N M (by have := NeZero.pos N; change 0 < 2*N; omega) f sf
    ‖x‖^2 = normFunctional M f (alpha N) ∧ paperInner (residualOperator ha N x) x =
      ((2/(N.totient:ℂ))*∑ χ ∈ oddCharacters N,
        characterSample χ M (companion f)*characterSample (star χ) M (companion f)) -
      (∑' i : ℕ, diagCoeff N i*(companion f ((i+1:ℕ)/(M:ℝ)):ℂ)^2) -
      ∑' j : ℕ, (singularSeries ((j+1)*N):ℂ)*(signedConvolution f (((j+1:ℕ):ℝ)/2):ℂ) := by
  intro M x
  have np := NeZero.pos N
  have hm : 0 < M := by dsimp [M]; omega
  have nm : N ≤ M := by dsimp [M]; omega
  have rep := testVector_rep N M hm f sf σ hs hab
  refine ⟨mixed_vector_norm M hm f sf σ hs hab x rep,?_⟩
  obtain ⟨v,w,repr⟩ := mixed_kernel N M hm he lar grh ha (companion f) (companion f)
    ((FiniteModel.companion_contDiff sf).of_le (by norm_num)) ((FiniteModel.companion_contDiff sf).of_le (by norm_num))
    sf.lower_pos sf.lower_pos (FiniteModel.companion_support_subset sf) (FiniteModel.companion_support_subset sf)
  obtain ⟨rv,rw',ent⟩ := repr σ hs hab
  have eqV (u : HardySpace (alpha N) beta) (r : ∀ ψ, finiteFunctionalValue M (companion f) σ ψ = paperInner ψ u) : u=x := by
    apply ext_inner_right ℂ
    intro ψ
    change paperInner ψ u = paperInner ψ x
    exact (r ψ).symm.trans (rep ψ)
  rw [eqV v rv,eqV w rw'] at ent
  rw [ent]
  let L := mellinWeight f
  let W := fun s z : ℂ => (M:ℂ)^(s+z)*L s*L z
  let P := fun s z : ℂ => W s z*characterKernel N s z
  let D := fun s z : ℂ => W s z*diagonalSeries N (s+z)
  let K := fun s z : ℂ => W s z*continuedModel N s z
  obtain ⟨pi,pv⟩ := character_gram (large_parameters lar).1 grh M nm (companion f) (companion f)
    ((FiniteModel.companion_contDiff sf).of_le (by norm_num)) ((FiniteModel.companion_contDiff sf).of_le (by norm_num))
    (FiniteModel.companion_support_subset sf) (FiniteModel.companion_support_subset sf) σ hs (by linarith)
  obtain ⟨di,dv⟩ := diagonal_test N M hm f sf σ hs
  obtain ⟨ki,kv⟩ := half_double_sampling N he np f sf σ hs hu
  let J := fun s z : ℂ => (2:ℂ)^(s+z)*(L s*L z*continuedDensity N (s+z)*betaKernel s z)
  have matchK (t v : ℝ) : K (line σ t) (line σ v) = J (line σ t) (line σ v) := by
    let s := line σ t
    let z := line σ v
    have fact : (M:ℂ)^(s+z)=(2:ℂ)^(s+z)*(N:ℂ)^(s+z) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg N) (s+z)
    have eqn := weighted_continuedModel_cancel N np f s z (mellin_betaDomain_line σ hs hu t v)
    change (M:ℂ)^(s+z)*L s*L z*continuedModel N s z = J s z
    rw [fact]
    dsimp only [J,L]
    linear_combination (2:ℂ)^(s+z)*eqn
  have ki' : Integrable (fun p : ℝ × ℝ => K (line σ p.1) (line σ p.2)) :=
    ki.congr (Filter.Eventually.of_forall (fun p => (matchK p.1 p.2).symm))
  have kv' : verticalMellin σ (fun s => verticalMellin σ (K s)) =
      verticalMellin σ (fun s => verticalMellin σ (J s)) := by
    unfold verticalMellin
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    congr 1
    apply integral_congr_ae
    filter_upwards [] with v
    exact matchK t v
  have split (s z : ℂ) : W s z*residual N s z = (P s z-D s z)-K s z := by
    dsimp [P,D,K,ConditionalGoldbach.residual]; ring
  change verticalMellin σ (fun s => verticalMellin σ (fun z => W s z*residual N s z)) = _
  simp_rw [split]
  rw [double_verticalMellin_sub σ _ K (pi.sub di) ki',double_verticalMellin_sub σ P D pi di,
    kv']
  exact congrArg₂ (· - ·) (congrArg₂ (· - ·) pv dv) kv

#print axioms doubled_quadratic
end GoldbachSpectral435

