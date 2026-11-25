module
public import Quadratic
public import Residues

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex MeasureTheory Set
open scoped ComplexConjugate
namespace GoldbachSpectral435

def sampleValue (M n : ℕ) (f : ℝ → ℝ) : ℝ := mangoldt n*f (n/(M:ℝ))/Real.sqrt M

private theorem coefficient_identity {q : ℕ} (χ : Character q) (M n : ℕ) (hm : 0<M) (f : ℝ → ℝ) :
    ((mangoldt n:ℂ)*χ n/(n:ℂ)^(1/2:ℂ))*(companion f (n/(M:ℝ)):ℂ) =
      (sampleValue M n f:ℂ)*χ n := by
  by_cases nz : n=0
  · simp [nz,sampleValue,mangoldt]
  have np : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero nz
  have mp : 0<(M:ℝ) := by exact_mod_cast hm
  have ns : (Real.sqrt (n:ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr np).ne'
  have ms : (Real.sqrt (M:ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr mp).ne'
  have eqn : (Real.sqrt (n:ℝ):ℂ) = (n:ℂ)^(1/2:ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow np.le]
    norm_num
  rw [← eqn]
  unfold companion sampleValue
  rw [Real.sqrt_div np.le]
  push_cast
  field_simp

theorem finite_character_sample {q : ℕ} (χ : Character q) (M : ℕ) (hm : 0<M)
    (f : ℝ → ℝ) (sf : FiniteModelWeight f) :
    characterSample χ M (companion f) = ∑ n ∈ Finset.range M, (sampleValue M n f:ℂ)*χ n := by
  let W := fun n : ℕ => (sampleValue M n f:ℂ)*χ n
  have cut (n : ℕ) (h : n ∉ Finset.range M) : W n=0 := by
    have le : M≤n := by simpa using h
    have mp : 0<(M:ℝ) := by exact_mod_cast hm
    have z : f (n/(M:ℝ))=0 := by
      by_contra nn
      exact (not_lt_of_ge ((one_le_div mp).mpr (by exact_mod_cast le))) (sf.mem_support_unit nn).2
    simp only [W,sampleValue,z,mul_zero,zero_div,Complex.ofReal_zero,zero_mul]
  have zero : W 0=0 := by simp [W,sampleValue,mangoldt]
  have sm : Summable W := summable_of_ne_finset_zero cut
  have reduction : characterSample χ M (companion f) = ∑' i : ℕ, W (i+1) := by
    apply tsum_congr
    intro i
    dsimp only [W]
    simpa only [Nat.cast_add,Nat.cast_one] using coefficient_identity χ M (i+1) hm f
  rw [reduction]
  change (∑' i : ℕ, W (i+1)) = ∑ n ∈ Finset.range M, W n
  rw [← zero_add (∑' i : ℕ,W (i+1)),← zero,← sm.tsum_eq_zero_add,tsum_eq_sum cut]

/-- The Riesz vectors for finite model weights form a real-linear family. -/
theorem testVector_add (N M : ℕ) (hm : 0<M) (f g : ℝ → ℝ)
    (F : FiniteModelWeight f) (G : FiniteModelWeight g) (A : FiniteModelWeight (f+g))
    (σ : ℝ) (hs : 0<σ) (hab : σ ∈ Ioo (alpha N) beta) :
    testVector N M hm (f+g) A = testVector N M hm f F + testVector N M hm g G := by
  have addM (s : ℂ) : mellinWeight (f+g) s = mellinWeight f s + mellinWeight g s := by
    unfold mellinWeight mellin
    simp only [companion,Pi.add_apply,mul_add,Complex.ofReal_add,smul_add]
    exact integral_add (FiniteModel.mellinWeight_convergent F s) (FiniteModel.mellinWeight_convergent G s)
  apply ext_inner_right ℂ
  intro ψ
  rw [inner_add_left]
  change paperInner ψ _ = paperInner ψ _ + paperInner ψ _
  rw [← testVector_rep N M hm _ A σ hs hab,← testVector_rep N M hm _ F σ hs hab,← testVector_rep N M hm _ G σ hs hab]
  have hi (v : ℝ → ℝ) (s : FiniteModelWeight v) := finiteFunctionalValue_integrable M hm (companion v)
    ((FiniteModel.companion_contDiff s).of_le (by norm_num)) _ _ (FiniteModel.companion_support_subset s) σ hs hab ψ
  unfold finiteFunctionalValue verticalMellin
  change _ * (∫ t : ℝ,(M:ℂ)^(line σ t)*mellinWeight (f+g) (line σ t)*(1+line σ t)*fourierLaplace ψ (line σ t)) = _
  have point (s : ℂ) : (M:ℂ)^s*mellinWeight (f+g) s*(1+s)*fourierLaplace ψ s =
      (M:ℂ)^s*mellinWeight f s*(1+s)*fourierLaplace ψ s + (M:ℂ)^s*mellinWeight g s*(1+s)*fourierLaplace ψ s := by rw [addM]; ring
  simp_rw [point]
  exact (congrArg (fun t : ℂ => (2*(Real.pi:ℂ))⁻¹*t) (integral_add (hi f F) (hi g G))).trans (mul_add ..)

/-- Disjoint supports kill the polarized exact diagonal at every integer. -/
theorem diagonal_separated (N M : ℕ) (f g : ℝ → ℝ)
    (disjoint : ∀ u, f u*g u=0) (i : ℕ) :
    diagCoeff N i*(companion (f+g) ((i+1:ℕ)/(M:ℝ)):ℂ)^2 =
      diagCoeff N i*(companion f ((i+1:ℕ)/(M:ℝ)):ℂ)^2 +
      diagCoeff N i*(companion g ((i+1:ℕ)/(M:ℝ)):ℂ)^2 := by
  let u := (i+1:ℕ)/(M:ℝ)
  rcases mul_eq_zero.mp (disjoint u) with e|e <;>
    change diagCoeff N i*((Real.sqrt u*((f+g) u):ℝ):ℂ)^2 =
      diagCoeff N i*((Real.sqrt u*f u:ℝ):ℂ)^2 + diagCoeff N i*((Real.sqrt u*g u:ℝ):ℂ)^2 <;>
    simp only [Pi.add_apply,e,add_zero,zero_add,mul_zero,Complex.ofReal_zero,zero_pow (by decide : 2≠0)]

#print axioms finite_character_sample
#print axioms testVector_add
end GoldbachSpectral435

