module
public import Dilation

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
namespace GoldbachSpectral435
open ConditionalGoldbach

/-- Sampling at k/2 allows both cutoffs to be inside (0,1), while one
physical test is centred at N. The density series still has modulus N. -/
theorem half_sampling (N : ℕ) (he : Even N) (hn : 0 < N)
    (φ : ℝ → ℝ) (smooth : FiniteModelWeight φ) (a : ℝ) (ha : 0 < a) :
    verticalMellin a (fun w => (2:ℂ)^w*continuedDensity N w*
      mellin (fun y => (signedConvolution φ y:ℂ)) w) =
      ∑' j : ℕ, (singularSeries ((j+1)*N):ℂ) * (signedConvolution φ (((j+1:ℕ):ℝ)/2):ℂ) := by
  simpa using dilated_sampling 2 (by norm_num) N he hn φ smooth a ha

/-- The continued beta kernel on the actual original contour, after
doubling the physical scale. All series and integrals are Bochner integrals
or unconditional sums in the original normalization. -/
theorem half_double_sampling (N : ℕ) (he : Even N) (hn : 0 < N)
    (φ : ℝ → ℝ) (smooth : FiniteModelWeight φ) (σ : ℝ) (hs : 0 < σ) (hu : σ ≤ 1/9) :
    Integrable (fun p : ℝ × ℝ => (2:ℂ)^(line σ p.1+line σ p.2)*
      (mellinWeight φ (line σ p.1)*mellinWeight φ (line σ p.2)*continuedDensity N (line σ p.1+line σ p.2)*betaKernel (line σ p.1) (line σ p.2))) ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z => (2:ℂ)^(s+z) *
      (mellinWeight φ s * mellinWeight φ z * continuedDensity N (s+z) * betaKernel s z))) =
      ∑' j : ℕ, (singularSeries ((j+1)*N):ℂ) * (signedConvolution φ (((j+1:ℕ):ℝ)/2):ℂ) := by
  simpa using dilated_double_sampling 2 (by norm_num) N he hn φ smooth σ hs hu

#print axioms half_double_sampling
end GoldbachSpectral435
