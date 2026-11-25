module
public import SpectralTests.Arithmetic
public import SpectralTests.Weights
public import SpectralTests.Thresholds
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section
namespace GoldbachSpectral
open MeasureTheory
open scoped InnerProductSpace

/-- A symmetric weight has f((N-n)/N)=f(n/N) on every summand. -/
theorem reflected_weight {N n : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (f : ℝ → ℝ) (hs : ∀ x, f (1-x) = f x) :
    f (((N-n:ℕ):ℝ)/N) = f ((n:ℝ)/N) := by
  rw [Nat.cast_sub hn, sub_div, div_self (by exact_mod_cast hN.ne')]
  exact hs _

noncomputable def defect (N : ℕ) (s : ℝ) (f : ℝ → ℝ) :=
  s * (∫ u, (f u)^2) - sample N (fun u => (f u)^2)

private theorem sample_expand (N : ℕ) (f g : ℝ → ℝ) :
    sample N (fun u => (f u+g u)^2) =
      sample N (fun u => (f u)^2) + sample N (fun u => (g u)^2)
      + 2*sample N (fun u => f u*g u) := by
  unfold sample
  simp_rw [show ∀ n : ℕ, coeff N n * (f ((n:ℝ)/N) + g ((n:ℝ)/N))^2 =
    coeff N n * (f ((n:ℝ)/N))^2 + coeff N n * (g ((n:ℝ)/N))^2 +
    2*(coeff N n * (f ((n:ℝ)/N)*g ((n:ℝ)/N))) by intro n; ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem defect_polarize (N : ℕ) (s : ℝ) (f g : ℝ → ℝ)
    (hf : Integrable (fun u => (f u)^2)) (hg : Integrable (fun u => (g u)^2))
    (hfg : Integrable (fun u => f u*g u)) :
    defect N s (fun u => f u+g u) - defect N s f - defect N s g =
      2*(s*(∫ u, f u*g u) - sample N (fun u => f u*g u)) := by
  unfold defect
  rw [sample_expand]
  have he : (fun u => (f u+g u)^2) =
      (fun u => (f u)^2 + (g u)^2 + 2*(f u*g u)) := by funext u; ring
  have hsum : Integrable (fun u => (f u)^2 + (g u)^2) := hf.add hg
  have hcross : Integrable (fun u => 2*(f u*g u)) := hfg.const_mul 2
  rw [he, integral_add hsum hcross, integral_add hf hg, integral_const_mul]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def form (T : E →L[ℂ] E) (x : E) := (inner ℂ x (T x)).re

/-- These three equalities are the diagonal identity (7.17) at f, g, f+g;
the linear dependence of the Riesz vector on real weights is included in the last one. -/
structure DiagonalData (N : ℕ) (s : ℝ) (T : E →L[ℂ] E) (f g : ℝ → ℝ) (x y : E) : Prop where
  first : defect N s f = form T x
  second : defect N s g = form T y
  together : defect N s (fun u => f u+g u) = form T (x+y)

private theorem mixed_bound (T : E →L[ℂ] E) (x y : E) :
    (inner ℂ x (T y)).re ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
  calc
    _ ≤ ‖inner ℂ x (T y)‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖T y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖*‖y‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

theorem gap_cube {N : ℕ} {s w A B J : ℝ} {b g : ℝ → ℝ} {T : E →L[ℂ] E} {x y : E}
    (hw : 0 < w) (hsmall : w ≤ 1/6) (hs : 0 ≤ s) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : 0 ≤ ∫ t, b t) (hb : Differentiable ℝ b)
    (hbnd : ∀ t, |b t| ≤ B ∧ |deriv b t| ≤ B)
    (hcut : ∀ t, 1 ≤ |t| → b t = 0 ∧ deriv b t = 0)
    (plateau : ∀ u, |u-1/2| < w → g u = 1)
    (hf : Integrable (fun u => (localize w b u)^2)) (hg : Integrable (fun u => (g u)^2))
    (hfg : Integrable (fun u => localize w b u*g u))
    (hi : Integrable (fun u => (localize w b u / 2 - u*deriv (localize w b) u)^2))
    (data : DiagonalData N s T (localize w b) g x y)
    (Qf : ‖x‖^2 ≤ A*energy (localize w b)) (Qg : ‖y‖^2 ≤ J)
    (gap : EmptyWindow N w) :
    s^2 * (∫ t, b t)^2 * w^3 ≤ 8*A*B^2*J*‖T‖^2 := by
  have sup := localized_support hw (fun t h => (hcut t h).1)
  have prod : (fun u => localize w b u*g u) = localize w b := by
    funext u
    by_cases h : |u-1/2| < w
    · rw [plateau u h, mul_one]
    · rw [sup u (le_of_not_gt h), zero_mul]
  have iden := defect_polarize N s (localize w b) g hf hg hfg
  rw [sample_zero_of_empty gap sup, sub_zero, prod, localized_mass _ hw,
    data.together, data.first, data.second] at iden
  simp only [form, map_add, inner_add_left, inner_add_right, Complex.add_re] at iden
  have hh : s * (w * ∫ t, b t) ≤ ‖T‖*‖x‖*‖y‖ := by
    linarith [mixed_bound T x y, mixed_bound T y x, mul_comm ‖x‖ ‖y‖]
  have hsq := pow_le_pow_left₀ (mul_nonneg hs (mul_nonneg hw.le hm)) hh 2
  have hx : ‖x‖^2 * w ≤ A*(8*B^2) := calc
    _ ≤ (A * energy (localize w b)) * w := mul_le_mul_of_nonneg_right Qf hw.le
    _ = A*(energy (localize w b)*w) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (localized_energy hw hsmall hB hb hbnd hcut hi) hA
  calc
    _ = (s*(w*∫ t, b t))^2 * w := by ring
    _ ≤ (‖T‖*‖x‖*‖y‖)^2*w := mul_le_mul_of_nonneg_right hsq hw.le
    _ = (‖x‖^2*w) * ‖y‖^2 * ‖T‖^2 := by ring
    _ ≤ (A*(8*B^2))*J*‖T‖^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hx Qg (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- Bounds for the relative half-width w, in precisely the squared scales of S and R. -/
theorem window_thresholds {N : ℕ} {s h M w I C : ℝ} (hn : 1 < N)
    (hs : 0 < s) (hh : 0 < h) (hC : 0 ≤ C) (hadm : width N s h ≤ 1/4)
    (gapBound : s^2*I^2*w^3 ≤ C*M^2) :
    (Rbound (deltaSq N s) M → (N:ℝ)*s*I^2*w^3 ≤ C*Real.log N^3) ∧
    (Sbound (deltaSq N s) M (width N s h) → 3*h^2*I^2*w^3 ≤ C) := by
  constructor
  · intro hr
    have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hm := gapBound.trans (mul_le_mul_of_nonneg_left hr hC)
    unfold deltaSq at hm
    field_simp at hm
    apply (mul_le_mul_iff_of_pos_right hs).mp
    nlinarith [hm]
  · intro hz
    have h1 := S_implies_normalized_bound hn hs hh hadm hz
    have h2 := mul_le_mul_of_nonneg_left gapBound (show 0 ≤ 3*h^2 by positivity)
    have h3 := mul_le_mul_of_nonneg_left h1 hC
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hs)).mp
    nlinarith [h2,h3]

end GoldbachSpectral

