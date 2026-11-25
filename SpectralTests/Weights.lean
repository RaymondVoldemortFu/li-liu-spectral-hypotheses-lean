module
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
namespace GoldbachSpectral
open MeasureTheory Set

noncomputable def localize (w : ℝ) (b : ℝ → ℝ) (u : ℝ) := b ((u-1/2)/w)

noncomputable def energy (f : ℝ → ℝ) : ℝ := ∫ u, (f u / 2 - u * deriv f u)^2

theorem localized_mass (b : ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ u, localize w b u) = w * ∫ x, b x := by
  calc
    _ = ∫ u : ℝ, b (u/w) := integral_sub_right_eq_self (fun x : ℝ => b (x/w)) (1/2:ℝ)
    _ = _ := by rw [Measure.integral_comp_div, abs_of_pos hw, smul_eq_mul]

theorem localized_support {b : ℝ → ℝ} {w : ℝ} (hw : 0 < w)
    (hs : ∀ x, 1 ≤ |x| → b x = 0) :
    ∀ u : ℝ, w ≤ |u-1/2| → localize w b u = 0 := by
  intro u hu
  apply hs
  simpa [abs_div, abs_of_pos hw, le_div_iff₀ hw] using hu

theorem localized_deriv {b : ℝ → ℝ} (hb : Differentiable ℝ b) {w : ℝ} (u : ℝ) :
    deriv (localize w b) u = deriv b ((u-1/2)/w) / w := by
  have h₁ : HasDerivAt (fun t : ℝ => (t-1/2)/w) (1/w) u :=
    ((hasDerivAt_id u).sub_const (1/2:ℝ)).div_const w
  have h₂ := (hb ((u-1/2)/w)).hasDerivAt.comp u h₁
  change deriv (b ∘ (fun t : ℝ => (t-1/2)/w)) u = _
  rw [h₂.deriv]; ring

/-- The constant is uniform in the window width. The energy is the integrand
in (7.15) after substituting the companion weight Φ(u)=√u f(u). -/
theorem localized_energy {b : ℝ → ℝ} {w B : ℝ}
    (hw : 0 < w) (hsmall : w ≤ 1/6) (hB : 0 ≤ B) (hb : Differentiable ℝ b)
    (hbnd : ∀ x, |b x| ≤ B ∧ |deriv b x| ≤ B)
    (hcut : ∀ x, 1 ≤ |x| → b x = 0 ∧ deriv b x = 0)
    (hi : Integrable (fun u => (localize w b u / 2 - u * deriv (localize w b) u)^2)) :
    energy (localize w b) * w ≤ 8 * B^2 := by
  let J := Icc (1/2-w) (1/2+w)
  let C := (2*B/w)^2
  have major : ∀ u : ℝ, (localize w b u/2-u*deriv (localize w b) u)^2 ≤
      J.indicator (fun _ => C) u := by
    intro u
    rw [localized_deriv hb, localize]
    by_cases hj : u ∈ J
    · rw [indicator_of_mem hj]
      have hj' : 1/2-w ≤ u ∧ u ≤ 1/2+w := hj
      have hu : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hj'.1], by linarith [hj'.2]⟩
      obtain ⟨bf,bd⟩ := hbnd ((u-1/2)/w)
      have h₁ : |b ((u-1/2)/w) / 2| ≤ B/2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        exact div_le_div_of_nonneg_right bf (by norm_num)
      have h₂ : |u * (deriv b ((u-1/2)/w) / w)| ≤ B/w := by
        rw [abs_mul, abs_div, abs_of_pos hw]
        simpa using mul_le_mul hu (div_le_div_of_nonneg_right bd hw.le)
          (by positivity) zero_le_one
      have h₃ : B/2 + B/w ≤ 2*B/w := by
        field_simp
        nlinarith [mul_nonneg hB (show 0 ≤ 1-w by linarith)]
      have hab := (abs_sub _ _).trans ((add_le_add h₁ h₂).trans h₃)
      exact (sq_le_sq).mpr ((le_abs_self _).trans' hab)
    · rw [indicator_of_notMem hj]
      have hh : w ≤ |u-1/2| := by
        by_contra! hh
        obtain ⟨h₁,h₂⟩ := abs_lt.mp hh
        exact hj ⟨by linarith, by linarith⟩
      have hout : 1 ≤ |(u-1/2)/w| := by rwa [abs_div, abs_of_pos hw, le_div_iff₀ hw, one_mul]
      obtain ⟨e₁,e₂⟩ := hcut _ hout
      rw [e₁,e₂]; norm_num
  have hi' : Integrable (J.indicator (fun _ : ℝ => C)) :=
    (integrableOn_const (s := J) (measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  have hm := integral_mono hi hi' major
  rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le
    (show 1/2-w ≤ 1/2+w by linarith), smul_eq_mul] at hm
  change energy (localize w b) ≤ (1/2+w-(1/2-w)) * (2*B/w)^2 at hm
  calc
    _ ≤ ((1/2+w-(1/2-w)) * (2*B/w)^2) * w := mul_le_mul_of_nonneg_right hm hw.le
    _ = _ := by field_simp; ring

end GoldbachSpectral

