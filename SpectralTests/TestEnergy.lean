module
public import SpectralTests.Weights
public import SpectralTests.ShiftDefinitions
public import Mathlib.Analysis.Calculus.Deriv.Support

@[expose] public section
namespace GoldbachSpectral
open Set MeasureTheory

/-- Estimate the derivative energy in physical coordinates. Outside the two
closed support intervals both the function and its derivative vanish. -/
theorem shift_energy {N : ℕ} {H P : ℝ} {b : ℝ → ℝ} (test : ShiftTest N H P b)
    (hi : Integrable (fun u => (b u/2-u*deriv b u)^2)) :
    energy b * H ≤ 9*P^2 := by
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one test.one_le
  have hP : 0 < P := hH.trans_le test.width_le
  obtain ⟨t,hJ⟩ := test.short_support
  let J := Icc t (t+H)
  let C := (3*P/H)^2
  have outside (a z u : ℝ) (hs : Function.support b ⊆ Icc a z) (hu : u ∉ Icc a z) :
      b u=0 ∧ deriv b u=0 := by
    have no : u ∉ tsupport b := fun h => hu ((closure_minimal hs isClosed_Icc) h)
    exact ⟨notMem_tsupport_iff_eventuallyEq.mp no |>.eq_of_nhds, deriv_of_notMem_tsupport no⟩
  have major (u : ℝ) : (b u/2-u*deriv b u)^2 ≤ J.indicator (fun _ => C) u := by
    by_cases hu : u ∈ J
    · rw [indicator_of_mem hu]
      by_cases hb : u ∈ Icc P (2*P)
      · have hpos : 0 ≤ u := hP.le.trans hb.1
        obtain ⟨v,d⟩ := test.normalized u
        have ha : |b u/2| ≤ 1/2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
          exact div_le_div_of_nonneg_right v (by norm_num)
        have hd : |deriv b u| ≤ 1/H := (le_div_iff₀ hH).mpr (by linarith)
        have hu' : |u*deriv b u| ≤ 2*P*(1/H) := by
          rw [abs_mul, abs_of_nonneg hpos]
          exact mul_le_mul hb.2 hd (abs_nonneg _) (by positivity)
        have htot := (abs_sub _ _).trans (add_le_add ha hu')
        apply sq_le_sq.mpr
        apply le_trans htot
        rw [abs_of_pos (by positivity : 0 < 3*P/H)]
        field_simp
        linarith [test.width_le]
      · obtain ⟨h₁,h₂⟩ := outside _ _ _ test.band hb
        rw [h₁,h₂]; simpa using sq_nonneg (3*P/H)
    · obtain ⟨h₁,h₂⟩ := outside _ _ _ hJ hu
      rw [indicator_of_notMem hu,h₁,h₂]
      norm_num
  have hij : Integrable (J.indicator (fun _ : ℝ => C)) :=
    (integrableOn_const (s := J) measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have est := integral_mono hi hij major
  rw [integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc_of_le (show t ≤ t+H by linarith), smul_eq_mul, add_sub_cancel_left] at est
  change energy b ≤ H*(3*P/H)^2 at est
  calc
    _ ≤ (H*(3*P/H)^2)*H := mul_le_mul_of_nonneg_right est hH.le
    _ = _ := by field_simp; ring

end GoldbachSpectral

