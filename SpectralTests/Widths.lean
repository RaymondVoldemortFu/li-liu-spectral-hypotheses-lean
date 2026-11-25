module
public import SpectralTests.Obstruction
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
namespace GoldbachSpectral
open Filter
open scoped Topology Quaternion

noncomputable def prescribedH (a N : ℕ) : ℝ :=
  if 1 < N then Real.sqrt ((N:ℝ)*singular N / (4*Real.log N^(a+3))) else 1

theorem prescribed_width (a N : ℕ) (hn : 1 < N) :
    width N (singular N) (prescribedH a N) = logWidth a N := by
  have hN : 1 < (N:ℝ) := by exact_mod_cast hn
  have hl := Real.log_pos hN
  have hs : 0 < singular N := lt_of_lt_of_le zero_lt_one (singular_lower N)
  rw [prescribedH, ite_eq_left hn, width, Real.sq_sqrt (by positivity), logWidth, pow_add]
  field_simp

private theorem log_power_over_N (k : ℕ) :
    Tendsto (fun N : ℕ => Real.log N^k / N) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem prescribed_admissible (a : ℕ) :
    (∀ N, 0 < prescribedH a N) ∧ Tendsto (prescribedH a) atTop atTop ∧
    ∀ᶠ N : ℕ in atTop, width N (singular N) (prescribedH a N) ≤ 1/4 := by
  have hs (N : ℕ) : 0 < singular N := lt_of_lt_of_le zero_lt_one (singular_lower N)
  constructor
  · intro N
    rw [prescribedH]
    split_ifs with hn
    · have hl := Real.log_pos (show (1:ℝ) < N by exact_mod_cast hn)
      exact Real.sqrt_pos.mpr (by have := hs N; positivity)
    · norm_num
  constructor
  · apply tendsto_atTop.mpr
    intro t
    let b := max t 1
    have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have ht : t ≤ b := le_max_left _ _
    have hp : (0:ℝ) < 1/(4*b^2) := by positivity
    filter_upwards [(log_power_over_N (a+3)).eventually_lt_const hp,
      eventually_gt_atTop 1] with N hbnd hn
    have hN : 1 < (N:ℝ) := by exact_mod_cast hn
    have hl := Real.log_pos hN
    have bound : 4*b^2 * Real.log N^(a+3) < N := by
      change Real.log N^(a+3)/(N:ℝ) < 1/(4*b^2) at hbnd
      field_simp at hbnd
      nlinarith [hbnd]
    apply ht.trans
    rw [prescribedH, ite_eq_left hn]
    apply (Real.le_sqrt hb.le (by have := hs N; positivity)).mpr
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (singular_lower N) (show (0:ℝ) ≤ N by positivity)]
  · have l := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [l.eventually_ge_atTop 1, eventually_gt_atTop 1] with N h hn
    change 1 ≤ Real.log N at h
    rw [prescribed_width a N hn, logWidth, div_le_iff₀ (by positivity)]
    linarith [one_le_pow₀ h (n := a)]

theorem admissible_even (a : ℕ) : Admissible (prescribedH a) := by
  obtain ⟨hp,hl,hw⟩ := prescribed_admissible a
  refine ⟨fun n _ _ => hp n, ?_, ?_⟩
  · intro b
    obtain ⟨K,H⟩ := eventually_atTop.mp (hl.eventually_ge_atTop b)
    exact ⟨K,fun n hn _ => H n hn⟩
  · obtain ⟨K,H⟩ := eventually_atTop.mp hw
    exact ⟨K,fun n hn _ => H n hn⟩

theorem prescribed_S_fails {M : ℕ → ℝ} {G : ℕ → Prop} {X : ℕ → ℍ[ℝ] → ℍ[ℝ]}
    (liu : LiuInput M G) (grh : ∀ N, Even N → G N) (D : ZeroFreeImpliesBound M G X)
    (a : ℕ) : ¬ HypothesisS G X (prescribedH a) := by
  apply (reject_R_and_wide_S liu grh D).2 _ a
  exact ⟨2, fun N hN _ _ => (prescribed_width a N (by omega)).ge⟩

/-- A scalar profile compatible with BOTH superlogarithmic scaled growth and
the slow S norm bound, using the actual arithmetic singular series. -/
noncomputable def slowProfile (N : ℕ) : ℝ := 1/Real.log N^2

theorem slow_compatibility :
    (∀ d : ℕ, ∀ᶠ N : ℕ in atTop, Real.log N^d < (N:ℝ)*(slowProfile N)^2) ∧
    (∀ᶠ N : ℕ in atTop, Sbound (deltaSq N (singular N)) (slowProfile N)
      (width N (singular N) (Real.log N))) := by
  have l := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  constructor
  · intro d
    filter_upwards [(log_power_over_N (d+4)).eventually_lt_const (by norm_num : (0:ℝ)<1),
      eventually_gt_atTop 1] with N hb hn
    have hN : 1 < (N:ℝ) := by exact_mod_cast hn
    have hl := Real.log_pos hN
    change Real.log N^(d+4)/(N:ℝ) < 1 at hb
    unfold slowProfile
    rw [pow_add, div_lt_iff₀ (by linarith), one_mul] at hb
    field_simp
    nlinarith [hb]
  · filter_upwards [l.eventually_ge_atTop 2, eventually_gt_atTop 1] with N h hn
    change 2 ≤ Real.log N at h
    have hN : 1 < (N:ℝ) := by exact_mod_cast hn
    have hs := singular_lower N
    have hs' : 0 < singular N := by linarith
    have he : 0 ≤ width N (singular N) (Real.log N) := by unfold width; positivity
    have hm : 0 ≤ (slowProfile N)^2 := sq_nonneg _
    unfold Sbound
    calc
      _ ≤ 4*width N (singular N) (Real.log N)*(slowProfile N)^2 := by
        nlinarith [mul_nonneg (sq_nonneg (width N (singular N) (Real.log N))) hm]
      _ ≤ _ := by
        unfold width deltaSq slowProfile
        field_simp
        nlinarith [mul_le_mul hs (show 4 ≤ Real.log N^2 by nlinarith [sq_nonneg (Real.log N-2)])
          (by norm_num : (0:ℝ) ≤ 4) hs'.le,
          mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ singular N*Real.log N^2 by positivity)]

end GoldbachSpectral

