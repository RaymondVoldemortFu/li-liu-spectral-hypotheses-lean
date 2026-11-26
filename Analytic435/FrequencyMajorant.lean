module
public import PrimeLineFrequencies
public import GoldbachSmoothTests

/-! A smooth positive envelope for the integrand of the exact prime line. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset MeasureTheory
namespace GoldbachSpectral435.GoldbachSieve
open FirstLineLimits

theorem positive_envelope (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ F : ℝ→ℝ, Nonempty (FiniteModelWeight F) ∧ ∀ x, |f x|≤F x := by
  let d := min hf.lower (1-hf.upper)/4
  have dp : 0<d := div_pos (lt_min hf.lower_pos (sub_pos.mpr hf.upper_lt_one)) (by norm_num)
  have lo : 2*d≤hf.lower := by dsimp [d]; linarith [hf.lower_pos,min_le_left hf.lower (1-hf.upper)]
  have hi : hf.upper≤1-2*d := by dsimp [d]; linarith [min_le_right hf.lower (1-hf.upper),hf.upper_lt_one]
  obtain ⟨B,hB⟩ := hf.norm_bounded
  let F := fun u => |B| *cutoff d u
  have ends := hf.lower_le_upper
  refine ⟨F,⟨⟨contDiff_const.mul (cutoff_smooth d),d,1-d,dp,by linarith,by linarith,?_⟩⟩,?_⟩
  · intro x h
    apply cutoff_support dp
    intro z
    exact h (by simp [F,z])
  · intro x
    by_cases z : f x=0
    · simp only [z,abs_zero,F]
      exact mul_nonneg (abs_nonneg _) (cutoff_limits d x).1
    · have h := hf.mem_support_interval z
      rw [show F x=|B| from by dsimp [F]; rw [cutoff_one dp (lo.trans h.1) (h.2.trans hi),mul_one]]
      exact (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hB x : |f x|≤B).trans (le_abs_self _)

private lemma sifted_abs (q M : ℕ) (f F : ℝ→ℝ) (h : ∀ x, |f x|≤F x) (n : ℕ) :
    |siftedWeight q M f n|≤siftedWeight q M F n := by
  unfold siftedWeight
  split
  · rw [weightedMangoldt,weightedMangoldt,abs_mul,abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
    exact mul_le_mul_of_nonneg_left (h _) ArithmeticFunction.vonMangoldt_nonneg
  · simp

theorem prime_frequency_majorant (q M H : ℕ) [NeZero q] (sign : Bool) (f g F G : ℝ→ℝ)
    (hf : ∀ x, |f x|≤F x) (hg : ∀ x, |g x|≤G x) (t : ℝ) :
    |frequencySlice q M H sign (siftedWeight q M f) (siftedWeight q M g) t|≤classPairs q H M M sign F G := by
  rw [class_pairs_lines]
  unfold frequencySlice lineSum
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro n _
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro m _
  unfold frequencyTerm
  split
  · rw [abs_mul,abs_mul]
    have fn := sifted_abs q M f F hf n
    have gm := sifted_abs q M g G hg m
    have v := mul_le_mul fn gm (abs_nonneg _) ((abs_nonneg _).trans fn)
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
      (by simpa using v)
  · simp

#print axioms positive_envelope
#print axioms prime_frequency_majorant
end GoldbachSpectral435.GoldbachSieve
