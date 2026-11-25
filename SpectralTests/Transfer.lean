module
public import SpectralTests.Shifts
public import SpectralTests.Window
public import SpectralTests.TestEnergy

@[expose] public section
namespace GoldbachSpectral
open Set MeasureTheory

/-- The two remaining Hardy-space inputs are the exact signed matrix entry and
the norm estimates from the Mellin functional. The latter are expressed after
the change of variables x=Nu for the narrow weight. -/
def HardyEntries {E : ℕ → Type*} [∀ N, NormedAddCommGroup (E N)]
    [∀ N, InnerProductSpace ℂ (E N)] (T : ∀ N, E N →L[ℂ] E N) (G : ℕ → Prop) : Prop :=
  ∃ A J : ℝ, 0 < A ∧ 0 < J ∧ ∃ K : ℕ, ∀ N ≥ K, Even N → G N → ∀ H P b,
    ShiftTest N H P b →
    Integrable (fun u => (b u/2-u*deriv b u)^2) ∧
    ∃ x y : E N, (inner ℂ x (T N y)).re = -(oppositeSum N b)/(N:ℝ) ∧
      ‖x‖^2 ≤ A * energy b / N ∧ ‖y‖^2 ≤ J

theorem transfer_from_entries {E : ℕ → Type*} [∀ N, NormedAddCommGroup (E N)]
    [∀ N, InnerProductSpace ℂ (E N)] {T : ∀ N, E N →L[ℂ] E N} {G : ℕ → Prop}
    (data : HardyEntries T G) : ShiftTransfer (fun N => ‖T N‖) G := by
  obtain ⟨A,J,hA,hJ,K,entries⟩ := data
  refine ⟨9*A*J,by positivity, max K 1, ?_⟩
  intro N hn he hg H P b test
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one test.one_le
  obtain ⟨hi,x,y,exactEntry,hx,hy⟩ := entries N (by omega) he hg H P b test
  have bound : |-(oppositeSum N b)/(N:ℝ)| ≤ ‖x‖*(‖T N‖*‖y‖) := calc
    _ = |(inner ℂ x (T N y)).re| := by rw [exactEntry]
    _ ≤ ‖inner ℂ x (T N y)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖*‖T N y‖ := norm_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left ((T N).le_opNorm _) (norm_nonneg _)
  rw [abs_div, abs_neg, abs_of_pos hN, div_le_iff₀ hN] at bound
  have bs := pow_le_pow_left₀ (abs_nonneg _) bound 2
  rw [sq_abs] at bs
  rw [le_div_iff₀ hN] at hx
  have xH : ‖x‖^2*(N:ℝ)*H ≤ A*(9*P^2) := calc
    _ ≤ A*energy b*H := mul_le_mul_of_nonneg_right hx hH.le
    _ = A*(energy b*H) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (shift_energy test hi) hA.le
  calc
    _ ≤ H*(‖x‖*(‖T N‖*‖y‖)*(N:ℝ))^2 := mul_le_mul_of_nonneg_left bs hH.le
    _ = (‖x‖^2*(N:ℝ)*H) * ‖y‖^2 * ((N:ℝ)*‖T N‖^2) := by ring
    _ ≤ (A*(9*P^2))*J*((N:ℝ)*‖T N‖^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul xH hy (sq_nonneg _) (by positivity)
    _ = _ := by ring

end GoldbachSpectral

