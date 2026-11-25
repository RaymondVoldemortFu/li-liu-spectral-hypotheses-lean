module
public import SpectralTests.Product
public import SpectralTests.Transfer
public import SpectralTests.Buchstab
public import SpectralTests.Record
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section
namespace GoldbachSpectral
open Set
open scoped Quaternion

/-- GRH(N) in Li–Liu §1.2, for primitive characters of positive conductor
dividing N. The primitive character of modulus one includes the zeta function. -/
def LocalGRH (N : ℕ) : Prop :=
  ∀ d : ℕ, ∀ [NeZero d], d ∣ N → ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1/2

def DirichletGRH : Prop :=
  ∀ d : ℕ, ∀ [NeZero d], ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1/2

theorem local_of_global (g : DirichletGRH) (N : ℕ) : LocalGRH N :=
  fun d _ _ χ h => g d χ h

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
    [∀ n, CompleteSpace (E n)]

noncomputable def Xof (T : ∀ n, E n →L[ℂ] E n) (N : ℕ) :=
  spectralX (T N) (deltaSq N (singular N))

/-- Only eventual eligible arithmetic moduli are relevant. -/
def CompactSymmetric (T : ∀ n, E n →L[ℂ] E n) : Prop :=
  ∃ K : ℕ, ∀ N ≥ K, Even N → LocalGRH N → IsCompactOperator (T N) ∧ (T N).IsSymmetric

theorem dictionary_of_spectrum {T : ∀ n, E n →L[ℂ] E n} (ht : CompactSymmetric T) :
    ZeroFreeImpliesBound (fun n => ‖T n‖) LocalGRH (Xof T) := by
  obtain ⟨K,H⟩ := ht
  refine ⟨max K 2,?_⟩
  intro n hn he hg η hη hη' no
  by_contra! large
  have hN : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hl := Real.log_pos hN
  have hs : 0 < singular n := lt_of_lt_of_le zero_lt_one (singular_lower n)
  have hd : 0 < deltaSq n (singular n) := by unfold deltaSq; positivity
  have hnrm : deltaSq n (singular n) < 4*η*(1-η)*‖T n‖^2 := lt_of_not_ge large
  obtain ⟨h₁,h₂⟩ := H n (by omega) he hg
  obtain ⟨r,hr,hx⟩ := real_zero_of_norm h₁ h₂ hd hη hη' hnrm
  have hi := no (r:ℍ[ℝ]) hx
  rw [Quaternion.re_coe] at hi
  exact (not_lt_of_ge hi) hr.1

/-- Given the two published analytic inputs, the obstructing zeros can be
chosen real and strictly below one. No spectral dictionary is assumed. -/
theorem real_zeros_of_growth {T : ∀ n, E n →L[ℂ] E n}
    (global : DirichletGRH) (ht : CompactSymmetric T)
    (growth : LiuInput (fun n => ‖T n‖) LocalGRH) (a K : ℕ) :
    ∃ n ≥ K, Even n ∧ LocalGRH n ∧ ∃ r : ℝ,
      1-logWidth a n < r ∧ r < 1 ∧ Xof T n (r:ℍ[ℝ])=0 := by
  obtain ⟨F,hF⟩ := ht
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp eventually_small_series
  obtain ⟨n,hn,he,lower⟩ := growth (a+6) (max (max (max K F) L) 2)
  have hn1 : 1 < n := by omega
  have hg := local_of_global global n
  obtain ⟨lpos,series⟩ := hL n (by omega)
  have hbad := logWidth_fails (a := a) (by omega : 0 < n) lpos series (lower hg)
  obtain ⟨compact,symm⟩ := hF n (by omega) he hg
  have hp : 1 ≤ Real.log n^a := one_le_pow₀ (by linarith)
  have hη : 0 < logWidth a n := by unfold logWidth; positivity
  have hη' : logWidth a n < 1/2 := by
    unfold logWidth
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hs : 0 < singular n := lt_of_lt_of_le zero_lt_one (singular_lower n)
  have hd : 0 < deltaSq n (singular n) := by unfold deltaSq; positivity
  obtain ⟨r,hr,hx⟩ := real_zero_of_norm compact symm hd hη hη' (lt_of_not_ge hbad)
  exact ⟨n,by omega,he,hg,r,hr.1,hr.2,hx⟩

theorem real_zeros_from_inputs {T : ∀ n, E n →L[ℂ] E n}
    (global : DirichletGRH) (ht : CompactSymmetric T)
    (entries : HardyEntries T LocalGRH) (bias : ShiftBias) (a K : ℕ) :
    ∃ n ≥ K, Even n ∧ LocalGRH n ∧ ∃ r : ℝ,
      1-logWidth a n < r ∧ r < 1 ∧ Xof T n (r:ℍ[ℝ])=0 :=
  real_zeros_of_growth global ht (growth_from_shifts bias (transfer_from_entries entries)) a K

theorem real_zeros_from_gain {T : ∀ n, E n →L[ℂ] E n}
    (global : DirichletGRH) (ht : CompactSymmetric T)
    (entries : HardyEntries T LocalGRH) (gain : CofinalShiftGain) (a K : ℕ) :
    ∃ n ≥ K, Even n ∧ LocalGRH n ∧ ∃ r : ℝ,
      1-logWidth a n < r ∧ r < 1 ∧ Xof T n (r:ℍ[ℝ])=0 :=
  real_zeros_of_growth global ht (growth_from_gain gain (transfer_from_entries entries)) a K

theorem spectral_conclusions {T : ∀ n, E n →L[ℂ] E n}
    (global : DirichletGRH) (ht : CompactSymmetric T)
    (entries : HardyEntries T LocalGRH) (bias : ShiftBias) :
    ¬ HypothesisR LocalGRH (Xof T) ∧
    (∀ a, ¬ HypothesisS LocalGRH (Xof T) (prescribedH a)) ∧
    (∀ (h : ℕ → ℝ) (a : ℕ),
      (∃ K : ℕ, ∀ N ≥ K, Even N → LocalGRH N → logWidth a N ≤ width N (singular N) (h N)) →
       ¬ HypothesisS LocalGRH (Xof T) h) := by
  have grh := fun N (_ : Even N) => local_of_global global N
  have growth := growth_from_shifts bias (transfer_from_entries entries)
  have dict := dictionary_of_spectrum ht
  have both := reject_R_and_wide_S growth grh dict
  exact ⟨both.1, prescribed_S_fails growth grh dict, both.2⟩

end GoldbachSpectral

