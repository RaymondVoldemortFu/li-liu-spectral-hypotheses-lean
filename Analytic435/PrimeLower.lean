module
public import ActualLimits
public import Opposite
public import SpectralTests.PrimeProgression

@[expose] public section
open ConditionalGoldbach GoldbachSpectral
namespace GoldbachSpectral435

theorem shiftTransfer_original : ShiftTransfer eligibleNorm GRH := by
  obtain ⟨C,hC,estimate⟩ := actual_transfer
  obtain ⟨K,L⟩ := evenEventually_large
  refine ⟨C,hC,max K 1,fun N hn he g H P b test => ?_⟩
  have lar := L N ((le_max_left _ _).trans hn) he
  have ha := (large_parameters lar).2.2
  let : NeZero N := ⟨by omega⟩
  rw [eligibleNorm_spec N ha g]
  exact estimate N he lar g ha H P b test

theorem cofinal_prime_lower :
    ∃ c : ℝ, 0<c ∧ ∀ K : ℕ, ∃ N ≥ K, Even N ∧
      (GRH N → c*Real.log N^2 ≤ (N:ℝ)*(eligibleNorm N)^2) :=
  one_shift_lower shiftTransfer_original

#print axioms cofinal_prime_lower
end GoldbachSpectral435

