module
public import SpectralTests
import Lean.Util.CollectAxioms

@[expose] public section
namespace GoldbachSpectral.Audit
open scoped Quaternion

/-- Independent spelling of the real slice of the spectral product, including
algebraic multiplicities (equal to geometric multiplicities for self-adjoint T). -/
noncomputable def realSlice {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (D x : ℝ) : ℂ :=
  ∏' j : (μ : {r : ℝ // r ≠ 0}) ×
      Fin (Module.finrank ℂ (Module.End.eigenspace T.toLinearMap (μ.val:ℂ))),
    (1 - ((4*j.1.val^2/D:ℝ):ℂ)*(x:ℂ)*(1-(x:ℂ)))

theorem as_printed {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    {T : ∀ n, H n →L[ℂ] H n} (g : DirichletGRH) (compact : CompactSymmetric T)
    (entry : HardyEntries T LocalGRH) (arithmetic : ShiftBias) :
    ∀ a K : ℕ, ∃ n ≥ K, Even n ∧ LocalGRH n ∧ ∃ r : ℝ,
      1 - 1/(4*Real.log n^a) < r ∧ r < 1 ∧
      realSlice (T n) (singular n*Real.log n^3/n) r = 0 := by
  intro a K
  obtain ⟨n,hn,he,hg,r,lo,hi,hx⟩ := real_zeros_from_inputs g compact entry arithmetic a K
  refine ⟨n,hn,he,hg,r,lo,hi,?_⟩
  have hp := congrArg QuaternionAlgebra.re hx
  change (spectralX (T n) (deltaSq n (singular n)) (r:ℍ[ℝ])).re = 0 at hp
  simp only [spectralX, Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe,
    Quaternion.imK_coe, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_add, Real.sqrt_zero] at hp
  have realpart : (realSlice (T n) (deltaSq n (singular n)) r).re = 0 := hp
  have conjfixed : star (realSlice (T n) (deltaSq n (singular n)) r) =
      realSlice (T n) (deltaSq n (singular n)) r := by
    let f := fun j : Mode (T n) => (1-((4*j.1.val^2/deltaSq n (singular n):ℝ):ℂ)*
      (r:ℂ)*(1-(r:ℂ)))
    change (starRingEnd ℂ) (∏' j, f j) = ∏' j, f j
    by_cases h : Multipliable f
    · rw [h.map_tprod (starRingEnd ℂ) continuous_star]
      have four : (starRingEnd ℂ) (4:ℂ) = 4 := map_ofNat _ _
      simp [f, four]
    · rw [tprod_eq_one_of_not_multipliable h, map_one]
  change realSlice (T n) (deltaSq n (singular n)) r = 0
  apply Complex.ext realpart
  have him := congrArg Complex.im conjfixed
  simp at him
  change _ = 0
  linarith

#print axioms arithmetic_obstruction
#print axioms arithmetic_real_zeros
#print axioms as_printed
#print axioms spectral_conclusions
#print axioms gap_cube
#print axioms checked_window

open Lean Elab Command in
elab "audit_spectral_axioms" : command => do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``unconditional_shift, ``arithmetic_one_shift, ``arithmetic_obstruction, ``arithmetic_real_zeros, ``arithmetic_prescribed, ``as_printed, ``spectral_conclusions, ``prescribed_admissible, ``slow_compatibility,
               ``buchstab_drop, ``beta_samples_cancel, ``gap_cube, ``window_thresholds,
               ``factorial_window, ``checked_window, ``separated_spectrum,
               ``BandSieve.inclusion_exclusion, ``BandSieve.extra_layer, ``BandSieve.residue_discrepancy, ``BandSieve.weighted_discrepancy, ``BandSieve.prime_mass_windows, ``BandSieve.layer_population, ``BandSieve.signed_matrix_lower, ``BandSieve.transpose, ``BandSieve.row_tests, ``BandSieve.growing_rows, ``BandSieve.wheel_small, ``residue_row_witness, ``reflectedBeta_mass, ``reflectedBeta_support, ``real_zeros_from_gain, ``some_width_iff_decay] do
    for ax in (← liftCoreM (Lean.collectAxioms decl)) do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {decl}"

audit_spectral_axioms
end GoldbachSpectral.Audit

