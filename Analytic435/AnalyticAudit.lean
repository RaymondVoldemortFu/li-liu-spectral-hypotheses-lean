module
public import ActualLimits
public import BetaSampling
public import Characters
public import Kernel
public import Residues
public import Progressions
public import BetaCross
public import Diagonal
public import Quadratic
public import Samples
public import Gram
public import Entry
public import Energy
public import SpectralTests.RowShape
public import PhysicalAP
public import FiniteSamples
public import SparsePrescriptions
public import ShortShiftLimit
import Lean.Util.CollectAxioms

public section
open Lean Elab Command in
elab "audit_actual_spectral_results" : command => do
  let allowed := [``propext,``Classical.choice,``Quot.sound]
  for decl in [
      ``GoldbachSpectral435.some_actual_S_iff,
      ``GoldbachSpectral435.half_double_sampling,
      ``GoldbachSpectral435.smooth_character_bound,
      ``GoldbachSpectral435.mixed_kernel_norms,
      ``GoldbachSpectral435.broad_projection,
      ``GoldbachSpectral435.smooth_class_bound,
      ``GoldbachSpectral435.character_gram,
      ``GoldbachSpectral435.half_cross_vanish,
      ``GoldbachSpectral435.diagonal_test,
      ``GoldbachSpectral435.doubled_quadratic,
      ``GoldbachSpectral435.testVector_add,
      ``GoldbachSpectral435.diagonal_separated,
      ``GoldbachSpectral435.projected_shifts,
      ``GoldbachSpectral.BandSieve.rounded_weight,
      ``GoldbachSpectral.BandSieve.layer_population,
      ``GoldbachSpectral435.opposite_entry_bound,
      ``GoldbachSpectral435.norm_at_double_le,
      ``GoldbachSpectral435.physical_rescale,
      ``GoldbachSpectral435.actual_transfer,
      ``GoldbachSpectral435.cofinal_prime_lower,
      ``GoldbachSpectral435.physical_AP,
      ``GoldbachSpectral435.R_forces_shifts,
      ``GoldbachSpectral435.S_forces_shifts,
      ``GoldbachSpectral.BandSieve.signed_matrix_lower,
      ``GoldbachSpectral.BandSieve.transpose,
      ``GoldbachSpectral.BandSieve.row_tests,
      ``GoldbachSpectral.BandSieve.sample_data,
      ``GoldbachSpectral.BandSieve.variation_bound,
      ``GoldbachSpectral.BandSieve.growing_rows,
      ``GoldbachSpectral435.principal_lower,
      ``GoldbachSpectral435.shifted_estimate,
      ``GoldbachSpectral435.mean_lower,
      ``GoldbachSpectral435.large_shift,
      ``GoldbachSpectral435.cofinal_growth,
      ``GoldbachSpectral435.refute_R,
      ``GoldbachSpectral435.refute_S,
      ``GoldbachSpectral435.prescribed_failure,
      ``GoldbachSpectral435.all_local_of_primitive,
      ``GoldbachSpectral435.norm_lower_on_original,
      ``GoldbachSpectral435.cofinal_original_zeros,
      ``GoldbachSpectral435.primitive_GRH_spectral_consequences,
      ``GoldbachSpectral435.common_zero_sequence,
      ``GoldbachSpectral435.guaranteed_width_and_log_gap,
      ``GoldbachSpectral435.no_admissible_S_iff,
      ``GoldbachSpectral435.arbitrarily_large_test,
      ``GoldbachSpectral435.arithmeticH_admissible,
      ``GoldbachSpectral435.arithmetic_width_decay,
      ``GoldbachSpectral435.arithmetic_width_refuted,
      ``GoldbachSpectral435.paper_GRH_iff,
      ``GoldbachSpectral435.paper_spectral_consequences,
      ``GoldbachSpectral435.sampleBound_iff_norm,
      ``GoldbachSpectral435.prescribed_S_iff_samples,
      ``GoldbachSpectral435.log_S_iff_samples,
      ``GoldbachSpectral435.no_S_iff_finite_obstructions,
      ``GoldbachSpectral435.record_exclusions_fail,
      ``GoldbachSpectral435.patched_eq_off,
      ``GoldbachSpectral435.sparse_failure,
      ``GoldbachSpectral435.sparse_count,
      ``GoldbachSpectral435.sparse_log_decay,
      ``GoldbachSpectral435.sparse_log_failure,
      ``GoldbachSpectral435.opposite_size,
      ``GoldbachSpectral435.shift_log_scale_cap,
      ``GoldbachSpectral435.short_shifts_below_log_scale] do
    for ax in (← liftCoreM (Lean.collectAxioms decl)) do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {decl}"
audit_actual_spectral_results

