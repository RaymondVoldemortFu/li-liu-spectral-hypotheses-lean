module
public import PrimeNumberTheoremAnd.Consequences

public section
open Filter Asymptotics
open scoped Topology
theorem spectral_band_prime_number_theorem :
    Tendsto (fun x : ℝ => Chebyshev.theta x/x) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one ?_).mp chebyshev_asymptotic
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using hx.ne'
#print axioms spectral_band_prime_number_theorem

