module
public import Mathlib.NumberTheory.LSeries.WeakPNT

public section
open Filter
open scoped Topology
theorem spectral_band_prime_number_theorem :
    Tendsto (fun x : ℝ => Chebyshev.theta x/x) atTop (𝓝 1) :=
  Chebyshev.tendsto_theta_div_atTop

