module
public import BandPNT
public import Mathlib.Data.Nat.Choose.Bounds
public import SpectralTests.BandSieve

@[expose] public section
namespace GoldbachSpectral.BandSieve
open Filter Chebyshev Finset
open scoped Topology

/-- An asymptotic consequence of the proved ordinary prime number theorem,
uniform over macroscopic intervals. There are no GRH assumptions. -/
theorem prime_mass_windows {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ X : ℝ, ∀ x ≥ X, ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ C*x →
      c*x ≤ b-a → (b-a)/2 ≤ theta b - theta a := by
  let ε := c/(4*C)
  have he : 0 < ε := div_pos hc (by positivity)
  obtain ⟨Y,hY⟩ := (Metric.tendsto_atTop.mp spectral_band_prime_number_theorem) ε he
  refine ⟨max Y 1,fun x hx a b ha hab hb hwidth => ?_⟩
  have hA : 0 < a := by grind
  have hB := hA.trans_le hab
  have err (y : ℝ) (hy : a ≤ y) : |theta y-y| ≤ ε*y := by
    have q := hY y (by grind)
    have eqn : theta y/y-1 = (theta y-y)/y := by rw [sub_div,div_self (hA.trans_le hy).ne']
    change dist (theta y/y) 1 < ε at q
    rw [Real.dist_eq, eqn, abs_div, abs_of_pos (hA.trans_le hy)] at q
    exact ((div_lt_iff₀ (hA.trans_le hy)).mp q).le
  obtain ⟨_,h₁⟩ := abs_le.mp (err a le_rfl)
  obtain ⟨h₂,_⟩ := abs_le.mp (err b hab)
  have e₁ := mul_le_mul_of_nonneg_left (hab.trans hb) he.le
  have e₂ := mul_le_mul_of_nonneg_left hb he.le
  have id : ε*(C*x) = c*x/4 := by dsimp [ε]; field_simp
  rw [id] at e₁ e₂
  linarith

/-- The actual dyadic band of prime divisors. -/
def bandPrimes (z : ℕ) := Nat.primesLE (2*z) \ Nat.primesLE z

theorem mem_band {z p : ℕ} : p ∈ bandPrimes z ↔ p.Prime ∧ z < p ∧ p ≤ 2*z := by
  simp only [bandPrimes,Finset.mem_sdiff,Nat.mem_primesLE]
  grind

theorem band_mass (z : ℕ) :
    ∑ p ∈ bandPrimes z, Real.log p = theta (2*z:ℕ) - theta (z:ℝ) := by
  have subset : Nat.primesLE z ⊆ Nat.primesLE (2*z) := by
    intro p hp
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨by omega,prime⟩
  rw [theta_eq_sum_primesLE_log,theta_eq_sum_primesLE_log,eq_sub_iff_add_eq]
  exact Finset.sum_sdiff subset

theorem band_population :
    ∃ Z : ℕ, ∀ z ≥ Z, (z:ℝ)/2 ≤ ((bandPrimes z).card:ℝ)*Real.log (2*z) := by
  obtain ⟨X,H⟩ := prime_mass_windows (c := 1) (C := 2) (by norm_num) (by norm_num)
  obtain ⟨Z,hZ⟩ := exists_nat_gt X
  refine ⟨Z,fun z hz => ?_⟩
  have h := H z (hZ.le.trans (by exact_mod_cast hz)) z (2*z) le_rfl (by linarith [Nat.cast_nonneg (α := ℝ) z]) le_rfl (by linarith)
  have eqn := band_mass z
  push_cast at eqn
  rw [← eqn] at h
  have upper := Finset.sum_le_sum (s := bandPrimes z) (f := fun p : ℕ => Real.log p)
    (g := fun _ => Real.log (2*(z:ℝ))) (fun p hp => Real.log_le_log
      (by exact_mod_cast (mem_band.mp hp).1.pos) (by exact_mod_cast (mem_band.mp hp).2.2))
  simp only [sum_const,nsmul_eq_mul] at upper
  linarith

/-- Each k-element subset yields a separate contribution, even when the
integer counted for one subset is also counted for another. -/
theorem layer_population {z k : ℕ} (hz : 0 < z) (many : 2*k ≤ (bandPrimes z).card)
    (mass : (z:ℝ)/2 ≤ ((bandPrimes z).card:ℝ)*Real.log (2*z)) :
    ((z:ℝ)/(4*Real.log (2*z)))^k / k.factorial ≤ ((bandPrimes z).powersetCard k).card := by
  have lg : 0 < Real.log (2*(z:ℝ)) := Real.log_pos (by exact_mod_cast (show 1<2*z by omega))
  have hsub : (bandPrimes z).card ≤ 2*((bandPrimes z).card+1-k) := by omega
  have hs : ((bandPrimes z).card:ℝ) ≤ 2*(((bandPrimes z).card+1-k:ℕ):ℝ) := by exact_mod_cast hsub
  have lower : (z:ℝ)/(4*Real.log (2*z)) ≤ (((bandPrimes z).card+1-k:ℕ):ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [mass,mul_le_mul_of_nonneg_right hs lg.le]
  rw [Finset.card_powersetCard]
  apply le_trans _ (Nat.pow_le_choose (α := ℝ) k (bandPrimes z).card)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) lower k) (Nat.cast_nonneg _)

end GoldbachSpectral.BandSieve
