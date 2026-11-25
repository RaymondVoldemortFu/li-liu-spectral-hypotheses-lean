module
public import SpectralTests.Obstruction
public import SpectralTests.ShiftDefinitions
public import SpectralTests.Arithmetic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section
namespace GoldbachSpectral
open Set ArithmeticFunction
open scoped ContDiff Quaternion

/-- An arithmetic input with no spectral quantities. The constants and the test
may depend on the desired power. This is the cofinal progression-average output
in Section 3 of Y. Liu, including its choice H=z^u, P=zH. -/
def ShiftBias : Prop :=
  ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 < A → ∀ K : ℕ,
    ∃ N ≥ K, Even N ∧ ∃ H P b, ShiftTest N H P b ∧
      c*H ≤ oppositeSum N b ∧ A * Real.log N^d * P^2 < H^3

theorem growth_from_shifts {M : ℕ → ℝ} {G : ℕ → Prop} (bias : ShiftBias)
    (transfer : ShiftTransfer M G) : LiuInput M G := by
  obtain ⟨C,hC,K₁,transfer⟩ := transfer
  intro d K
  obtain ⟨c,hc,bias⟩ := bias d
  obtain ⟨N,hN,he,H,P,b,test,hB,hsize⟩ := bias (C/c^2) (by positivity) (max K K₁)
  refine ⟨N,by omega,he,fun hg => ?_⟩
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one test.one_le
  have hP : 0 < P := lt_of_lt_of_le hH test.width_le
  have sqB := pow_le_pow_left₀ (mul_nonneg hc.le hH.le) hB 2
  have lower := mul_le_mul_of_nonneg_left sqB hH.le
  have upper := transfer N (by omega) he hg H P b test
  field_simp at hsize
  apply (mul_lt_mul_iff_of_pos_right (show 0 < C*P^2 by positivity)).mp
  nlinarith [hsize,lower,upper]

/-- Cofinal signed-shift energy at the scale needed to test an arbitrary
fixed logarithmic power. It allows the arithmetic bias to lose log-log factors. -/
def CofinalShiftGain : Prop :=
  ∀ d : ℕ, ∀ C : ℝ, 0 < C → ∀ K : ℕ, ∃ N ≥ K, Even N ∧ ∃ H P b,
    ShiftTest N H P b ∧ C*P^2*Real.log N^d < H*(oppositeSum N b)^2

theorem growth_from_gain {M : ℕ → ℝ} {G : ℕ → Prop}
    (gain : CofinalShiftGain) (tr : ShiftTransfer M G) : LiuInput M G := by
  obtain ⟨C,hC,F,tr⟩ := tr
  intro d K
  obtain ⟨n,hn,even,H,P,b,test,large⟩ := gain d C hC (max K F)
  refine ⟨n,by omega,even,fun g => ?_⟩
  have pp := test.one_le.trans test.width_le
  have hp : 0 < P := by linarith
  have positive : 0 < C*P^2 := mul_pos hC (sq_pos_of_pos hp)
  apply (mul_lt_mul_iff_right₀ positive).mp
  have h := large.trans_le (tr n (by omega) even g H P b test)
  linarith only [h, show C*P^2*n*M n^2 = C*P^2*((n:ℝ)*M n^2) by ring]

/-- The pointwise cancellation behind the sampled continuous Beta model.
All three terms use the zero extensions of the test functions. -/
theorem beta_samples_cancel {f g : ℝ → ℝ}
    (hf : ∀ u, f u ≠ 0 → u ∈ Ioo (0:ℝ) (1/10))
    (hg : ∀ u, g u ≠ 0 → u ∈ Ioo (4/5:ℝ) (6/5))
    (flat : ∀ u ∈ Icc (9/10:ℝ) (11/10), g u = 1)
    (k : ℕ) (hk : 1 ≤ k) (u : ℝ) (hu : 0 ≤ u) :
    f u*g (u+k) + g u*f (u+k) - f u*g (k-u) = 0 := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hz : f (u+k) = 0 := by
    by_contra hn
    have hh := (hf _ hn).2
    linarith
  rw [hz, mul_zero, add_zero]
  by_cases hfu : f u = 0
  · rw [hfu]; ring
  obtain ⟨h0,h1⟩ := hf u hfu
  by_cases hke : k = 1
  · subst k
    rw [flat _ ⟨by norm_num; linarith, by norm_num; linarith⟩,
        flat _ ⟨by norm_num; linarith, by norm_num; linarith⟩, sub_self]
  · have hk2 : (2:ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have outside (x : ℝ) (hx : 6/5 ≤ x) : g x = 0 := by
      by_contra h
      exact (not_lt_of_ge hx) (hg _ h).2
    rw [outside _ (by linarith), outside _ (by linarith), sub_self]

theorem zero_obstruction_from_shifts {M : ℕ → ℝ} {G : ℕ → Prop} {X : ℕ → ℍ[ℝ] → ℍ[ℝ]}
    (bias : ShiftBias) (transfer : ShiftTransfer M G)
    (grh : ∀ N, Even N → G N) (dictionary : ZeroFreeImpliesBound M G X) :
    ¬ HypothesisR G X ∧ ∀ (h : ℕ → ℝ) (a : ℕ),
      (∃ K : ℕ, ∀ N ≥ K, Even N → G N → logWidth a N ≤ width N (singular N) (h N)) →
        ¬ HypothesisS G X h :=
  reject_R_and_wide_S (growth_from_shifts bias transfer) grh dictionary

end GoldbachSpectral

