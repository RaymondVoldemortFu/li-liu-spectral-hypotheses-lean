module
public import SieveEuler
public import ConditionalGoldbach.Proofs.CharacterEulerBounds

/-! Reciprocal mass of prime divisors above the local cutoff for all shifts
with logarithm O(z log z). The cutoff can thus have size proportional to
the logarithm of the original modulus, even at its full spectral horizon. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset Filter
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open MathlibNt.SieveTheory.MertensTheorem

def largeFactors (H z : ℕ) := H.primeFactors.filter (fun p => z<p)

def reciprocalTail (H z : ℕ) : ℝ := ∑ p∈largeFactors H z, 1/(p:ℝ)

private lemma split_tail (H z : ℕ) (hp : 0<H) (zz : 2≤z) (d B : ℝ)
    (size : Real.log H≤B*z*Real.log z) :
    reciprocalTail H z≤weightedPrimeReciprocalLogSum (fun _ => 1) z 1 (1+d)+B/(z:ℝ)^d := by
  let P := largeFactors H z
  let X := (z:ℝ)^(1+d)
  let small := P.filter (fun p : ℕ => (p:ℝ)≤X)
  let large := P.filter (fun p : ℕ => ¬(p:ℝ)≤X)
  have zr : (1:ℝ)<z := by exact_mod_cast zz
  have zp := zero_lt_one.trans zr
  have lp := Real.log_pos zr
  have xp : 0<X := Real.rpow_pos_of_pos zp _
  have sub : small⊆(Ioc (rpowFloor z 1) (rpowFloor z (1+d))).filter Nat.Prime := by
    intro p mem
    obtain ⟨a,b⟩ := mem_filter.mp mem
    obtain ⟨c,gt⟩ := mem_filter.mp a
    apply mem_filter.mpr
    exact ⟨mem_Ioc_rpowFloor_iff.mpr ⟨by simpa using (show (z:ℝ)<p by exact_mod_cast gt),b⟩,
      Nat.prime_of_mem_primeFactors c⟩
  have first : (∑ p∈small, 1/(p:ℝ))≤weightedPrimeReciprocalLogSum (fun _ => 1) z 1 (1+d) :=
    sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => by positivity)
  have point (p : ℕ) (mem : p∈large) : (1/(p:ℝ))*(X*Real.log z)≤Real.log p := by
    obtain ⟨a,b⟩ := mem_filter.mp mem
    have gt := (mem_filter.mp a).2
    have pp : 0<(p:ℝ) := zp.trans (by exact_mod_cast gt)
    have le := Real.log_le_log zp (show (z:ℝ)≤p by exact_mod_cast gt.le)
    have s := mul_le_mul_of_nonneg_right (le_of_not_ge b) lp.le
    calc
      _ ≤ (1/(p:ℝ))*((p:ℝ)*Real.log z) := mul_le_mul_of_nonneg_left s (by positivity)
      _ = Real.log z := by field_simp
      _ ≤ _ := le
  have ls : large⊆H.primeFactors := fun p mem => (mem_filter.mp (mem_filter.mp mem).1).1
  have upper := (sum_le_sum point).trans ((sum_le_sum_of_subset_of_nonneg ls
    (fun p mem _ => Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors mem).one_le))).trans
    (sum_log_primeFactors_le_log H hp))
  rw [← sum_mul] at upper
  have second : (∑ p∈large, 1/(p:ℝ))≤B/(z:ℝ)^d := by
    apply le_of_mul_le_mul_right _ (mul_pos xp lp)
    apply (upper.trans size).trans_eq
    dsimp only [X]
    rw [Real.rpow_add zp,Real.rpow_one]
    field_simp
  have split := sum_filter_add_sum_filter_not P (fun p : ℕ => (p:ℝ)≤X) (fun p : ℕ => 1/(p:ℝ))
  change (∑ p∈P, 1/(p:ℝ))≤_
  rw [← split]
  exact add_le_add first second

/-- Uniformly in H, even when H is as large as exp(B z log z), the Euler
factors above z coming from prime divisors of H have vanishing reciprocal mass. -/
theorem uniform_reciprocal_tail (B ε : ℝ) (ep : 0<ε) :
    ∀ᶠ z : ℕ in atTop, ∀ H : ℕ, 0<H → Real.log H≤B*z*Real.log z → reciprocalTail H z≤ε := by
  let d := ε/4
  have dp : 0<d := by dsimp [d]; positivity
  have m := tendsto_weightedPrimeReciprocalLogSum_const (c:=(1:ℝ)) zero_lt_one (show (1:ℝ)<1+d by linarith)
  have mlim : Tendsto (fun z => weightedPrimeReciprocalLogSum (fun _ => 1) z 1 (1+d)) atTop (𝓝 (Real.log (1+d))) := by
    simpa only [div_one,one_mul] using m
  have ll : Real.log (1+d)≤d := by linarith only [Real.log_le_sub_one_of_pos (show 0<1+d by positivity)]
  have large : Tendsto (fun z : ℕ => (z:ℝ)^d) atTop atTop :=
    (tendsto_rpow_atTop dp).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have lim : Tendsto (fun z : ℕ => B/(z:ℝ)^d) atTop (𝓝 0) := tendsto_const_nhds.div_atTop large
  filter_upwards [eventually_ge_atTop (2:ℕ),mlim.eventually_lt_const (show Real.log (1+d)<ε/2 by dsimp [d] at ll; linarith),
    lim.eventually_lt_const (half_pos ep)] with z zz first second
  intro H hp h
  exact (split_tail H z hp zz d B h).trans (by linarith)

#print axioms uniform_reciprocal_tail
end GoldbachSpectral435.GoldbachSieve
