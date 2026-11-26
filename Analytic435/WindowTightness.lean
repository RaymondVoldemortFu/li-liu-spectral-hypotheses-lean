module
public import GoldbachUpper
public import GoldbachPrimitive
public import ConditionalGoldbach.Proofs.PrimePowers
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-! Uniform interval bounds for the original weighted Goldbach counting
measure, with an error tending to zero after division by N. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset MeasureTheory Filter
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve

/-- A choice of the sieve cutoff depending only on the even modulus gives
a square-root additive error, uniformly in the endpoints of the interval. -/
theorem prime_window :
    ∃ C : ℝ, 0<C ∧ ∀ N A Y : ℕ, 2^64≤N → Even N → A+Y≤N+1 →
      (Real.log N)^2*primePairs N A Y≤ C*Y*singularSeries N+6*Real.sqrt N*(Real.log N)^2 := by
  obtain ⟨C,cp,estimate⟩ := prime_pairs_upper
  refine ⟨128^2*C,by positivity,?_⟩
  intro N A Y big even inc
  let z := Nat.nthRoot 64 N
  have zz : 2≤z := (Nat.le_nthRoot_iff (by decide : 64≠0)).mpr big
  have np : 0<N := by omega
  have sp := singularSeries_pos N
  have zp : 0<(z:ℝ) := by exact_mod_cast (show 0<z by omega)
  have lower : z^64≤N := Nat.pow_nthRoot_le (Or.inl (by decide : 64≠0))
  have upper : N<z^128 := by
    have m : z+1≤z^2 := by nlinarith [Nat.mul_le_mul_right z zz]
    have p := Nat.pow_le_pow_left m 64
    rw [← pow_mul] at p
    exact (Nat.lt_pow_nthRoot_add_one (by decide : 64≠0) N).trans_le p
  have logz : 0<Real.log z := Real.log_pos (by exact_mod_cast (show 1<z by omega))
  have logn := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast np)
  have logs : Real.log N≤128*Real.log z := by
    have h := Real.log_le_log (by exact_mod_cast np : 0<(N:ℝ)) (show (N:ℝ)≤(z:ℝ)^128 by exact_mod_cast upper.le)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have ls := pow_le_pow_left₀ logn logs 2
  have e : ((z^8:ℕ):ℝ)^4≤Real.sqrt N := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr
    push_cast
    rw [← pow_mul,← pow_mul]
    exact_mod_cast lower
  have zle : (z:ℝ)≤Real.sqrt N := by
    apply le_trans _ e
    push_cast
    rw [← pow_mul]
    simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ)≤z by exact_mod_cast (show 1≤z by omega))
      (by decide : 1≤8*4)
  have one : 1≤Real.sqrt (N:ℝ) := (by exact_mod_cast (show 1≤z by omega) : (1:ℝ)≤z).trans zle
  have h := estimate N z (z^8) A Y np even zz le_rfl inc
  have main : (Real.log N)^2*(C*Y*singularSeries N/(Real.log z)^2)≤128^2*C*Y*singularSeries N := by
    have rr := mul_le_mul_of_nonneg_right ls (show 0≤C*Y*singularSeries N/(Real.log z)^2 by positivity)
    apply rr.trans_eq
    field_simp
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans
  have er : 2*((z^8:ℕ):ℝ)^4+2*((z:ℝ)+1)≤6*Real.sqrt N := by linarith only [e,zle,one]
  nlinarith only [main,mul_le_mul_of_nonneg_left er (sq_nonneg (Real.log N))]

private def bad (n : ℕ) : ℝ := if ¬n.Prime then mangoldt n else 0

private lemma bad_nonneg (n : ℕ) : 0≤bad n := by
  unfold bad
  split_ifs <;> first | exact ArithmeticFunction.vonMangoldt_nonneg | rfl

/-- The von Mangoldt pair mass in any translated interval. Neither the
origin of the interval nor its length affects the absolute constants. -/
theorem mangoldt_window :
    ∃ C : ℝ, 0<C ∧ ∀ N A Y : ℕ, 2^64≤N → Even N → A+Y≤N+1 →
      (∑ n∈Ico A (A+Y), mangoldt n*mangoldt (N-n))≤
        C*(Y*singularSeries N+Real.sqrt N*(Real.log N)^2) := by
  obtain ⟨C,cp,primes⟩ := prime_window
  obtain ⟨B,rem⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C+6+2*|B|,by positivity,?_⟩
  intro N A Y big even inc
  let I := Ico A (A+Y)
  let L := Real.log (N:ℝ)
  have np : 0<N := by omega
  have l : 1≤L := by
    have h : (Real.exp 1)<(N:ℝ) := Real.exp_one_lt_three.trans_le (by exact_mod_cast (show 3≤N by omega))
    exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast np : 0<(N:ℝ))).mpr h).le
  have lm : 0≤L := zero_le_one.trans l
  have all : I⊆range (N+1) := fun n h => mem_range.mpr ((mem_Ico.mp h).2.trans_le inc)
  have point (n : ℕ) (hn : n∈I) : mangoldt n*mangoldt (N-n)≤
      L^2*(if n.Prime ∧ (N-n).Prime then (1:ℝ) else 0)+L*(bad n+bad (N-n)) := by
    have a : mangoldt n≤L := mangoldt_le_log_of_le np (by have := mem_range.mp (all hn); omega)
    have b : mangoldt (N-n)≤L := mangoldt_le_log_of_le np (Nat.sub_le ..)
    have an : 0≤mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have bn : 0≤mangoldt (N-n) := ArithmeticFunction.vonMangoldt_nonneg
    by_cases p : n.Prime <;> by_cases q : (N-n).Prime
    · simp [p,q,bad,sq]; exact mul_le_mul a b bn lm
    · simp [p,q,bad]; exact mul_le_mul_of_nonneg_right a bn
    · simp [p,q,bad]; exact (mul_le_mul_of_nonneg_left b an).trans_eq (mul_comm _ _)
    · simp [p,q,bad]
      nlinarith only [mul_le_mul_of_nonneg_right a bn,mul_nonneg lm an]
  have complete : (∑ n∈range (N+1), bad n)=Chebyshev.psi N-Chebyshev.theta N := sum_nonprime_mangoldt_eq_psi_sub_theta N
  have back : (∑ n∈range (N+1), bad (N-n))=∑ n∈range (N+1), bad n := by
    simpa using sum_range_reflect bad (N+1)
  have left := sum_le_sum_of_subset_of_nonneg all (fun n _ _ => bad_nonneg n)
  have right := sum_le_sum_of_subset_of_nonneg all (fun n _ _ => bad_nonneg (N-n))
  rw [back] at right
  rw [complete] at left right
  have powcap := (rem (N:ℝ)).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.sqrt_nonneg _))
  have bads := mul_le_mul_of_nonneg_left (add_le_add (left.trans powcap) (right.trans powcap)) lm
  have primes' := primes N A Y big even inc
  change L^2*(∑ n∈I, if n.Prime ∧ (N-n).Prime then (1:ℝ) else 0)≤C*Y*singularSeries N+6*Real.sqrt N*L^2 at primes'
  change (∑ n∈I, mangoldt n*mangoldt (N-n))≤_
  apply (sum_le_sum point).trans
  simp_rw [sum_add_distrib,← mul_sum]
  rw [sum_add_distrib]
  have hL : L≤L^2 := by nlinarith only [mul_le_mul_of_nonneg_left l lm]
  have ss := singularSeries_pos N
  have y : 0≤(Y:ℝ)*singularSeries N := by positivity
  have err : 0≤Real.sqrt (N:ℝ)*L^2 := by positivity
  have fac := mul_le_mul_of_nonneg_left hL (show 0≤2*|B| * Real.sqrt (N:ℝ) by positivity)
  change _≤(C+6+2*|B|)*((Y:ℝ)*singularSeries N+Real.sqrt N*L^2)
  nlinarith only [primes',bads,fac,mul_nonneg (show 0≤6+2*|B| by positivity) y,mul_nonneg cp.le err]

#print axioms prime_window
#print axioms mangoldt_window
end GoldbachSpectral435.GoldbachSieve
