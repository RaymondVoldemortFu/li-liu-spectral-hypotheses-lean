module
public import SieveDenominator
public import OriginalBounds
public import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-! Uniform local products for the binary Goldbach upper sieve. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset
namespace GoldbachSpectral435.GoldbachSieve

def smallPrimes (z : ℕ) := (range (z+1)).filter Nat.Prime

private def correction (p : ℕ) : ℝ := ((p:ℝ)-1)/((p:ℝ)-2)

private def twoFactor (p : ℕ) : ℝ := if p=2 then 2 else 1

private def divisorFactor (N p : ℕ) : ℝ := if 2<p ∧ p∣N then correction p else 1

private lemma correction_ge {p : ℕ} (h : 2<p) : 1≤correction p := by
  have pr : 2<(p:ℝ) := by exact_mod_cast h
  exact (one_le_div (by linarith)).mpr (by linarith)

private lemma factor_le (N p : ℕ) (even : Even N) (hp : p.Prime) :
    1-localDensity N p≤(1-1/(p:ℝ))^2*(twoFactor p*divisorFactor N p) := by
  have pp : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  by_cases two : p=2
  · subst p
    have dv := even_iff_two_dvd.mp even
    norm_num [localDensity,twoFactor,divisorFactor,dv]
  have more : 2<p := by have := hp.two_le; omega
  have m : (2:ℝ)<p := by exact_mod_cast more
  have nz : (p:ℝ)≠0 := by positivity
  by_cases dvd : p∣N
  · simp only [localDensity,twoFactor,divisorFactor,more,dvd,two,ite_true,ite_false,true_and,one_mul,correction]
    field_simp
    nlinarith
  · simp only [localDensity,twoFactor,divisorFactor,more,dvd,two,ite_false,and_false,mul_one]
    nlinarith [sq_nonneg (1/(p:ℝ)),show 2/(p:ℝ)=2*(1/(p:ℝ)) by ring]

private lemma divisor_product (N z : ℕ) (np : 0<N) :
    (∏ p∈smallPrimes z, divisorFactor N p)≤singularSeries N := by
  classical
  let Q := (smallPrimes z).filter (fun p => 2<p ∧ p∣N)
  let A := N.primeFactors.filter (2<·)
  have sub : Q⊆A := by
    intro p h
    obtain ⟨hm,gt,dv⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hm).2,dv,np.ne'⟩,gt⟩
  have cmp : (∏ p∈Q, correction p)≤∏ p∈A, correction p :=
    prod_le_prod_of_subset_of_one_le₀ sub (fun p h => zero_le_one.trans (correction_ge (mem_filter.mp (sub h)).2))
      (fun p h _ => correction_ge (mem_filter.mp h).2)
  have nonneg : 0≤∏ p∈A, correction p := prod_nonneg (fun p h => zero_le_one.trans (correction_ge (mem_filter.mp h).2))
  have twin := GoldbachSpectral.twin_convergence.2
  have htw : 1≤2*∏' n, GoldbachSpectral.twinFactor n := by linarith
  unfold divisorFactor
  rw [← prod_filter,original_series]
  exact cmp.trans (le_mul_of_one_le_left nonneg htw)

theorem product_upper (N z : ℕ) (np : 0<N) (ev : Even N) (zz : 2≤z) :
    (∏ p∈smallPrimes z, (1-localDensity N p)) ≤
      2*singularSeries N*(MathlibNt.SieveTheory.MertensTheorem.primeProduct z)^2 := by
  classical
  let P := smallPrimes z
  have pr (p : ℕ) (hp : p∈P) := (mem_filter.mp hp).2
  have lower (p : ℕ) (hp : p∈P) : 0≤1-localDensity N p := (sub_pos.mpr (density_range N p ev (pr p hp)).2).le
  have compare := prod_le_prod₀ lower (fun p hp => factor_le N p ev (pr p hp))
  have tw : (∏ p∈P, twoFactor p)=2 := by
    have h : 2∈P := mem_filter.mpr ⟨mem_range.mpr (by omega),Nat.prime_two⟩
    simp [twoFactor,Finset.prod_ite_eq',h]
  have pp : (∏ p∈P, (1-1/(p:ℝ)))=MathlibNt.SieveTheory.MertensTheorem.primeProduct z := rfl
  apply compare.trans
  rw [prod_mul_distrib,prod_mul_distrib,tw,prod_pow,pp]
  calc
    _ ≤ (MathlibNt.SieveTheory.MertensTheorem.primeProduct z)^2*(2*singularSeries N) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (divisor_product N z np) (by norm_num)
    _ = _ := by ring

/-- The dimension-two Euler product is uniformly bounded by the original
singular series divided by the square of the logarithm of the sieve cutoff. -/
theorem uniform_product :
    ∃ C : ℝ, 0<C ∧ ∀ N z : ℕ, 0<N → Even N → 2≤z →
      (∏ p∈smallPrimes z, (1-localDensity N p))≤C*singularSeries N/(Real.log z)^2 := by
  obtain ⟨c,B,cp,estimate⟩ := MathlibNt.SieveTheory.MertensTheorem.primeProduct_asymptotic_order
  refine ⟨2*(|B|+1)^2,by positivity,?_⟩
  intro N z np e zz
  have l : 0<Real.log z := Real.log_pos (by exact_mod_cast (show 1<z by omega))
  have ss := singularSeries_pos N
  obtain ⟨lo,hi⟩ := estimate z zz
  have pos := (div_pos cp l).le.trans lo
  have be : B≤|B|+1 := (le_abs_self B).trans (by linarith)
  have bound := hi.trans (div_le_div_of_nonneg_right be l.le)
  apply (product_upper N z np e zz).trans
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ pos bound 2) (show 0≤2*singularSeries N by positivity)).trans_eq
  ring

#print axioms uniform_product
end GoldbachSpectral435.GoldbachSieve
