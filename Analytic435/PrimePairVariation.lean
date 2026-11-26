module
public import PrimePairLogLoss
public import GoldbachIntervals

/-! Total variation distance between the original Goldbach atomic measure
and the counting measure on ordered pairs of primes, after normalization. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset
namespace GoldbachSpectral435.GoldbachSieve
open GoldbachPrimitive

def rawMass (N n : ℕ) : ℝ := if n.Coprime N then mangoldt n*mangoldt (N-n) else 0

private def powerPart (n : ℕ) : ℝ := if n.Prime then 0 else mangoldt n

private def loss (N n : ℕ) := pairIndicator N n*(Real.log N-Real.log n)

private lemma power_nonneg (n : ℕ) : 0≤powerPart n := by
  unfold powerPart
  split <;> first | rfl | exact ArithmeticFunction.vonMangoldt_nonneg

private lemma mirror_loss (N n : ℕ) (hn : n≤N) :
    loss N (N-n)=pairIndicator N n*(Real.log N-Real.log ((N-n:ℕ):ℝ)) := by
  simp only [loss,pairIndicator,Nat.sub_sub_self hn,and_comm (a:=(N-n).Prime)]

private lemma prime_diagonal {N n : ℕ} (hn : n≤N) (p : n.Prime) (q : (N-n).Prime)
    (nc : ¬n.Coprime N) : n=N/2 := by
  have divides := Classical.not_not.mp (mt p.coprime_iff_not_dvd.mpr nc)
  have dm : n∣N-n := Nat.dvd_sub divides dvd_rfl
  rcases (Nat.dvd_prime q).mp dm with one|same
  · exact (p.ne_one one).elim
  · omega

private lemma variation_point (N n : ℕ) (np : 0<N) (hn : n≤N) :
    |rawMass N n-(Real.log N)^2*pairIndicator N n|≤
      Real.log N*(loss N n+loss N (N-n))+Real.log N*(powerPart n+powerPart (N-n))+
      (if n=N/2 then (Real.log N)^2 else 0) := by
  let L := Real.log (N:ℝ)
  have lp : 0≤L := Real.log_nonneg (by exact_mod_cast np : (1:ℝ)≤N)
  have ma : 0≤mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have mb : 0≤mangoldt (N-n) := ArithmeticFunction.vonMangoldt_nonneg
  have a : mangoldt n≤L := mangoldt_le_log_of_le np hn
  have b : mangoldt (N-n)≤L := mangoldt_le_log_of_le np (Nat.sub_le ..)
  have tail : 0≤(if n=N/2 then L^2 else 0) := by split <;> positivity
  rw [mirror_loss N n hn]
  change |rawMass N n-L^2*pairIndicator N n|≤L*(loss N n+pairIndicator N n*(L-Real.log ((N-n:ℕ):ℝ)))+
    L*(powerPart n+powerPart (N-n))+(if n=N/2 then L^2 else 0)
  by_cases p : n.Prime ∧ (N-n).Prime
  · have pn := p.1
    have qn := p.2
    have x : mangoldt n=Real.log n := ArithmeticFunction.vonMangoldt_apply_prime pn
    have y : mangoldt (N-n)=Real.log ((N-n:ℕ):ℝ) := ArithmeticFunction.vonMangoldt_apply_prime qn

    by_cases cp : n.Coprime N
    · simp only [rawMass,ite_eq_left cp,loss,pairIndicator,ite_eq_left p,one_mul,mul_one,powerPart,ite_eq_left pn,ite_eq_left qn,add_zero,mul_zero]
      rw [← x,← y,abs_of_nonpos (by nlinarith only [mul_le_mul a b mb lp] : mangoldt n*mangoldt (N-n)-L^2≤0)]
      nlinarith only [mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr b),tail]
    · have eq := prime_diagonal hn pn qn cp
      simp only [rawMass,ite_eq_right cp,loss,pairIndicator,ite_eq_left p,one_mul,mul_one,powerPart,ite_eq_left pn,ite_eq_left qn,
        add_zero,mul_zero,zero_sub,abs_neg,abs_of_nonneg (sq_nonneg L),ite_eq_left eq]
      rw [← x,← y]
      nlinarith only [mul_nonneg lp (sub_nonneg.mpr a),mul_nonneg lp (sub_nonneg.mpr b)]
  · simp only [loss,pairIndicator,p,ite_false,zero_mul,mul_zero,add_zero,zero_add,sub_zero]
    have pparts : mangoldt n*mangoldt (N-n)≤L*(powerPart n+powerPart (N-n)) := by
      by_cases u : n.Prime
      · have v : ¬(N-n).Prime := fun h => p ⟨u,h⟩
        simpa [powerPart,u,v] using mul_le_mul_of_nonneg_right a mb
      · have hn' := mul_le_mul_of_nonneg_left b ma
        have hb := mul_nonneg lp (power_nonneg (N-n))
        rw [powerPart,ite_eq_right u]
        nlinarith only [hn',hb]
    have rawcap : |rawMass N n|≤mangoldt n*mangoldt (N-n) := by
      unfold rawMass
      split <;> simp [abs_of_nonneg (mul_nonneg ma mb),mul_nonneg ma mb]
    exact rawcap.trans (pparts.trans (le_add_of_nonneg_right tail))

private lemma both_powers :
    ∃ B : ℝ, 0≤B ∧ ∀ N : ℕ, ∑ n∈range N, (powerPart n+powerPart (N-n))≤ B*Real.sqrt N := by
  obtain ⟨B,h⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨2*|B|,by positivity,?_⟩
  intro N
  have s : (∑ n∈range (N+1), powerPart n)=Chebyshev.psi N-Chebyshev.theta N := by
    simpa only [powerPart,ite_not] using sum_nonprime_mangoldt_eq_psi_sub_theta N
  have r : (∑ n∈range (N+1), powerPart (N-n))=∑ n∈range (N+1), powerPart n := by
    simpa using sum_range_reflect powerPart (N+1)
  have sub : range N⊆range (N+1) := range_mono (by omega)
  have a := sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => power_nonneg n)
  have b := sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => power_nonneg (N-n))
  rw [r] at b
  rw [s] at a b
  rw [sum_add_distrib]
  have c := (h (N:ℝ)).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.sqrt_nonneg _))
  linarith

/-- Uniform error on all subsets of the first line follows by bounding
the sum of the absolute atom-by-atom errors. -/
theorem variation_bound :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 2^64≤N → Even N →
      ∑ n∈range N, |rawMass N n-(Real.log N)^2*pairIndicator N n|≤
        C*((N:ℝ)*singularSeries N/Real.log N+Real.sqrt N*(Real.log N)^2) := by
  obtain ⟨C,cp,abel⟩ := pair_log_loss
  obtain ⟨B,bp,powers⟩ := both_powers
  refine ⟨2*C+B+13,by positivity,?_⟩
  intro N big ev
  have np : 0<N := by omega
  let L := Real.log (N:ℝ)
  have one : 1≤L := by
    apply ((Real.le_log_iff_exp_le (by exact_mod_cast np : 0<(N:ℝ))).mpr)
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3≤N by omega))
  have lp := zero_lt_one.trans_le one
  have root : 1≤Real.sqrt (N:ℝ) := by simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤N by exact_mod_cast np)
  have endpoint : loss N N=0 := by simp [loss]
  have initial : loss N 0=0 := by simp [loss,pairIndicator,Nat.not_prime_zero]
  have mir : (∑ n∈range N, loss N (N-n))=∑ n∈range N, loss N n := by
    have e : (∑ n∈range (N+1), loss N (N-n))=∑ n∈range (N+1), loss N n := by
      simpa using sum_range_reflect (loss N) (N+1)
    simpa only [sum_range_succ,Nat.sub_self,initial,endpoint,add_zero] using e
  have logcap : L*(∑ n∈range N, loss N n)≤C*((N:ℝ)*singularSeries N/L)+6*Real.sqrt N*L^2 := by
    apply le_of_mul_le_mul_left _ lp
    have b := abel N big ev
    change L^2*(∑ n∈range N, loss N n)≤C*N*singularSeries N+6*Real.sqrt N*L^3 at b
    field_simp
    nlinarith only [b]
  have sumcap := sum_le_sum (s:=range N) (fun n hn => variation_point N n np (mem_range.mp hn).le)
  change (∑ n∈range N, |rawMass N n-L^2*pairIndicator N n|)≤_
  apply sumcap.trans
  simp only [sum_add_distrib,← mul_sum,mir]
  have diag : (∑ n∈range N, if n=N/2 then (Real.log N)^2 else 0)≤L^2 := by
    rw [sum_ite_eq']
    split <;> first | rfl | positivity
  have pw := mul_le_mul_of_nonneg_left (powers N) lp.le
  have u : 0≤(N:ℝ)*singularSeries N/L := by have := singularSeries_pos N; positivity
  have v : 0≤Real.sqrt (N:ℝ)*L^2 := by positivity
  have loss2 := mul_le_mul_of_nonneg_left one (mul_nonneg bp (mul_nonneg (Real.sqrt_nonneg (N:ℝ)) lp.le))
  have rt := mul_le_mul_of_nonneg_right root (sq_nonneg L)
  change L*((∑ n∈range N, loss N n)+(∑ n∈range N, loss N n))+
    L*((∑ n∈range N, powerPart n)+(∑ n∈range N, powerPart (N-n)))+_≤_
  rw [sum_add_distrib] at pw
  dsimp only [L] at *
  nlinarith only [logcap,diag,pw,loss2,rt,mul_nonneg (show 0≤B+13 by linarith) u,mul_nonneg cp.le v]

#print axioms variation_bound
end GoldbachSpectral435.GoldbachSieve
