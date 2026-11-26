module
public import PrimitiveAdditiveMean
public import HorizonDenominators

/-! The reduced-residue Fourier coefficient at arbitrary integral shifts
and its exact contribution to the denominator-truncated Euler product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open ConditionalGoldbach Finset ArithmeticFunction Complex
namespace GoldbachSpectral435.CriticalCharacter
open GoldbachSieve

def divisorWeight (H : ℕ) : ArithmeticFunction ℤ where
  toFun n := if n∣H then n else 0
  map_zero' := by simp

private lemma divisor_mult (H : ℕ) : (divisorWeight H).IsMultiplicative := by
  refine ⟨by simp [divisorWeight],?_⟩
  intro d e cp
  have criterion : d*e∣H ↔ d∣H ∧ e∣H := ⟨fun h => ⟨(dvd_mul_right ..).trans h,(dvd_mul_left ..).trans h⟩,
    fun h => cp.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  change (if d*e∣H then ((d*e:ℕ):ℤ) else 0) = (if d∣H then (d:ℤ) else 0)*(if e∣H then (e:ℤ) else 0)
  by_cases a : d∣H <;> by_cases b : e∣H <;> simp [criterion,a,b]

def ramanujan (H : ℕ) : ArithmeticFunction ℤ := moebius*divisorWeight H

lemma ramanujan_mult (H : ℕ) : (ramanujan H).IsMultiplicative := isMultiplicative_moebius.mul (divisor_mult H)

lemma ramanujan_divisors (H q : ℕ) : ramanujan H q=
    ∑ d∈q.divisors, moebius d*(if q/d∣H then ((q/d:ℕ):ℤ) else 0) := by
  unfold ramanujan
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun d e => moebius d*divisorWeight H e)]
  rfl

lemma ramanujan_prime (H p : ℕ) (pr : p.Prime) :
    ramanujan H p=if p∣H then (p:ℤ)-1 else -1 := by
  rw [ramanujan_divisors,pr.sum_divisors,Nat.div_self pr.pos,Nat.div_one,moebius_apply_prime pr]
  by_cases d : p∣H <;> simp [d,sub_eq_add_neg,add_comm]

private lemma phase_on_multiples (H q d : ℕ) [NeZero q] (dv : d∣q)
    (ψ : AddChar (ZMod q) ℂ) (inj : Function.Injective ψ) :
    (∑ n∈range q, if d∣n then ψ ((H:ZMod q)*n) else 0)=
      if q/d∣H then ((q/d:ℕ):ℂ) else 0 := by
  let e := q/d
  have dp := Nat.pos_of_dvd_of_pos dv (NeZero.pos q)
  have eq : d*e=q := Nat.mul_div_cancel' dv
  rw [sum_on_multiples d q dp dv]
  let b := ψ ((H:ZMod q)*d)
  have term (k : ℕ) : ψ ((H:ZMod q)*((d*k:ℕ):ZMod q))=b^k := by
    rw [Nat.cast_mul,← mul_assoc,mul_comm _ (k:ZMod q),← nsmul_eq_mul,AddChar.map_nsmul_eq_pow]
  simp_rw [term]
  have test : b=1 ↔ e∣H := by
    have eqv : b=1 ↔ ((H*d:ℕ):ZMod q)=0 := by
      rw [Nat.cast_mul]
      exact ⟨fun h => inj (h.trans ψ.map_zero_eq_one.symm),fun h => by dsimp only [b]; rw [h,ψ.map_zero_eq_one]⟩
    rw [eqv,ZMod.natCast_eq_zero_iff,← eq,mul_comm H d]
    exact Nat.mul_dvd_mul_iff_left dp
  by_cases h : e∣H
  · rw [ite_eq_left h,test.mpr h]
    simp
  rw [ite_eq_right h,geom_sum_eq (mt test.mp h)]
  have power : b^e=1 := by
    rw [← term e,eq,ZMod.natCast_self,mul_zero,ψ.map_zero_eq_one]
  rw [power,sub_self,zero_div]

/-- The integral arithmetic function is exactly the complex sum at
frequency H for every primitive additive character on the modulus. -/
theorem ramanujan_phase (H q : ℕ) [NeZero q] (ψ : AddChar (ZMod q) ℂ) (inj : Function.Injective ψ) :
    (∑ a∈unitClasses q, ψ ((H:ZMod q)*a))=(ramanujan H q:ℂ) := by
  rw [unit_phase_expansion,ramanujan_divisors,Int.cast_sum]
  apply sum_congr rfl
  intro d hd
  rw [phase_on_multiples H q d (Nat.mem_divisors.mp hd).1 ψ inj,Int.cast_mul]
  split_ifs <;> simp only [Int.cast_natCast,Int.cast_zero]

private def totientFunction : ArithmeticFunction ℕ := ⟨Nat.totient,Nat.totient_zero⟩
private lemma totient_mult : totientFunction.IsMultiplicative := ⟨Nat.totient_one,fun h => Nat.totient_mul h⟩

lemma squarefree_coefficient (H : ℕ) (T : Finset ℕ) (pr : ∀ p∈T,p.Prime) :
    (∏ p∈T,localCoefficient H p)=(ramanujan H (∏ p∈T,p):ℝ)/((∏ p∈T,p).totient:ℝ)^2 := by
  have a := (ramanujan_mult H).map_prod_of_prime T pr
  have b := totient_mult.map_prod_of_prime T pr
  change (∏ p∈T,p).totient=∏ p∈T,p.totient at b
  rw [a,b,Int.cast_prod,Nat.cast_prod,← prod_pow,← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  have pp := pr p hp
  rw [ramanujan_prime H p pp,Nat.totient_prime pp,Nat.cast_sub pp.one_le,Nat.cast_one]
  have nz : (p:ℝ)-1≠0 := by
    have h : (1:ℝ)<p := by exact_mod_cast pp.one_lt
    linarith
  by_cases dvd : p∣H <;> simp [localCoefficient,dvd] <;> field_simp

/-- The denominator truncation in the spectral criterion is the ordinary
partial sum of the Goldbach Ramanujan series, including nonsquarefree indices. -/
theorem denominator_ramanujan (H Q : ℕ) :
    denominatorSum H Q=∑ q∈Icc 1 Q, (moebius q:ℝ)^2*(ramanujan H q:ℝ)/(q.totient:ℝ)^2 := by
  classical
  let P := smallPrimes Q
  let d := fun T : Finset ℕ => ∏ p∈T,p
  let a := fun q : ℕ => (moebius q:ℝ)^2*(ramanujan H q:ℝ)/(q.totient:ℝ)^2
  let B := (Icc 1 Q).filter Squarefree
  have off : (∑ q∈B,a q)=∑ q∈Icc 1 Q,a q := by
    apply sum_subset (filter_subset ..)
    intro q hq outside
    have ns : ¬Squarefree q := fun sq => outside (mem_filter.mpr ⟨hq,sq⟩)
    simp [a,moebius_eq_zero_of_not_squarefree ns]
  change (∑ T∈P.powerset,if d T≤Q then ∏ p∈T,localCoefficient H p else 0)=_
  rw [← off,← sum_filter]
  let F := P.powerset.filter (fun T => d T≤Q)
  have pr (T : Finset ℕ) (ht : T∈F) (p : ℕ) (m : p∈T) : p.Prime :=
    (mem_filter.mp ((mem_powerset.mp (mem_filter.mp ht).1) m)).2
  have sq (T : Finset ℕ) (ht : T∈F) : Squarefree (d T) := by
    apply (squarefree_primorial Q).squarefree_of_dvd
    apply Finset.prod_primes_dvd _ (fun p h => (pr T ht p h).prime)
    intro p h
    exact (pr T ht p h).dvd_primorial_iff.mpr (Nat.le_of_lt_succ (mem_range.mp
      (mem_filter.mp (mem_powerset.mp (mem_filter.mp ht).1 h)).1))
  apply sum_bij (fun T _ => d T)
  · intro T ht
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero (sq T ht).ne_zero,(mem_filter.mp ht).2⟩,sq T ht⟩
  · intro T ht U hu e
    have t := Nat.primeFactors_prod (pr T ht)
    have u := Nat.primeFactors_prod (pr U hu)
    change (d T).primeFactors=T at t
    change (d U).primeFactors=U at u
    exact t.symm.trans ((congrArg Nat.primeFactors e).trans u)
  · intro q hq
    obtain ⟨bound,hs⟩ := mem_filter.mp hq
    have id := Nat.prod_primeFactors_of_squarefree hs
    change d q.primeFactors=q at id
    refine ⟨q.primeFactors,mem_filter.mpr ⟨mem_powerset.mpr ?_,by rw [id]; exact (mem_Icc.mp bound).2⟩,id⟩
    intro p m
    obtain ⟨pp,dv,nz⟩ := Nat.mem_primeFactors.mp m
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_dvd (Nat.pos_of_ne_zero nz) dv).trans (mem_Icc.mp bound).2)),pp⟩
  · intro T ht
    have mu := moebius_sq_eq_one_of_squarefree (sq T ht)
    have eq : (moebius (d T):ℝ)^2=1 := by exact_mod_cast mu
    dsimp only [a]
    rw [eq,one_mul]
    exact squarefree_coefficient H T (pr T ht)

/-- One increasing polylogarithmic denominator cutoff gives the original
singular series uniformly on every even line in the finite spectral test. -/
theorem full_horizon_ramanujan (ε : ℝ) (ep : 0<ε) :
    ∃ A : ℕ, 0<A ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ H : ℕ, 0<H → Even H →
      H≤2*PhysicalTests.scale N*N →
      |(∑ q∈Icc 1 ((localCutoff N)^A), (moebius q:ℝ)^2*(ramanujan H q:ℝ)/(q.totient:ℝ)^2)/
        singularSeries H-1|≤ε := by
  simpa only [denominator_ramanujan] using horizon_denominators ε ep

#print axioms full_horizon_ramanujan
#print axioms ramanujan_phase
#print axioms squarefree_coefficient
end GoldbachSpectral435.CriticalCharacter
