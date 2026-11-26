module
public import SingularDenominators

/-! Uniform approximation of the singular series on the full spectral horizon
by the squarefree coefficients with denominator at most a power of log N. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open ConditionalGoldbach Finset Filter
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open PhysicalTests

private lemma point_score (H p z : ℕ) (pp : p.Prime) (zp : 0<z) :
    |localCoefficient H p| * Real.log p/(1+|localCoefficient H p|)≤
      (if p≤z then Real.log p/p else 0)+(if p∣H then Real.log p/z else 0)+
        (4/(z:ℝ))*(Real.log p/p) := by
  let w := |localCoefficient H p|
  have wp : 0≤w := abs_nonneg _
  have pr : (2:ℝ)≤p := by exact_mod_cast pp.two_le
  have pos : 0<(p:ℝ) := by linarith
  have zr : 0<(z:ℝ) := Nat.cast_pos.mpr zp
  have den : 0<(p:ℝ)-1 := by linarith
  have lg := Real.log_nonneg (show (1:ℝ)≤p by linarith)
  have bound : w/(1+w)≤1/(p:ℝ) := by
    apply (div_le_div_iff₀ (by positivity) pos).mpr
    have step : w*((p:ℝ)-1)≤1 := by
      dsimp [w,localCoefficient]
      split_ifs
      · rw [abs_of_pos (one_div_pos.mpr den),one_div_mul_cancel den.ne']
      · rw [abs_neg,abs_of_pos (by positivity),one_div_mul_eq_div]
        apply (div_le_one (pow_pos den 2)).mpr
        nlinarith only [mul_nonneg den.le (sub_nonneg.mpr pr)]
    linarith
  have eq : w*Real.log p/(1+w)=w/(1+w)*Real.log p := by ring
  change w*Real.log p/(1+w)≤_
  rw [eq]
  have bs := (mul_le_mul_of_nonneg_right bound lg).trans_eq (by ring : 1/(p:ℝ)*Real.log p=Real.log p/p)
  have loss : 0≤(4/(z:ℝ))*(Real.log p/p) := by positivity
  by_cases small : p≤z
  · rw [ite_eq_left small]
    split_ifs <;> linarith [div_nonneg lg zr.le]
  rw [ite_eq_right small,zero_add]
  have zp' : (z:ℝ)≤p := by exact_mod_cast (le_of_lt (lt_of_not_ge small))
  by_cases dvd : p∣H
  · rw [ite_eq_left dvd]
    exact bs.trans ((div_le_div_of_nonneg_left lg zr zp').trans (le_add_of_nonneg_right loss))
  rw [ite_eq_right dvd,zero_add]
  have wval : w=1/((p:ℝ)-1)^2 := by simp only [w,localCoefficient,ite_eq_right dvd,abs_neg,abs_of_pos (by positivity : 0<1/((p:ℝ)-1)^2)]
  have wle : w≤4/((z:ℝ)*p) := by
    rw [wval,div_le_div_iff₀ (pow_pos den 2) (mul_pos zr pos)]
    have a := mul_le_mul_of_nonneg_right zp' pos.le
    nlinarith only [a,mul_nonneg (sub_nonneg.mpr pr) (show 0≤3*(p:ℝ)-2 by linarith)]
  have wr : w/(1+w)≤w := div_le_self wp (by linarith)
  exact (mul_le_mul_of_nonneg_right (wr.trans wle) lg).trans_eq (by ring)

theorem horizon_score (H z A : ℕ) (hp : 0<H) (zz : 2≤z) (large : 8*A≤z)
    (B : ℝ) (size : Real.log H≤B*z*Real.log z) :
    (∑ p∈smallPrimes (z^A), |localCoefficient H p| * Real.log p/(1+|localCoefficient H p|))≤
      (3+B)*Real.log z := by
  classical
  let Q := z^A
  let P := smallPrimes Q
  have zp : 0<z := by omega
  have zr : 0<(z:ℝ) := Nat.cast_pos.mpr zp
  have lp := Real.log_nonneg (show (1:ℝ)≤z by exact_mod_cast (show 1≤z by omega))
  have qp : 0<Q := pow_pos zp _
  have pr (p : ℕ) (m : p∈P) : p.Prime := (mem_filter.mp m).2
  have sm (p : ℕ) (m : p∈P) : p≤Q := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp m).1)
  have logQ : Real.log (Q:ℝ)=(A:ℝ)*Real.log z := by simp only [Q,Nat.cast_pow,Real.log_pow]
  have small : (∑ p∈P,if p≤z then Real.log p/p else 0)≤2*Real.log z := by
    rw [← sum_filter]
    exact prime_log_sum z zp _ (fun p m => pr p (mem_filter.mp m).1) (fun _ m => (mem_filter.mp m).2)
  have divisor : (∑ p∈P,if p∣H then Real.log p/z else 0)≤B*Real.log z := by
    rw [← sum_filter,← sum_div,div_le_iff₀ zr]
    have sub : P.filter (·∣H)⊆H.primeFactors := fun p h => Nat.mem_primeFactors.mpr
      ⟨pr p (mem_filter.mp h).1,(mem_filter.mp h).2,hp.ne'⟩
    have m := sum_le_sum_of_subset_of_nonneg (f:=fun p : ℕ => Real.log p) sub
      (fun p h _ => Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_le))
    exact (m.trans ((sum_log_primeFactors_le_log H hp).trans size)).trans_eq (by ring)
  have nondiv : (∑ p∈P,(4/(z:ℝ))*(Real.log p/p))≤Real.log z := by
    rw [← mul_sum]
    apply (mul_le_mul_of_nonneg_left (prime_log_sum Q qp P pr sm) (by positivity : 0≤4/(z:ℝ))).trans
    rw [logQ,div_mul_eq_mul_div,div_le_iff₀ zr]
    have sz : 8*(A:ℝ)≤z := by exact_mod_cast large
    linarith only [mul_le_mul_of_nonneg_right sz lp]
  have point := sum_le_sum (s:=P) (fun p m => point_score H p z (pr p m) zp)
  rw [sum_add_distrib,sum_add_distrib] at point
  exact point.trans (by linarith only [small,divisor,nondiv])

/-- The rational-denominator truncation is uniform in every even shift that
occurs at Li and Liu's full prescribed sampling horizon. -/
theorem horizon_denominators (ε : ℝ) (ep : 0<ε) :
    ∃ A : ℕ, 0<A ∧ ∀ᶠ N : ℕ in atTop, ∀ H : ℕ, 0<H → Even H → H≤2*scale N*N →
      |denominatorSum H ((localCutoff N)^A)/singularSeries H-1|≤ε := by
  let η := min (ε/2) 1
  have eta : 0<η := lt_min (by positivity) zero_lt_one
  obtain ⟨A,ha⟩ := exists_nat_gt (8*(2307:ℝ)/η)
  have ap : 0<A := by exact_mod_cast (show (0:ℝ)<A from (by positivity : 0<(8*(2307:ℝ)/η)).trans ha)
  refine ⟨A,ap,?_⟩
  have grows : Tendsto (fun N => (localCutoff N)^A) atTop atTop :=
    (tendsto_pow_atTop ap.ne').comp cutoff_grows
  filter_upwards [eventually_ge_atTop (1:ℕ),cutoff_grows.eventually_ge_atTop (max 128 (8*A)),
    grows.eventually (truncated_series_uniform 2304 η eta)] with N np cut uniform
  intro H hp ev size
  let z := localCutoff N
  let Q := z^A
  have zmin : 128≤z := (le_max_left ..).trans cut
  have zbig : 8*A≤z := (le_max_right ..).trans cut
  have zz : 2≤z := by omega
  have zq : z≤Q := Nat.le_self_pow ap.ne' _
  have qq : 2≤Q := zz.trans zq
  have zr : (1:ℝ)<z := by exact_mod_cast (show 1<z by omega)
  have lz := Real.log_pos zr
  have sizeH := (cutoff_horizon N np zmin).2 H hp size
  have szQ : Real.log H≤2304*Q*Real.log Q := by
    apply sizeH.trans
    gcongr
  have near := uniform H hp szQ
  change |truncatedSeries H Q/singularSeries H-1|≤η at near
  let T := truncatedSeries H Q
  let S := singularSeries H
  have sp : 0<S := singularSeries_pos H
  have tBound : T≤2*S := by
    have j := (abs_le.mp near).2
    have one : η≤1 := min_le_right ..
    exact (div_le_iff₀ sp).mp (by change truncatedSeries H Q/singularSeries H≤2; linarith)
  have score := horizon_score H z A hp zz zbig 2304 sizeH
  have tail := denominator_tail H Q hp ev qq _ score
  have logQ : Real.log (Q:ℝ)=(A:ℝ)*Real.log z := by simp only [Q,Nat.cast_pow,Real.log_pow]
  rw [logQ] at tail
  have t : |denominatorSum H Q-T| * (A:ℝ)≤4*T*2307 := by
    apply le_of_mul_le_mul_right _ lz
    change |denominatorSum H Q-truncatedSeries H Q| * (A:ℝ)*Real.log z≤4*truncatedSeries H Q*2307*Real.log z
    linarith only [tail]
  have a : 8*(2307:ℝ)≤(A:ℝ)*η := ((div_lt_iff₀ eta).mp ha).le
  have err : |denominatorSum H Q-T|≤η*S := by
    apply le_of_mul_le_mul_right _ (Nat.cast_pos.mpr ap : 0<(A:ℝ))
    nlinarith only [t,mul_le_mul_of_nonneg_right a sp.le,tBound]
  have e : |denominatorSum H Q/S-T/S|≤η := by
    rw [← sub_div,abs_div,abs_of_pos sp,div_le_iff₀ sp]
    exact err
  have tri := abs_sub_le (denominatorSum H Q/S) (T/S) 1
  have half : η≤ε/2 := min_le_left ..
  exact tri.trans (by linarith only [near,e,half])

#print axioms horizon_denominators
end GoldbachSpectral435.GoldbachSieve
