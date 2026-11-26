module
public import WeightedPrimeLimit
public import MixedSieve
public import ConditionalGoldbach.Proofs.PrimePowers

/-! Uniform mixed prime and sieve asymptotics over the original finite
horizon. Only the genuine two-prime correlation remains after centering. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Chebyshev MeasureTheory Finset Filter
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open PhysicalTests
open MathlibNt.SieveTheory.MertensTheorem (primeProduct)

private theorem principal_loss (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ q M : ℕ, 0<q → 0<M → (q:ℝ)<M*hf.lower →
      |principalMass q M f-primeSum M f|≤C*Real.sqrt M := by
  obtain ⟨B,b⟩ := isCompact_Icc (a:=(0:ℝ)) (b:=1) |>.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨D,d⟩ := psi_sub_theta_le_mul_sqrt
  let K := |B|+1
  have kp : 0<K := by dsimp [K]; positivity
  refine ⟨K*(|D|+1),by positivity,?_⟩
  intro q M qp mp small
  let bad := fun n : ℕ => if ¬n.Prime then mangoldt n else 0
  have nn (n : ℕ) : 0≤bad n := by dsimp [bad]; split <;> first | exact ArithmeticFunction.vonMangoldt_nonneg | rfl
  have mr : 0<(M:ℝ) := Nat.cast_pos.mpr mp
  have point (n : ℕ) (h : n∈range M) :
      |(if n.Coprime q then weightedMangoldt M n f else 0)-weightedMangoldt M n f|≤K*bad n := by
    by_cases cp : n.Coprime q
    · rw [ite_eq_left cp,sub_self,abs_zero]
      exact mul_nonneg kp.le (nn n)
    rw [ite_eq_right cp,zero_sub,abs_neg,weightedMangoldt,abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    by_cases p : n.Prime
    · have dv : n∣q := Classical.not_not.mp (mt p.coprime_iff_not_dvd.mpr cp)
      have lt : (n:ℝ)/M<hf.lower := (div_lt_iff₀ mr).mpr (by
        rw [mul_comm]
        exact (Nat.cast_le.mpr (Nat.le_of_dvd qp dv)).trans_lt small)
      have z : f (n/(M:ℝ))=0 := by by_contra nz; exact (not_le_of_gt lt) (hf.mem_support_interval nz).1
      simp [z,bad,p]
    · have loc : (n:ℝ)/M∈Set.Icc (0:ℝ) 1 := ⟨by positivity,(div_le_one mr).mpr (by exact_mod_cast (mem_range.mp h).le)⟩
      have cap : |f (n/(M:ℝ))|≤K := (b _ loc).trans (by dsimp [K]; linarith [le_abs_self B])
      simpa only [bad,p,not_false_eq_true,ite_true,mul_comm K] using
        mul_le_mul_of_nonneg_left cap (ArithmeticFunction.vonMangoldt_nonneg (n:=n))
  have sub : range M⊆range (M+1) := range_mono (by omega)
  have sum := sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => nn n)
  have tot : (∑ n∈range (M+1),bad n)=psi M-theta M := sum_nonprime_mangoldt_eq_psi_sub_theta M
  rw [tot] at sum
  rw [principalMass,primeSum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum point).trans _)
  rw [← mul_sum,mul_assoc]
  exact mul_le_mul_of_nonneg_left ((sum.trans (d (M:ℝ))).trans
    (mul_le_mul_of_nonneg_right (by linarith [le_abs_self D]) (Real.sqrt_nonneg _))) kp.le

theorem uniform_principal (f : ℝ→ℝ) (hf : FiniteModelWeight f) (ε : ℝ) (ep : 0<ε) :
    ∀ᶠ M : ℕ in atTop, ∀ q : ℕ, 0<q → (q:ℝ)≤Real.sqrt M →
      |principalMass q M f/M-(∫ u in (0:ℝ)..1,f u)|≤ε := by
  obtain ⟨C,cp,loss⟩ := principal_loss f hf
  have growth := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have l1 : Tendsto (fun M : ℕ => 1/Real.sqrt M) atTop (𝓝 0) := tendsto_const_nhds.div_atTop growth
  have lc : Tendsto (fun M : ℕ => C/Real.sqrt M) atTop (𝓝 0) := tendsto_const_nhds.div_atTop growth
  filter_upwards [eventually_ge_atTop (1:ℕ),l1.eventually_lt_const hf.lower_pos,
    lc.eventually_lt_const (half_pos ep),Metric.tendsto_nhds.mp (primeSum_limit f hf) _ (half_pos ep)] with M mp one small base
  have mr : 0<(M:ℝ) := Nat.cast_pos.mpr mp
  have sp := Real.sqrt_pos.mpr mr
  have ss := Real.sq_sqrt mr.le
  intro q qp qle
  have lower := (div_lt_iff₀ sp).mp one
  have qb : (q:ℝ)<M*hf.lower := qle.trans_lt (by
    calc Real.sqrt M = 1*Real.sqrt M := (one_mul _).symm
         _ < (hf.lower*Real.sqrt M)*Real.sqrt M := mul_lt_mul_of_pos_right lower sp
         _ = M*hf.lower := by rw [mul_assoc,← sq,ss,mul_comm])
  have bound := loss q M qp mp qb
  have s : |principalMass q M f/M-primeSum M f/M|≤C/Real.sqrt M := by
    rw [← sub_div,abs_div,abs_of_pos mr,div_le_div_iff₀ mr sp]
    apply (mul_le_mul_of_nonneg_right bound sp.le).trans_eq
    rw [mul_assoc,← sq,ss]
  rw [Real.dist_eq] at base
  exact (abs_sub_le _ (primeSum M f/M) _).trans (by linarith)

/-- One prime variable can be kept genuine, with a uniform limit for every
translation H and every sampling scale M at least N. -/
theorem mixed_prime_limit (f : ℝ→ℝ) (hf : FiniteModelWeight f) (ε : ℝ) (ep : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ M H : ℕ, N≤M → 0<H → Even H → H≤2*scale N*N →
      GRH (primorial (localCutoff N)) →
      |mixedMass H (localCutoff N) M f/((M:ℝ)*primeProduct (localCutoff N)*singularSeries H)-
        (∫ u in (0:ℝ)..1,f u)|≤ε := by
  obtain ⟨C,cp,h⟩ := mixed_horizon_power f hf
  let I := ∫ u in (0:ℝ)..1,f u
  let δ := min 1 (ε/(4*(|I|+1)))
  have dp : 0<δ := lt_min zero_lt_one (div_pos ep (by positivity))
  have d1 : δ≤1 := min_le_left ..
  have dε : δ*(|I|+1)≤ε/4 := by
    have d := (le_div_iff₀ (by positivity : 0<4*(|I|+1))).mp (min_le_right 1 (ε/(4*(|I|+1))))
    dsimp [δ]; linarith
  have growth := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have lim : Tendsto (fun M : ℕ => C/(M:ℝ)^(1/8:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop growth
  obtain ⟨K,k⟩ := eventually_atTop.mp ((uniform_principal f hf (ε/4) (by positivity)).and
    (lim.eventually_lt_const (show (0:ℝ)<ε/4 by positivity)))
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop (1:ℕ),cutoff_grows.eventually_ge_atTop 3,
    all_horizon_factors δ dp] with N nk np zz cap
  intro M H nm hp ev hh grh
  let z := localCutoff N
  let Q := primorial z
  let S := singularSeries H
  let T := truncatedSeries H z
  let A := mixedMass H z M f/((M:ℝ)*primeProduct z)
  let P := principalMass Q M f/(M:ℝ)
  have qp : (1:ℝ)≤Q := by exact_mod_cast primorial_pos z
  have qle : (Q:ℝ)≤Real.sqrt M :=
    (le_self_pow₀ qp (by decide : 3≠0)).trans (cap.1.trans (Real.sqrt_le_sqrt (Nat.cast_le.mpr nm)))
  obtain ⟨pr,sm⟩ := k M (nk.trans nm)
  have near : |P-I|≤ε/4 := pr Q (primorial_pos z) qle
  have sp : 0<S := singularSeries_pos H
  have ss : 1≤S := (singularSeries_gt_one H).le
  have ap : |A-T*P|≤ε/4 := (h N M H np nm zz hp ev grh).trans sm.le
  have rem : |(A-T*P)/S|≤ε/4 := by
    rw [abs_div,abs_of_pos sp]
    exact (div_le_self (abs_nonneg _) ss).trans ap
  have ratio : |T/S-1|≤δ := cap.2 H hp hh
  have tb : |T/S|≤2 := by
    have b := abs_add_le (T/S-1) 1
    rw [sub_add_cancel,abs_one] at b
    linarith only [b,ratio,d1]
  have di := mul_le_mul_of_nonneg_right ratio (abs_nonneg I)
  have prod := mul_le_mul tb near (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  change |mixedMass H z M f/((M:ℝ)*primeProduct z*S)-I|≤ε
  rw [← div_div]
  change |A/S-I|≤_
  have eq : A/S-I=(A-T*P)/S+((T/S)*(P-I)+(T/S-1)*I) := by ring
  rw [eq]
  apply (abs_add_le ..).trans
  have right := abs_add_le ((T/S)*(P-I)) ((T/S-1)*I)
  simp only [abs_mul] at right
  linarith only [rem,right,di,prod,dε,dp]

#print axioms uniform_principal
#print axioms mixed_prime_limit
end GoldbachSpectral435.GoldbachSieve
