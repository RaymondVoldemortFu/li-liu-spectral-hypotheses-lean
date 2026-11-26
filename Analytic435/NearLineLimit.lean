module
public import NearLineDispersion

/-! Both prime variables are retained in every congruence. At a dyadic
lift close to the allowed maximum, only logarithmically many sum or
difference lines occur in the support of the two weights. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset MeasureTheory
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open PhysicalTests

lemma base_period {N M : ℕ} (np : 0<N) (nm : N≤M) :
    (primorial (localCutoff N):ℝ)≤Real.sqrt M := by
  let Q := primorial (localCutoff N)
  have qp : (1:ℝ)≤Q := Nat.one_le_cast.mpr (primorial_pos _)
  apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
  exact (pow_le_pow_right₀ qp (by decide : 2≤32)).trans ((primorial_cutoff_power N np).trans (Nat.cast_le.mpr nm))

theorem near_modulus_power (k : ℕ) : ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, N≤M → ∃ j : ℕ,
    let q : ℝ := liftedModulus (localCutoff N) j
    let L := Real.log (M:ℝ)
    q*L^k≤M ∧ (M:ℝ)<2*q*L^k := by
  have h := (isLittleO_log_rpow_rpow_atTop (k:ℝ) (show (0:ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h' : Tendsto (fun M : ℕ => (Real.log (M:ℝ))^k/Real.sqrt M) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_eq_rpow,Real.rpow_natCast] using h
  obtain ⟨K,small⟩ := eventually_atTop.mp (h'.eventually_lt_const zero_lt_one)
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop (2:ℕ)] with N nk np
  intro M nm
  let L := Real.log (M:ℝ)
  let Q : ℝ := primorial (localCutoff N)
  have qp : 0<Q := Nat.cast_pos.mpr (primorial_pos _)
  have mr : (1:ℝ)<M := by exact_mod_cast (show 1<M by omega)
  have lp : 0<L := Real.log_pos mr
  have divp : 0<Q*L^k := by positivity
  have cap : Q*L^k≤M := by
    have a : L^k≤Real.sqrt M := (by simpa using (div_lt_iff₀ (Real.sqrt_pos.mpr (zero_lt_one.trans mr))).mp (small M (nk.trans nm)) : L^k<Real.sqrt M).le
    exact (mul_le_mul (base_period (by omega) nm) a (pow_nonneg lp.le _) (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt (Nat.cast_nonneg _))
  obtain ⟨j,lo,hi⟩ := exists_nat_pow_near ((one_le_div divp).mpr cap) (by norm_num : (1:ℝ)<2)
  refine ⟨j,?_⟩
  dsimp only [liftedModulus]
  push_cast
  change 2^j*Q*L^k≤M ∧ (M:ℝ)<2*(2^j*Q)*L^k
  rw [pow_succ (2:ℝ) j] at hi
  constructor
  · linarith only [(le_div_iff₀ divp).mp lo]
  · linarith only [(div_lt_iff₀ divp).mp hi]

theorem near_line_modulus : ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, N≤M → ∃ j : ℕ,
    let q : ℝ := liftedModulus (localCutoff N) j
    let L := Real.log (M:ℝ)
    q*L^8≤M ∧ (M:ℝ)<2*q*L^8 := near_modulus_power 8

lemma perturbed_product {R P U V x y c d δ : ℝ} (dp : 0≤δ) (d1 : δ≤1)
    (cp : 0≤c) (cd : c≤δ) (dd : d≤δ) (rr : |R-1|≤δ)
    (uu : |U-x|≤δ) (vv : |V-y|≤δ) (err : |P-U*V|≤c*d+|U| *d+|V| *c) :
    |R*P-x*y|≤δ*(4*(|x|+|y|+2)+|x*y|) := by
  have absBound (a b : ℝ) (h : |a-b|≤δ) : |a|≤|b|+1 := by
    have e := abs_add_le (a-b) b
    rw [sub_add_cancel] at e
    linarith
  have u := absBound U x uu
  have v := absBound V y vv
  have r : |R|≤2 := by simpa only [abs_one,one_add_one_eq_two] using absBound R 1 rr
  have ab : c*d≤δ := (mul_le_mul_of_nonneg_left dd cp).trans (by nlinarith only [mul_le_mul_of_nonneg_right (cd.trans d1) dp])
  have err' : |P-U*V|≤δ*(|x|+|y|+3) := by
    linarith only [err,ab,(mul_le_mul_of_nonneg_left dd (abs_nonneg U)).trans (mul_le_mul_of_nonneg_right u dp),
      (mul_le_mul_of_nonneg_left cd (abs_nonneg V)).trans (mul_le_mul_of_nonneg_right v dp)]
  have uv : |U*V-x*y|≤δ*(|x|+|y|+1) := by
    rw [show U*V-x*y=(U-x)*V+x*(V-y) by ring]
    have e := abs_add_le ((U-x)*V) (x*(V-y))
    simp only [abs_mul] at e
    linarith only [e,mul_le_mul uu v (abs_nonneg _) dp,mul_le_mul_of_nonneg_left vv (abs_nonneg x)]
  have pv := (abs_sub_le P (U*V) (x*y)).trans (add_le_add err' uv)
  rw [show R*P-x*y=R*(P-x*y)+(R-1)*(x*y) by ring]
  have e := abs_add_le (R*(P-x*y)) ((R-1)*(x*y))
  simp only [abs_mul R,abs_mul (R-1)] at e
  linarith only [e,mul_le_mul r pv (abs_nonneg _) (by norm_num : (0:ℝ)≤2),
    mul_le_mul_of_nonneg_right rr (abs_nonneg (x*y))]

theorem near_line_limit (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (ε : ℝ) (ep : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ M H j : ℕ, N≤M → 0<H → Even H → H≤2*scale N*N →
      let q := liftedModulus (localCutoff N) j
      (q:ℝ)*(Real.log M)^8≤M → GRH q → ∀ sign : Bool,
      |(q:ℝ)*classPairs q H M M sign f g/((M:ℝ)^2*singularSeries H)-
        (∫ u in (0:ℝ)..1,f u)*(∫ u in (0:ℝ)..1,g u)|≤ε := by
  let x := ∫ u in (0:ℝ)..1,f u
  let y := ∫ u in (0:ℝ)..1,g u
  let A := 4*(|x|+|y|+2)+|x*y|
  let δ := min (1/2:ℝ) (ε/A)
  have ap : 0<A := by dsimp [A]; positivity
  have dp : 0<δ := lt_min (by norm_num) (div_pos ep ap)
  have d2 : δ≤1/2 := min_le_left ..
  have d1 : δ≤1 := by linarith
  have pay : δ*A≤ε := (le_div_iff₀ ap).mp (min_le_right ..)
  obtain ⟨C,D,cp,dpos,err⟩ := near_line_error f g hf hg
  have growth := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have small (B : ℝ) := (tendsto_const_nhds.div_atTop (a:=B) growth).eventually_lt_const dp
  obtain ⟨K,k⟩ := eventually_atTop.mp (((uniform_principal f hf δ dp).and
    (uniform_principal g hg δ dp)).and (((small C).and (small D)).and (growth.eventually_ge_atTop 6)))
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop (1:ℕ),cutoff_grows.eventually_ge_atTop 3,
    all_horizon_factors δ dp] with N nk np zz factors
  intro M H j nm hp ev hh q cap grh sign
  let z := localCutoff N
  let T := truncatedSeries H z
  let S := singularSeries H
  let L := Real.log (M:ℝ)
  let U := principalMass q M f/M
  let V := principalMass q M g/M
  let P := (q:ℝ)*classPairs q H M M sign f g/((M:ℝ)^2*T)
  have pp := k M (nk.trans nm)
  have l6 : 6≤L := pp.2.2
  have lp : 0<L := by linarith
  have q4 : 4≤q := calc
    4 ≤ primorial 3 := by decide
    _ ≤ primorial z := primorial_mono zz
    _ ≤ q := Nat.le_of_dvd (NeZero.pos q) (dvd_mul_left ..)
  have qm : q≤M := by
    have b := mul_le_mul_of_nonneg_left (one_le_pow₀ (show 1≤L by linarith) : 1≤L^8) (Nat.cast_nonneg (α:=ℝ) q)
    rw [mul_one] at b
    exact Nat.cast_le.mp (b.trans cap)
  have t := factors.2 H hp hh
  have ss : 1≤S := (singularSeries_gt_one H).le
  have sp : 0<S := zero_lt_one.trans_le ss
  have low : 1/2≤T := by
    have a : 1/2≤T/S := by linarith only [(abs_le.mp t).1,d2]
    linarith only [(le_div_iff₀ sp).mp a,ss]
  have tp : 0<T := by linarith
  have basis := err z j H M (by omega) hp ev q4 qm l6 cap low grh sign
  have u : |U-x|≤δ := by
    dsimp only [U,q]
    rw [lifted_principal (by omega)]
    exact pp.1.1 _ (primorial_pos _) (base_period np nm)
  have v : |V-y|≤δ := by
    dsimp only [V,q]
    rw [lifted_principal (by omega)]
    exact pp.1.2 _ (primorial_pos _) (base_period np nm)
  have e := (perturbed_product dp.le d1 (div_nonneg cp.le lp.le) pp.2.1.1.le pp.2.1.2.le t u v basis).trans pay
  have eq : T/S*P=(q:ℝ)*classPairs q H M M sign f g/((M:ℝ)^2*S) := by dsimp only [P]; field_simp
  exact eq ▸ e

#print axioms near_line_modulus
#print axioms near_line_limit
end GoldbachSpectral435.GoldbachSieve
