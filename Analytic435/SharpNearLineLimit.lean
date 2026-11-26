module
public import SharpPairDispersion
public import NearLineLimit

/-! A two-prime asymptotic down to a logarithmic number of parallel lines. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset MeasureTheory
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open PhysicalTests

theorem sharp_near_line_limit (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (ε : ℝ) (ep : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ᶠ N : ℕ in atTop, ∀ M H j : ℕ, N≤M → 0<H → Even H → H≤2*scale N*N →
      let q := liftedModulus (localCutoff N) j
      q≤M → (q:ℝ)*(6+Real.log q)^2≤η^2*M → GRH q → ∀ sign : Bool,
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
  obtain ⟨C,D,cp,dpos,err⟩ := sharp_near_line_error f g hf hg
  let η := δ/(C+D)
  have sump : 0<C+D := add_pos cp dpos
  have ep' : 0<η := div_pos dp sump
  have eq : (C+D)*η=δ := by dsimp [η]; field_simp
  have cd : C*η≤δ := by nlinarith only [eq,mul_nonneg dpos.le ep'.le]
  have dd : D*η≤δ := by nlinarith only [eq,mul_nonneg cp.le ep'.le]
  refine ⟨η,ep',?_⟩
  obtain ⟨K,k⟩ := eventually_atTop.mp (((uniform_principal f hf δ dp).and
    (uniform_principal g hg δ dp)).and err)
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop (1:ℕ),cutoff_grows.eventually_ge_atTop 3,
    all_horizon_factors δ dp] with N nk np zz factors
  intro M H j nm hp ev hh q qm cap grh sign
  let z := localCutoff N
  let T := truncatedSeries H z
  let S := singularSeries H
  let U := principalMass q M f/M
  let V := principalMass q M g/M
  let P := (q:ℝ)*classPairs q H M M sign f g/((M:ℝ)^2*T)
  have pp := k M (nk.trans nm)
  have q4 : 4≤q := calc
    4 ≤ primorial 3 := by decide
    _ ≤ primorial z := primorial_mono zz
    _ ≤ q := Nat.le_of_dvd (NeZero.pos q) (dvd_mul_left ..)
  have t := factors.2 H hp hh
  have ss : 1≤S := (singularSeries_gt_one H).le
  have sp : 0<S := zero_lt_one.trans_le ss
  have low : 1/2≤T := by
    have a : 1/2≤T/S := by linarith only [(abs_le.mp t).1,d2]
    linarith only [(le_div_iff₀ sp).mp a,ss]
  have tp : 0<T := by linarith
  have basis := pp.2 z j H η (by omega) hp ev q4 qm ep'.le cap low grh sign
  have u : |U-x|≤δ := by
    dsimp only [U,q]
    rw [lifted_principal (by omega)]
    exact pp.1.1 _ (primorial_pos _) (base_period np nm)
  have v : |V-y|≤δ := by
    dsimp only [V,q]
    rw [lifted_principal (by omega)]
    exact pp.1.2 _ (primorial_pos _) (base_period np nm)
  have e := (perturbed_product dp.le d1 (mul_nonneg cp.le ep'.le) cd dd t u v basis).trans pay
  have eq : T/S*P=(q:ℝ)*classPairs q H M M sign f g/((M:ℝ)^2*S) := by dsimp only [P]; field_simp
  exact eq ▸ e


theorem log_cube_line_limit (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (ε : ℝ) (ep : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, N≤M → ∃ j : ℕ,
      let q := liftedModulus (localCutoff N) j
      let L := Real.log (M:ℝ)
      (q:ℝ)*L^3≤M ∧ (M:ℝ)<2*q*L^3 ∧ ∀ H : ℕ, 0<H → Even H → H≤2*scale N*N →
      GRH q → ∀ sign : Bool,
      |(q:ℝ)*classPairs q H M M sign f g/((M:ℝ)^2*singularSeries H)-
        (∫ u in (0:ℝ)..1,f u)*(∫ u in (0:ℝ)..1,g u)|≤ε := by
  obtain ⟨η,hp,lim⟩ := sharp_near_line_limit f g hf hg ε ep
  have growth := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨K,k⟩ := eventually_atTop.mp (growth.eventually_ge_atTop (max 6 (4/η^2)))
  filter_upwards [near_modulus_power 3,lim,eventually_ge_atTop K] with N choice est nk
  intro M nm
  obtain ⟨j,lo,hi⟩ := choice M nm
  let q := liftedModulus (localCutoff N) j
  let L := Real.log (M:ℝ)
  have big : max 6 (4/η^2)≤L := k M (nk.trans nm)
  have l6 : 6≤L := (le_max_left ..).trans big
  have l1 : 1≤L := by linarith
  have qr : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have qm : q≤M := Nat.cast_le.mp ((le_mul_of_one_le_right qr.le (one_le_pow₀ l1 (n:=3))).trans lo)
  have jq : 0≤6+Real.log (q:ℝ) := by
    have := Real.log_nonneg (Nat.one_le_cast.mpr (NeZero.pos q) : (1:ℝ)≤q)
    linarith
  have top : 6+Real.log (q:ℝ)≤2*L := by linarith only [l6,Real.log_le_log qr (Nat.cast_le.mpr qm)]
  have sq := pow_le_pow_left₀ jq top 2
  have pay : 4≤L*η^2 := (div_le_iff₀ (sq_pos_of_pos hp)).mp ((le_max_right ..).trans big)
  have cap : (q:ℝ)*(6+Real.log q)^2≤η^2*M := calc
    _ ≤ (q:ℝ)*(2*L)^2 := mul_le_mul_of_nonneg_left sq qr.le
    _ ≤ η^2*((q:ℝ)*L^3) := by nlinarith only [mul_le_mul_of_nonneg_left pay (mul_nonneg qr.le (sq_nonneg L))]
    _ ≤ _ := mul_le_mul_of_nonneg_left lo (sq_nonneg η)
  exact ⟨j,lo,hi,fun H a b c => est M H j nm a b c qm cap⟩

#print axioms sharp_near_line_limit
#print axioms log_cube_line_limit
end GoldbachSpectral435.GoldbachSieve
