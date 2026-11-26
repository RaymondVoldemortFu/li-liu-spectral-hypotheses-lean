module
public import ActualLimits
public import ConditionalGoldbach.Proofs.QuantitativeBounds
public import ConditionalGoldbach.Proofs.VariableStripOperators
public import OriginalBounds

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Filter Complex
open scoped Topology InnerProductSpace ENNReal
namespace GoldbachSpectral435.ExistenceLocalization

private lemma weight_le {u a : ℝ} (ua : u ≤ a) (ab : a ≤ beta) (t : ℝ) :
    hardyWeight a beta t ≤ 2 * hardyWeight u beta t := by
  unfold hardyWeight
  by_cases h : t ≤ 0
  · have e := Real.exp_le_exp.mpr (show 2*a*t ≤ 2*u*t by nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ua) h])
    linarith [Real.exp_pos (2*beta*t),Real.exp_pos (2*u*t)]
  · have e := Real.exp_le_exp.mpr (show 2*a*t ≤ 2*beta*t by nlinarith [mul_nonneg (sub_nonneg.mpr ab) (le_of_not_ge h)])
    linarith [Real.exp_pos (2*u*t)]

lemma measure_le {u a : ℝ} (ua : u ≤ a) (ab : a ≤ beta) :
    hardyMeasure a beta ≤ (2 : ℝ≥0∞) • hardyMeasure u beta := by
  unfold hardyMeasure
  rw [← withDensity_smul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
  apply withDensity_mono
  apply Eventually.of_forall
  intro t
  have e := ENNReal.ofReal_le_ofReal (weight_le ua ab t)
  simpa [Pi.smul_apply,ENNReal.ofReal_mul] using e

def restrictStrip {u a : ℝ} (ua : u ≤ a) (ab : a ≤ beta) :
    HardySpace u beta →L[ℂ] HardySpace a beta := by
  let J : HardySpace u beta →L[ℝ] HardySpace a beta :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (measure_le ua ab)
  have aeJ (f : HardySpace u beta) : J f =ᵐ[hardyMeasure a beta] f :=
    Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f
  exact { toFun := J
          map_add' := J.map_add
          map_smul' := fun c f => by
            apply Lp.ext
            have ac := Measure.absolutelyContinuous_of_le_smul (measure_le ua ab)
            filter_upwards [aeJ (c • f),aeJ f,Lp.coeFn_smul c (J f),ac.ae_eq (Lp.coeFn_smul c f)] with t h1 h2 h3 h4
            simpa only [RingHom.id_apply] using h1.trans (h4.trans (by simpa only [Pi.smul_apply,h2] using h3.symm))
          cont := J.continuous }

lemma restrict_ae {u a : ℝ} (ua : u ≤ a) (ab : a ≤ beta) (f : HardySpace u beta) :
    restrictStrip ua ab f =ᵐ[hardyMeasure a beta] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (measure_le ua ab) f

private lemma restrict_values {u a : ℝ} (ua : u ≤ a) (ab : a ≤ beta) (f : HardySpace u beta) (s : ℂ) :
    fourierLaplace (restrictStrip ua ab f) s = fourierLaplace f s := by
  unfold fourierLaplace
  congr 1
  apply integral_congr_ae
  filter_upwards [(volume_absolutelyContinuous_hardyMeasure a beta).ae_eq (restrict_ae ua ab f)] with t eq
  exact congrArg (fun w : ℂ => w * Complex.exp (s*t)) eq

private lemma adjoint_eval {u a : ℝ} (ua : u ≤ a) (ab : a < beta) {s : ℂ} (hs : s ∈ strip a beta) :
    (restrictStrip ua ab.le).adjoint (evaluationVector s) = (evaluationVector s : HardySpace u beta) := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hs' : s ∈ strip u beta := ⟨ua.trans_lt hs.1,hs.2⟩
  exact ((evaluationVector_spec hs _).symm.trans (restrict_values ua ab.le f s)).trans (evaluationVector_spec hs' f)

private lemma vector_ext {a : ℝ} (ab : a < beta) (x y : HardySpace a beta)
    (e : ∀ s ∈ strip a beta, paperInner x (evaluationVector s) = paperInner y (evaluationVector s)) :
    x=y := by
  exact fourierLaplace_injective_strip ab x y fun s hs => (evaluationVector_spec hs _).trans
    ((e s hs).trans (evaluationVector_spec hs _).symm)

/-- Restriction compresses two operators with the same interior kernel. -/
theorem compression_of_entries {u a : ℝ} (ua : u≤a) (ab : a<beta)
    (A : HardySpace a beta →L[ℂ] HardySpace a beta)
    (T : HardySpace u beta →L[ℂ] HardySpace u beta)
    (same : ∀ s z : ℂ, s∈strip a beta → z∈strip a beta →
      paperInner (A (evaluationVector z)) (evaluationVector s) =
      paperInner (T (evaluationVector z)) (evaluationVector s)) :
    A = (restrictStrip ua ab.le).comp (T.comp (restrictStrip ua ab.le).adjoint) := by
  let B := (restrictStrip ua ab.le).comp (T.comp (restrictStrip ua ab.le).adjoint)
  have entry (s z : ℂ) (hs : s ∈ strip a beta) (hz : z ∈ strip a beta) :
      paperInner (A (evaluationVector z)) (evaluationVector s) = paperInner (B (evaluationVector z)) (evaluationVector s) := by
    dsimp only [B,ContinuousLinearMap.comp_apply]
    rw [adjoint_eval ua ab hz]
    conv_rhs => rw [← evaluationVector_spec hs,restrict_values]
    rw [evaluationVector_spec (show s ∈ strip u beta from ⟨ua.trans_lt hs.1,hs.2⟩)]
    exact same s z hs hz
  have vals (z : ℂ) (hz : z ∈ strip a beta) : A (evaluationVector z) = B (evaluationVector z) :=
    vector_ext ab _ _ fun s hs => entry s z hs hz
  change A = B
  apply ContinuousLinearMap.ext
  intro x
  apply vector_ext ab
  intro z hz
  have adjs : A.adjoint (evaluationVector z) = B.adjoint (evaluationVector z) := by
    apply vector_ext ab
    intro s hs
    simp only [paperInner,ContinuousLinearMap.adjoint_inner_right,vals s hs]
  simp only [paperInner,← ContinuousLinearMap.adjoint_inner_left,adjs]

/-- Exact comparison of the *same* arithmetic residual on two Hardy strips. -/
theorem exact_compression {u a : ℝ} (up : 0 < u) (ua : u ≤ a) (ab : a < beta)
    (N : ℕ) [NeZero N] (four : 4 ≤ N) (g : GRH N) :
    residualOperator ab N =
      (restrictStrip ua ab.le).comp ((residualOperator (ua.trans_lt ab) N).comp (restrictStrip ua ab.le).adjoint) := by
  apply compression_of_entries ua ab
  intro s z hs hz
  exact (residualOperator_pairing_at a N (up.trans_le ua) four g ab s z hs hz).symm.trans
    (residualOperator_pairing_at u N up four g (ua.trans_lt ab) s z ⟨ua.trans_lt hs.1,hs.2⟩ ⟨ua.trans_lt hz.1,hz.2⟩)

private lemma far_weight {u a L t : ℝ} (ua : u ≤ a) (ab : a ≤ beta) (hL : 0 ≤ L) (ht : t ≤ -L) :
    hardyWeight a beta t ≤ (2 * Real.exp (-2*(a-u)*L)) * hardyWeight u beta t := by
  have t0 : t ≤ 0 := by linarith
  have e1 : Real.exp (2*a*t) ≤ Real.exp (-2*(a-u)*L) * Real.exp (2*u*t) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith only [mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr ua)]
  have e2 := Real.exp_le_exp.mpr (show 2*beta*t ≤ 2*a*t by
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ab) t0])
  unfold hardyWeight
  nlinarith only [e1,e2,mul_pos (Real.exp_pos (-2*(a-u)*L)) (Real.exp_pos (2*beta*t))]

lemma restrict_tail {u a L : ℝ} (ua : u ≤ a) (ab : a ≤ beta) (hL : 0 ≤ L)
    (v : HardySpace u beta) :
    (∫ t in Iic (-L), ‖restrictStrip ua ab v t‖^2 * hardyWeight a beta t) ≤
      (2*Real.exp (-2*(a-u)*L))*‖v‖^2 := by
  let K := 2*Real.exp (-2*(a-u)*L)
  have integr := (hardySpace_integrable_weighted_sq v).const_mul K
  have ae := (volume_absolutelyContinuous_hardyMeasure a beta).ae_eq (restrict_ae ua ab v)
  calc
    _ ≤ ∫ t in Iic (-L), K*(‖v t‖^2*hardyWeight u beta t) := by
      apply integral_mono_ae (hardySpace_integrable_weighted_sq _).integrableOn integr.integrableOn
      filter_upwards [ae_restrict_of_ae ae,ae_restrict_mem measurableSet_Iic] with t eq ht
      rw [eq]
      exact (mul_le_mul_of_nonneg_left (far_weight ua ab hL ht) (sq_nonneg _)).trans_eq (by dsimp [K]; ring)
    _ ≤ ∫ t, K*(‖v t‖^2*hardyWeight u beta t) := setIntegral_le_integral integr
      (Eventually.of_forall (fun t => by dsimp [K]; have := hardyWeight_pos u beta t; positivity))
    _ = _ := by rw [integral_const_mul,← hardySpace_norm_sq_integral]

lemma restrict_norm {u a : ℝ} (ua : u ≤ a) (ab : a ≤ beta) :
    ‖restrictStrip ua ab‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  have ae := (volume_absolutelyContinuous_hardyMeasure a beta).ae_eq (restrict_ae ua ab v)
  have h : ‖restrictStrip ua ab v‖^2 ≤ 2*‖v‖^2 := by
    rw [hardySpace_norm_sq_integral,hardySpace_norm_sq_integral,← integral_const_mul]
    apply integral_mono_ae (hardySpace_integrable_weighted_sq _) ((hardySpace_integrable_weighted_sq _).const_mul _)
    filter_upwards [ae] with t eq
    rw [eq]
    exact (mul_le_mul_of_nonneg_left (weight_le ua ab t) (sq_nonneg _)).trans_eq (by ring)
  nlinarith only [h,norm_nonneg v,sq_nonneg ‖v‖,norm_nonneg (restrictStrip ua ab v)]

/-- Uniform bound on the entire far-output block, including arbitrary inputs. -/
theorem operator_tail {u a L : ℝ} (up : 0 < u) (ua : u ≤ a) (ab : a < beta) (hL : 0 ≤ L)
    (N : ℕ) [NeZero N] (four : 4 ≤ N) (g : GRH N) (x : HardySpace a beta) :
    (∫ t in Iic (-L), ‖(residualOperator ab N x) t‖^2 * hardyWeight a beta t) ≤
      8 * Real.exp (-2*(a-u)*L) * ‖residualOperator (ua.trans_lt ab) N‖^2 * ‖x‖^2 := by
  let J := restrictStrip ua ab.le
  let T := residualOperator (ua.trans_lt ab) N
  rw [exact_compression up ua ab N four g]
  have op : ‖J.adjoint x‖ ≤ 2 * ‖x‖ := (J.adjoint.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (by simpa [J] using restrict_norm ua ab.le) (norm_nonneg _))
  have h := (T.le_opNorm (J.adjoint x)).trans (mul_le_mul_of_nonneg_left op (norm_nonneg _))
  exact (restrict_tail ua ab.le hL (T (J.adjoint x))).trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) h 2) (by positivity : 0 ≤ 2*Real.exp (-2*(a-u)*L))).trans_eq (by dsimp [T]; ring))
/-- All unit input directions have negligible squared output energy beyond
physical scale exp(8 log N log log N), uniformly in the eligible modulus. -/
theorem uniform_far_energy :
    ∃ D : ℝ, 0<D ∧ ∀ N : ℕ, ∀ [NeZero N], Even N → Real.exp 10 < (N:ℝ) → GRH N →
      ∀ (ha : alpha N < beta) (x : HardySpace (alpha N) beta),
      (∫ t in Iic (-(8*Real.log N*Real.log (Real.log N))),
        ‖(residualOperator ha N x) t‖^2 * hardyWeight (alpha N) beta t) ≤
          D / Real.log N^4 * ‖x‖^2 := by
  obtain ⟨C,cp,bound⟩ := residualOperator_uniform_hs_bound
  refine ⟨200*C^2,by positivity,?_⟩
  intro N inst he large g ha x
  let l := Real.log (N:ℝ)
  have pos := (large_parameters large).2.1
  have lp : 0 < l := pos
  have big : 10 < l := (Real.lt_log_iff_exp_lt (by exact_mod_cast (NeZero.pos N))).mpr large
  let u := (2*l)⁻¹
  have up : 0 < u := by dsimp [u]; positivity
  have ua : u ≤ alpha N := by
    change (2*l)⁻¹ ≤ 1/l
    rw [← one_div]
    apply one_div_le_one_div_of_le lp
    linarith
  have ul := (bound N inst he large g u up (ua.trans_lt ha)).2
  have norm : ‖residualOperator (ua.trans_lt ha) N‖ ≤ 5*C*l^2 := by
    apply ul.1.trans (ul.2.trans_eq _)
    dsimp [u,l]
    rw [inv_inv]
    ring
  have ll : 0 ≤ Real.log l := Real.log_nonneg (by linarith)
  let L := 8*l*Real.log l
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have eqp : -2*(alpha N-u)*L = -(8*Real.log l) := by
    change -2*(1/l-(2*l)⁻¹)*(8*l*Real.log l) = _
    field_simp
    ring
  have weight : Real.exp (-2*(alpha N-u)*L) = (l^8)⁻¹ := by
    rw [eqp,Real.exp_neg]
    have power := Real.exp_nat_mul (Real.log l) 8
    simpa only [Nat.cast_ofNat, Real.exp_log lp] using congrArg Inv.inv power
  have tail := operator_tail up ua ha hL N (large_parameters large).1 g x
  rw [weight] at tail
  apply tail.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ 8*(l^8)⁻¹*(5*C*l^2)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) norm 2) (by positivity)
    _ = 200*C^2/l^4 := by field_simp; ring

open GoldbachSpectral435

/-- Output energy remaining after the uniform far-tail estimate. -/
def coreEnergy (N : ℕ) [NeZero N] (ha : alpha N < beta) (x : HardySpace (alpha N) beta) : ℝ :=
  ∫ t in Ioi (-(8*Real.log N*Real.log (Real.log N))),
      ‖(residualOperator ha N x) t‖^2 * hardyWeight (alpha N) beta t

theorem existence_iff_core : (∃ h, HypothesisS h) ↔
    ∀ ε : ℝ, 0 < ε → EvenEventually (fun N => ∀ [NeZero N], GRH N →
      ∀ (ha : alpha N < beta) (x : HardySpace (alpha N) beta),
        coreEnergy N ha x ≤ (ε*singularSeries N)^2 * ‖x‖^2) := by
  rw [some_actual_S_iff]
  constructor
  · intro limit ε ep
    obtain ⟨K,small⟩ := limit ε ep
    refine ⟨K,fun N hn he inst g ha x => ?_⟩
    have h := small N hn he
    change eligibleNorm N ≤ ε * singularSeries N at h
    rw [eligibleNorm_spec N ha g] at h
    unfold coreEnergy
    calc
      _ ≤ ∫ t, ‖(residualOperator ha N x) t‖^2 * hardyWeight (alpha N) beta t :=
        setIntegral_le_integral (hardySpace_integrable_weighted_sq _)
          (Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (hardyWeight_pos _ _ t).le))
      _ = _ := (hardySpace_norm_sq_integral _).symm
      _ ≤ ((ε*singularSeries N)*‖x‖)^2 := pow_le_pow_left₀ (norm_nonneg _)
        (((residualOperator ha N).le_opNorm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))) 2
      _ = _ := mul_pow _ _ _
  · intro core ε ep
    obtain ⟨D,dp,far⟩ := uniform_far_energy
    obtain ⟨K,test⟩ := (core (ε/2) (by positivity)).and evenEventually_large
    have logs := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have decay : Tendsto (fun n : ℕ => D / (Real.log n)^4) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 4 ≠ 0)).comp logs)
    obtain ⟨J,small⟩ := eventually_atTop.mp (decay.eventually_lt_const (show 0 < (ε/2)^2 by positivity))
    refine ⟨max K J, fun N hn he => ?_⟩
    obtain ⟨cut,big⟩ := test N (by omega) he
    obtain ⟨four,_,ha⟩ := large_parameters big
    let inst : NeZero N := ⟨by omega⟩
    have ss : 1 ≤ singularSeries N := by rw [original_series]; exact GoldbachSpectral.singular_lower N
    by_cases g : GRH N
    · rw [eligibleNorm_spec N ha g]
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro x
      let f := fun t : ℝ => ‖(residualOperator ha N x) t‖^2 * hardyWeight (alpha N) beta t
      have intg := hardySpace_integrable_weighted_sq (residualOperator ha N x)
      have both := integral_add_compl (s := Iic (-(8*Real.log N*Real.log (Real.log N)))) measurableSet_Iic intg
      have right := cut g ha x
      have left := far N he big g ha x
      have comp : ‖residualOperator ha N x‖^2 ≤
          (D/Real.log N^4 + ((ε/2)*singularSeries N)^2)*‖x‖^2 := by
        rw [hardySpace_norm_sq_integral,← both,compl_Iic,add_mul]
        exact add_le_add left right
      have cap := small N (by omega)
      have es : ε/2 ≤ ε/2 * singularSeries N := by nlinarith only [mul_le_mul_of_nonneg_left ss (by positivity : 0≤ε/2)]
      have step := (le_of_lt cap).trans (pow_le_pow_left₀ (by positivity) es 2)
      have C : (D/Real.log N^4+((ε/2)*singularSeries N)^2) ≤ (ε*singularSeries N)^2 := by
        nlinarith only [step,sq_nonneg (ε*singularSeries N)]
      have sqr := comp.trans (mul_le_mul_of_nonneg_right C (sq_nonneg _))
      rw [← mul_pow] at sqr
      exact le_of_sq_le_sq sqr (by positivity)
    · simp [eligibleNorm,g,mul_nonneg ep.le (singularSeries_pos N).le]

#print axioms existence_iff_core
#print axioms exact_compression
#print axioms uniform_far_energy
end GoldbachSpectral435.ExistenceLocalization
