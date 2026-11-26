module
public import ExistenceLocalization
public import LocalPrimeForm
public import ModelDecay
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! Compression of the full residual above its critical left boundary. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.StripDecay
open GoldbachSpectral435.ExistenceLocalization

private def cut {a : ℝ} (S : Set ℝ) (hS : MeasurableSet S) (f : HardySpace a beta) :
    HardySpace a beta := ((Lp.memLp f).indicator hS.nullMeasurableSet).toLp _

private lemma cut_ae {a : ℝ} (S : Set ℝ) (hS : MeasurableSet S) (f : HardySpace a beta) :
    cut S hS f =ᵐ[hardyMeasure a beta] S.indicator f := ((Lp.memLp f).indicator hS.nullMeasurableSet).coeFn_toLp

private lemma cut_norm {a : ℝ} (S : Set ℝ) (hS : MeasurableSet S) (f : HardySpace a beta) :
    ‖cut S hS f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cut_ae S hS f] with t ht
  rw [ht]
  exact norm_indicator_le_norm_self (f:ℝ→ℂ) t

private lemma cut_inner {a : ℝ} (S : Set ℝ) (hS : MeasurableSet S) (f : HardySpace a beta) :
    inner ℂ (cut S hS f) f=inner ℂ (cut S hS f) (cut S hS f) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cut_ae S hS f] with t ht
  by_cases hm : t∈S <;> simp [ht,hm]

private lemma restricted_far {u a L : ℝ} (ua : u≤a) (ab : a≤beta) (lp : 0≤L)
    (v : HardySpace u beta) (supp : ∀ᵐ t ∂hardyMeasure u beta, -L<t → v t=0) :
    ‖restrictStrip ua ab v‖ ≤ 2*Real.exp (-(a-u)*L)*‖v‖ := by
  let J := restrictStrip ua ab
  have r := restrict_tail ua ab lp v
  have su : ∀ᵐ t ∂hardyMeasure a beta, -L<t → v t=0 :=
    (Measure.absolutelyContinuous_of_le_smul (measure_le ua ab)).ae_le supp
  have ae : ∀ᵐ t : ℝ, (-L<t → v t=0) ∧ J v t=v t :=
    (volume_absolutelyContinuous_hardyMeasure a beta).ae_le (su.and (restrict_ae ua ab v))
  have eq : ‖J v‖^2=∫ t in Iic (-L), ‖J v t‖^2*hardyWeight a beta t := by
    rw [hardySpace_norm_sq_integral,← integral_indicator measurableSet_Iic]
    apply integral_congr_ae
    filter_upwards [ae] with t h
    by_cases m : t∈Iic (-L)
    · rw [indicator_of_mem m]
    · have z : J v t=0 := h.2.trans (h.1 (lt_of_not_ge m))
      simp [z,indicator_of_notMem m]
  have power : Real.exp (-2*(a-u)*L) = Real.exp (-(a-u)*L)^2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [eq]
  rw [power] at r
  exact r.trans (by nlinarith only [mul_nonneg (sq_nonneg (Real.exp (-(a-u)*L))) (sq_nonneg ‖v‖)])

private lemma adjoint_far {u a L : ℝ} (ua : u≤a) (ab : a≤beta) (lp : 0≤L)
    (f : HardySpace a beta) :
    ‖cut (Iic (-L)) measurableSet_Iic ((restrictStrip ua ab).adjoint f)‖ ≤
      2*Real.exp (-(a-u)*L)*‖f‖ := by
  let J := restrictStrip ua ab
  let z := J.adjoint f
  let v := cut (Iic (-L)) measurableSet_Iic z
  have supp : ∀ᵐ t ∂hardyMeasure u beta, -L<t → v t=0 := by
    filter_upwards [cut_ae (Iic (-L)) measurableSet_Iic z] with t h ht
    exact h.trans (indicator_of_notMem (show t∉Iic (-L) from not_le.mpr ht) _)
  have pair : inner ℂ v v=inner ℂ (J v) f := by
    rw [← cut_inner (Iic (-L)) measurableSet_Iic z]
    exact ContinuousLinearMap.adjoint_inner_right J v f
  have bound := (norm_inner_le_norm (𝕜:=ℂ) (J v) f).trans (mul_le_mul_of_nonneg_right
    (restricted_far ua ab lp v supp) (norm_nonneg _))
  rw [← pair,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_norm] at bound
  change ‖v‖ ≤ _
  rcases (norm_nonneg v).eq_or_lt with h|h
  · rw [← h]; positivity
  · apply le_of_mul_le_mul_right _ h
    nlinarith only [bound]

private lemma model_compression {u a : ℝ} (up : 0<u) (ua : u≤a) (ha : a<beta)
    (N : ℕ) [NeZero N] :
    modelOperator ha N=(restrictStrip ua ha.le).comp
      ((modelOperator (ua.trans_lt ha) N).comp (restrictStrip ua ha.le).adjoint) := by
  obtain ⟨B,bp,G⟩ := continuedModel_uniform_power_bound
  have entry {v : ℝ} (vp : 0<v) (vb : v<beta) (s z : ℂ) (hs : s∈strip v beta) (hz : z∈strip v beta) :
      weightedAnalyticKernel (continuedModel N) s z =
      paperInner (modelOperator vb N (evaluationVector z)) (evaluationVector s) := by
    obtain ⟨hk,hc⟩ := weightedAnalyticKernel_inputs_at vp vb (continuedModel N)
      (continuedModel_differentiableOn N (NeZero.pos N)) _ (by positivity)
      (G v vp vb N (NeZero.pos N))
    have herm : HermitianKernel (weightedAnalyticKernel (continuedModel N)) := by
      apply weightedAnalyticKernel_hermitian
      intro s z
      rw [continuedModel_conj,Complex.conj_conj,continuedModel_symmetric]
    exact kernelOperator_pairing_of_hardyColumns vb N _ herm hk hc s z hs hz
  apply compression_of_entries ua ha
  intro s z hs hz
  exact (entry (up.trans_le ua) ha s z hs hz).symm.trans
    (entry up (ua.trans_lt ha) s z ⟨ua.trans_lt hs.1,hs.2⟩ ⟨ua.trans_lt hz.1,hz.2⟩)

private lemma form_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (v z : H) : ‖inner ℂ v (A z)‖ ≤ ‖A‖*‖v‖*‖z‖ :=
  (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left (A.le_opNorm z) (norm_nonneg v)).trans_eq (by ring))

private lemma compressed_form {u a L ε : ℝ} (ua : u≤a) (ab : a≤beta) (lp : 0≤L) (ep : 0≤ε)
    (A : HardySpace u beta →L[ℂ] HardySpace u beta)
    (near : ∀ v : HardySpace u beta, (∀ᵐ t ∂hardyMeasure u beta, t≤ -L → v t=0) →
      ‖inner ℂ v (A v)‖≤ε*‖v‖^2) (f : HardySpace a beta) :
    let J := restrictStrip ua ab
    ‖inner ℂ (J.adjoint f) (A (J.adjoint f))‖ ≤
      (4*ε+8*‖A‖*Real.exp (-(a-u)*L))*‖f‖^2 := by
  intro J
  let z := J.adjoint f
  let p := cut (Ioi (-L)) measurableSet_Ioi z
  let q := cut (Iic (-L)) measurableSet_Iic z
  let E := Real.exp (-(a-u)*L)
  have e0 : 0≤E := (Real.exp_pos _).le
  have zn : ‖z‖≤2*‖f‖ := (J.adjoint.le_opNorm _).trans (mul_le_mul_of_nonneg_right
    (by simpa [J] using restrict_norm ua ab) (norm_nonneg _))
  have pn : ‖p‖≤2*‖f‖ := (cut_norm _ _ _).trans zn
  have qn : ‖q‖≤2*E*‖f‖ := adjoint_far ua ab lp f
  have de : p+q=z := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add p q,cut_ae (Ioi (-L)) measurableSet_Ioi z,
      cut_ae (Iic (-L)) measurableSet_Iic z] with t a b c
    rw [a,Pi.add_apply]
    change p t+q t=z t
    rw [show p t=_ from b,show q t=_ from c]
    by_cases h : -L<t
    · simp [h,not_le.mpr h]
    · simp [h,le_of_not_gt h]
  have ps : ∀ᵐ t ∂hardyMeasure u beta, t≤ -L → p t=0 := by
    filter_upwards [cut_ae (Ioi (-L)) measurableSet_Ioi z] with t e ht
    exact e.trans (indicator_of_notMem (show t∉Ioi (-L) from not_lt.mpr ht) _)
  have identity : inner ℂ z (A z) = inner ℂ p (A p)+inner ℂ p (A q)+inner ℂ q (A z) := by
    conv_lhs => lhs; rw [← de]
    rw [inner_add_left]
    conv_lhs => lhs; rhs; rw [← de,map_add]
    rw [inner_add_right]
  have b1 := (near p ps).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg p) pn 2) ep)
  have b2 := (form_bound A p q).trans (mul_le_mul (mul_le_mul_of_nonneg_left pn (norm_nonneg _))
    qn (norm_nonneg _) (by positivity))
  have b3 := (form_bound A q z).trans (mul_le_mul (mul_le_mul_of_nonneg_left qn (norm_nonneg _))
    zn (norm_nonneg _) (by positivity))
  change ‖inner ℂ z (A z)‖≤_
  rw [identity]
  calc
    _ ≤ ‖inner ℂ p (A p)+inner ℂ p (A q)‖+‖inner ℂ q (A z)‖ := norm_add_le _ _
    _ ≤ (‖inner ℂ p (A p)‖+‖inner ℂ p (A q)‖)+‖inner ℂ q (A z)‖ :=
      add_le_add_left (norm_add_le _ _) _
    _ ≤ _ := (add_le_add (add_le_add b1 b2) b3).trans_eq (by dsimp [E]; ring)

private lemma norm_of_forms {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) (symm : IsSelfAdjoint A) {B : ℝ} (nonneg : 0≤B)
    (cap : ∀ x, ‖inner ℂ x (A x)‖ ≤ B*‖x‖^2) : ‖A‖≤B := by
  rw [A.norm_eq_iSup_rayleighQuotient symm.isSymmetric]
  apply ciSup_le
  intro x
  by_cases zero : x=0
  · simpa [zero] using nonneg
  change |(inner ℂ (A x) x).re / ‖x‖^2|≤B
  rw [abs_div,abs_of_nonneg (sq_nonneg ‖x‖)]
  apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr zero) _)).mpr
  apply (Complex.abs_re_le_norm _).trans
  exact (congrArg norm (symm.isSymmetric x x)).le.trans (cap x)

/-- Operator norm of the complete residual on a variable left boundary.
The short arithmetic form vanishes exactly. The two terms bound the
complementary block and the model. -/
theorem residual_strip_decay :
    ∃ C B : ℝ, 0<C ∧ 0<B ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
    Real.exp 10<(N:ℝ) → GRH N → ∀ {a : ℝ}, alpha N≤a → ∀ (ha : a<beta) (Y : ℕ),
    0<Y → 2*Y≤N →
    ‖residualOperator ha N‖ ≤ C*(Real.log N)^2*Real.exp (-(a-alpha N)*Real.log Y)+
      B*singularSeries N*(N:ℝ)^(-2*a)*(a⁻¹)^2 := by
  obtain ⟨C,cp,op⟩ := residualOperator_uniform_hs_bound
  obtain ⟨D,dp,model⟩ := modelOperator_uniform_hs_bound
  obtain ⟨B,bp,decay⟩ := ModelDecay.operator_decay
  refine ⟨8*(2*C+D),B,by positivity,bp,?_⟩
  intro N inst he lar g a ua ha Y yp ys
  obtain ⟨four,lp,hu⟩ := large_parameters lar
  have up := large_alpha_pos lar
  have ap := up.trans_le ua
  let u := alpha N
  let A := residualOperator hu N+modelOperator hu N
  let J := restrictStrip ua ha.le
  let L := Real.log (N:ℝ)
  let E := Real.exp (-(a-u)*Real.log Y)
  let M := B*singularSeries N*(N:ℝ)^(-2*a)*(a⁻¹)^2
  have sp := singularSeries_pos N
  have ylog := Real.log_nonneg (by exact_mod_cast yp : (1:ℝ)≤Y)
  have lpos : 0<L := lp
  have epos : 0<E := Real.exp_pos _
  have m0 : 0≤M := by dsimp [M]; positivity
  have id : A=arithmeticOperator hu N-diagonalOperator hu N := by
    simp only [A,residualOperator_components_at _ N up four g hu,sub_add_cancel]
  have r := (op N inst he lar g u up hu).2
  have d := model u up hu N inst
  have an : ‖A‖≤(2*C+D)*L^2 := by
    apply (norm_add_le _ _).trans
    have t := add_le_add (r.1.trans r.2) (d.1.norm_le_hsNorm.trans d.2)
    exact t.trans_eq (by simp only [u,alpha,one_div,inv_inv,L]; ring)
  have ma := ((model a ap ha N inst).1.norm_le_hsNorm).trans (decay ap ha N)
  have ad : J.comp (A.comp J.adjoint)=residualOperator ha N+modelOperator ha N := by
    rw [exact_compression up ua ha N four g,model_compression up ua ha N]
    apply ContinuousLinearMap.ext
    intro f
    simp only [A,J,add_apply,ContinuousLinearMap.comp_apply,map_add]
  change ‖residualOperator ha N‖ ≤ 8*(2*C+D)*L^2*E+M
  apply norm_of_forms _ (residualOperator_spec_at a N ap four g ha).2.2.2.1 (by positivity)
  intro f
  have c := compressed_form ua ha.le ylog (le_refl (0:ℝ)) A
    (fun v hv => by rw [id,LocalPrimeForm.short_arithmetic_zero N Y he lar g hu yp ys v hv,norm_zero,zero_mul]) f
  have ae : inner ℂ (J.adjoint f) (A (J.adjoint f)) =
      inner ℂ f ((residualOperator ha N+modelOperator ha N) f) := by
    rw [ContinuousLinearMap.adjoint_inner_left,← ad]
    rfl
  change ‖inner ℂ (J.adjoint f) (A (J.adjoint f))‖≤ (4*0+8*‖A‖*E)*‖f‖^2 at c
  simp only [mul_zero,zero_add] at c
  rw [ae] at c
  have mb : ‖inner ℂ f (modelOperator ha N f)‖≤M*‖f‖^2 :=
    (form_bound _ _ _).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ma
      (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring))
  have algebra : inner ℂ f (residualOperator ha N f) =
      inner ℂ f ((residualOperator ha N+modelOperator ha N) f)-
      inner ℂ f (modelOperator ha N f) := by rw [add_apply,inner_add_right,add_sub_cancel_right]
  rw [algebra]
  apply (norm_sub_le _ _).trans ((add_le_add c mb).trans _)
  have scale := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left an (by norm_num : (0:ℝ)≤8)) epos.le
  calc
    _ ≤ (8*((2*C+D)*L^2)*E)*‖f‖^2+M*‖f‖^2 := by gcongr
    _ = _ := by ring

theorem residual_strip_bound :
    ∃ K C B : ℝ, 0<K ∧ 0<C ∧ 0<B ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
    Real.exp 10<(N:ℝ) → GRH N → ∀ {a : ℝ}, alpha N≤a → ∀ (ha : a<beta) (Y : ℕ),
    0<Y → 2*Y≤N →
    ‖residualOperator ha N‖ ≤ K/(Real.log N)^16+
      C*(Real.log N)^2*Real.exp (-(a-alpha N)*Real.log Y)+
      B*singularSeries N*(N:ℝ)^(-2*a)*(a⁻¹)^2 := by
  obtain ⟨C,B,cp,bp,cap⟩ := residual_strip_decay
  refine ⟨1,C,B,zero_lt_one,cp,bp,?_⟩
  intro N inst he big g a ua ha Y yp ys
  have logp := (large_parameters big).2.1
  exact (cap N inst he big g ua ha Y yp ys).trans (by
    have := div_nonneg (zero_le_one: (0:ℝ)≤1) (pow_nonneg logp.le 16)
    linarith)

/-- A uniform bound down to a moving neighborhood of the original left
boundary. It gives normalized decay whenever a log N - 2 log log N
tends to positive infinity. -/
theorem normalized_exponential_bound :
    ∃ D : ℝ, 0<D ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N → Real.exp 10<(N:ℝ) → GRH N →
    ∀ {a : ℝ}, alpha N≤a → ∀ ha : a<beta,
      ‖residualOperator ha N‖/singularSeries N ≤
        D*(Real.log N^2*Real.exp (-a*Real.log N)) := by
  obtain ⟨C,B,cp,bp,cap⟩ := residual_strip_decay
  let D := 2*Real.exp 1*C+B
  have dpos : 0<D := by dsimp [D]; positivity
  refine ⟨D,dpos,?_⟩
  intro N inst even large g a ua ha
  obtain ⟨Y,eqY⟩ := even
  obtain ⟨four,lp,_⟩ := large_parameters large
  have yp : 0<Y := by omega
  have yr : 0<(Y:ℝ) := by exact_mod_cast yp
  have nr : 0<(N:ℝ) := by exact_mod_cast (NeZero.pos N)
  have alg : (N:ℝ)=2*(Y:ℝ) := by exact_mod_cast (show N=2*Y by omega)
  let L := Real.log (N:ℝ)
  let u := alpha N
  let E := Real.exp (-a*L)
  let S := singularSeries N
  have lp' : 0<L := lp
  have up : 0<u := large_alpha_pos large
  have ap := up.trans_le ua
  have ep : 0<E := Real.exp_pos _
  have sp : 1≤S := (singularSeries_gt_one N).le
  have s0 : 0<S := zero_lt_one.trans_le sp
  have uL : u*L=1 := by change 1/L*L=1; field_simp
  have logs : Real.log (Y:ℝ)=L-Real.log 2 := by
    dsimp only [L]; rw [alg,Real.log_mul (by norm_num) yr.ne']; ring
  have gap : a-u≤1 := by have := ha.le; dsimp [beta] at this; linarith
  have damp : Real.exp (-(a-u)*Real.log Y) ≤ 2*Real.exp 1*E := by
    rw [logs,show -(a-u)*(L-Real.log 2)=(a-u)*Real.log 2+1+(-a*L) by linear_combination uL,
      Real.exp_add,Real.exp_add]
    have small : Real.exp ((a-u)*Real.log 2)≤2 := by
      calc
        _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by
          simpa using mul_le_mul_of_nonneg_right gap (Real.log_nonneg (by norm_num : (1:ℝ)≤2)))
        _ = 2 := Real.exp_log (by norm_num)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right small (Real.exp_pos _).le) ep.le
  have ai : a⁻¹≤L := by
    calc
      _ ≤ u⁻¹ := inv_anti₀ up ua
      _ = _ := by dsimp [u,alpha,L]; simp [one_div]
  have nscale : (N:ℝ)^(-2*a)≤E := by
    rw [Real.rpow_def_of_pos nr]
    apply Real.exp_le_exp.mpr
    change L*(-2*a)≤ -a*L
    nlinarith [mul_nonneg ap.le lp'.le]
  have est := cap N inst ⟨Y,eqY⟩ large g ua ha Y yp (by omega)
  have cros := mul_le_mul_of_nonneg_left damp (show 0≤C*L^2 by positivity)
  have model : B*S*(N:ℝ)^(-2*a)*(a⁻¹)^2 ≤ B*S*E*L^2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left nscale (by positivity))
      (pow_le_pow_left₀ (inv_nonneg.mpr ap.le) ai 2) (sq_nonneg _) (by positivity)
  have crossS := le_mul_of_one_le_left (show 0≤C*L^2*(2*Real.exp 1*E) by positivity) sp
  change ‖residualOperator ha N‖/S ≤ D*(L^2*E)
  apply (div_le_iff₀ s0).mpr
  exact est.trans ((add_le_add (cros.trans crossS) model).trans_eq (by dsimp only [D]; ring))

theorem normalized_strip_bound :
    ∃ D : ℝ, 0<D ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N → Real.exp 10<(N:ℝ) → GRH N →
    ∀ {a : ℝ}, alpha N≤a → ∀ ha : a<beta,
      ‖residualOperator ha N‖/singularSeries N ≤
        D*((Real.log N^16)⁻¹ + Real.log N^2*Real.exp (-a*Real.log N)) := by
  obtain ⟨D,dp,cap⟩ := normalized_exponential_bound
  refine ⟨D,dp,?_⟩
  intro N inst even big g a ua ha
  apply (cap N inst even big g ua ha).trans
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) dp.le

/-- Along every eligible sequence, the entire normalized operator tends
to zero once the left boundary exceeds the indicated logarithmic scale. -/
theorem strip_limit {n : ℕ → ℕ} [∀ k, NeZero (n k)] (ng : Tendsto n atTop atTop)
    (ev : ∀ k, Even (n k)) (g : ∀ k, GRH (n k)) (a : ℕ → ℝ)
    (ha : ∀ k, a k<beta)
    (gap : Tendsto (fun k => a k*Real.log (n k)-2*Real.log (Real.log (n k))) atTop atTop) :
    Tendsto (fun k => ‖residualOperator (ha k) (n k)‖/singularSeries (n k)) atTop (𝓝 0) := by
  obtain ⟨D,_,cap⟩ := normalized_strip_bound
  let L := fun k => Real.log (n k)
  have lg : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp ng)
  have inv : Tendsto (fun k => ((L k)^16)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : 16≠0)).comp lg)
  have ex := Real.tendsto_exp_neg_atTop_nhds_zero.comp gap
  have rate := (inv.add ex).const_mul D
  rw [add_zero,mul_zero] at rate
  apply squeeze_zero' _ _ rate
  · exact Eventually.of_forall (fun k => div_nonneg (norm_nonneg _) (singularSeries_pos _).le)
  filter_upwards [lg.eventually_ge_atTop 11,gap.eventually_ge_atTop 1] with k big room
  have yn : 0<(n k:ℝ) := by exact_mod_cast NeZero.pos (n k)
  have lar : Real.exp 10<(n k:ℝ) := (Real.lt_log_iff_exp_lt yn).mp (by change 10<L k; linarith)
  have pos : 0<L k := by linarith
  have llog : 0≤Real.log (L k) := Real.log_nonneg (by linarith)
  have wide : alpha (n k)≤a k := by
    change 1/L k≤a k
    apply (div_le_iff₀ pos).mpr
    change 1 ≤ a k*L k-2*Real.log (L k) at room
    linarith
  apply (cap _ inferInstance (ev k) lar (g k) wide (ha k)).trans_eq
  change D*(((L k)^16)⁻¹+(L k)^2*Real.exp (-a k*L k)) =
    D*(((L k)^16)⁻¹+Real.exp (-(a k*L k-2*Real.log (L k))))
  rw [show -(a k*L k-2*Real.log (L k))=2*Real.log (L k)+(-a k*L k) by ring,
    Real.exp_add,show 2*Real.log (L k)=Real.log ((L k)^2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by positivity)]

#print axioms strip_limit
#print axioms normalized_strip_bound
#print axioms residual_strip_bound
end GoldbachSpectral435.StripDecay
