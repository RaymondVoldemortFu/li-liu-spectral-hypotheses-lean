module
public import KernelEnvelope
public import SingleScaleCriterion
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Square integrability of the normalized cumulative kernel, including
the singular endpoint. Only the size of its integral needs estimating. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Filter
namespace GoldbachSpectral435.CumulativeKernel
open GoldbachPrimitive

private lemma inverse_weight (M : ℕ) (mp : 0<M) (a : ℝ) (ap : 0≤a) (ab : a≤beta)
    (u : ℝ) (up : 0<u) (u1 : u≤1) :
    (energyWeight M a u)⁻¹≤2*u^(-(1/4:ℝ)) := by
  let x := (M:ℝ)*u
  have xp : 0<x := mul_pos (by exact_mod_cast mp) up
  have ux : u≤x := le_mul_of_one_le_left up.le (by exact_mod_cast mp)
  have cmp (b : ℝ) (bp : 0≤b) (bb : b≤beta) : x^(-2*b)≤u^(-(1/4:ℝ)) := by
    apply (Real.rpow_le_rpow_of_nonpos up ux (by linarith : -2*b≤0)).trans
    apply Real.rpow_le_rpow_of_exponent_ge up u1
    norm_num [beta] at bb
    linarith
  unfold energyWeight
  rw [max_eq_left up.le,inv_div,add_div]
  change 1/x^(2*beta)+x^(2*(beta-a))/x^(2*beta)≤_
  rw [one_div,← Real.rpow_neg xp.le,← Real.rpow_sub xp,
    show -(2*beta)= -2*beta by ring,show 2*(beta-a)-2*beta= -2*a by ring]
  linarith only [cmp a ap ab,cmp beta (by norm_num [beta]) le_rfl]

private lemma factor_squared (M : ℕ) (mp : 0<M) (a u : ℝ) (up : 0<u) :
    0<energyWeight M a u ∧ (factor M a u)^2=energyWeight M a u*(edgeWeight u)^2 := by
  have pos : 0<energyWeight M a u := by rw [weight_eq mp up]; positivity
  refine ⟨pos,?_⟩
  rw [factor,max_eq_left up.le,Real.sq_sqrt (by positivity),edgeWeight,mul_pow,Real.sq_sqrt up.le]
  ring

/-- Independent of any prime asymptotic, every finite dilation has a
well-defined square-integrable normalized kernel on the entire square. -/
theorem kernel_memLp (N k : ℕ) (np : 0<N) (kp : 0<k) (ap : 0≤alpha N) (ab : alpha N<beta) :
    MemLp (normalizedKernel N k) 2 thresholds := by
  let M := k*N
  have mp : 0<M := Nat.mul_pos kp np
  let a := alpha N
  have fc : Continuous (factor M a) := Real.continuous_sqrt.comp
    ((energyWeight_continuous M ab).mul ((continuous_id.max continuous_const).pow 3))
  obtain ⟨meas,C,cp,cap⟩ := signed_control N k kp
  have mk : Measurable (normalizedKernel N k) :=
    meas.div ((fc.measurable.comp measurable_fst).mul (fc.measurable.comp measurable_snd))
  let r := fun u : ℝ => u^(-(1/4:ℝ))
  have ri : Integrable r unitMeasure := (intervalIntegral.intervalIntegrable_rpow'
    (a:=(0:ℝ)) (b:=(1:ℝ)) (by norm_num : -1< -(1/4:ℝ))).1
  apply (memLp_two_iff_integrable_sq_norm mk.aestronglyMeasurable).mpr
  apply ((ri.mul_prod ri).const_mul (4*C^2)).mono' (mk.norm.pow_const 2).aestronglyMeasurable
  have unit : ∀ᵐ x ∂unitMeasure, x∈Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  filter_upwards [(Measure.quasiMeasurePreserving_fst (ν:=unitMeasure)).ae unit,
    (Measure.quasiMeasurePreserving_snd (μ:=unitMeasure)).ae unit] with p hs ht
  let s := p.1
  let t := p.2
  have sp : 0<s := hs.1
  have tp : 0<t := ht.1
  have rs : 0≤r s := Real.rpow_nonneg sp.le _
  obtain ⟨ws,fs⟩ := factor_squared M mp a s sp
  obtain ⟨wt,ft⟩ := factor_squared M mp a t tp
  have scale : (C*(edgeWeight s*edgeWeight t))^2/(factor M a s*factor M a t)^2 =
      C^2*((energyWeight M a s)⁻¹*(energyWeight M a t)⁻¹) := by
    have es := (edge_pos sp).ne'
    have et := (edge_pos tp).ne'
    rw [mul_pow (factor M a s),fs,ft]
    field_simp
  have sq := pow_le_pow_left₀ (abs_nonneg _) (cap s t sp tp) 2
  rw [sq_abs] at sq
  change ‖‖signedKernel N k p/(factor M a s*factor M a t)‖^2‖≤4*C^2*(r s*r t)
  rw [Real.norm_of_nonneg (sq_nonneg _),Real.norm_eq_abs,sq_abs,div_pow]
  apply (div_le_div_of_nonneg_right sq (sq_nonneg _)).trans
  rw [scale]
  have invs := inverse_weight M mp a ap ab.le s sp hs.2
  have invt := inverse_weight M mp a ap ab.le t tp ht.2
  have pr := mul_le_mul invs invt (inv_nonneg.mpr wt.le) (mul_nonneg (by norm_num : (0:ℝ)≤2) rs)
  exact (mul_le_mul_of_nonneg_left pr (sq_nonneg C)).trans_eq (by dsimp [r]; ring)

/-- The single-scale square-integral criterion has only one analytic
premise, a numerical rate for the explicit integral itself. -/
theorem exists_of_kernel_size (decay : ∀ ε : ℝ, 0<ε → EvenEventually (fun N => ∀ [NeZero N], GRH N →
    2*Real.pi*kernelSize N (PhysicalTests.scale N)≤ε*singularSeries N)) :
    ∃ h, HypothesisS h := by
  apply PhysicalTests.exists_of_single_kernel_decay
  intro ε ep
  obtain ⟨K,b⟩ := (decay ε ep).and evenEventually_large
  refine ⟨K,fun N hn he inst grh => ?_⟩
  obtain ⟨bound,big⟩ := b N hn he
  exact ⟨kernel_memLp N _ (NeZero.pos N) (PhysicalTests.horizon_le_log N).1
    (large_alpha_pos big).le (large_parameters big).2.2,bound grh⟩

#print axioms kernel_memLp
#print axioms exists_of_kernel_size
end GoldbachSpectral435.CumulativeKernel
