module
public import FiniteDiscrepancy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-! Rectangular cumulative kernels for all physical dilations. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Filter
namespace GoldbachSpectral435.CumulativeKernel

/-- Integration in one or two threshold coordinates. -/
def unitMeasure : Measure ℝ := volume.restrict (Ioc 0 1)
instance : IsFiniteMeasure unitMeasure := by unfold unitMeasure; infer_instance

def thresholds : Measure (ℝ×ℝ) := unitMeasure.prod unitMeasure
instance : IsFiniteMeasure thresholds := by unfold thresholds; infer_instance

def profile (f : ℝ→ℝ) (u : ℝ) := f u/Real.sqrt u

/-- The weighted rectangle has open upper edges and is supported in (0,1]. -/
def step (r u : ℝ) : ℝ := if 0<u ∧ u<r ∧ u≤1 then Real.sqrt u else 0

lemma profile_smooth {f : ℝ→ℝ} (hf : FiniteModelWeight f) : ContDiff ℝ 6 (profile f) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases low : u<hf.lower
  · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds low] with t h
    have z : f t=0 := by by_contra ne; exact (not_le_of_gt h) (hf.mem_support_interval ne).1
    simp [profile,z]
  · have pos := hf.lower_pos.trans_le (le_of_not_gt low)
    exact hf.smooth.contDiffAt.div (Real.contDiffAt_sqrt pos.ne') (Real.sqrt_pos.mpr pos).ne'

lemma step_measurable {α : Type*} [MeasurableSpace α] {r u : α→ℝ}
    (hr : Measurable r) (hu : Measurable u) : Measurable (fun x => step (r x) (u x)) :=
  Measurable.ite ((measurableSet_lt measurable_const hu).inter
    ((measurableSet_lt hu hr).inter (measurableSet_le hu measurable_const)))
    (Real.continuous_sqrt.measurable.comp hu) measurable_const

lemma step_bounds (r u : ℝ) : 0≤step r u ∧ step r u≤1 := by
  unfold step
  split_ifs with h
  · exact ⟨Real.sqrt_nonneg _,by simpa using Real.sqrt_le_sqrt h.2.2⟩
  · norm_num

private lemma profile_end {f : ℝ→ℝ} (hf : FiniteModelWeight f) : profile f 1=0 := by
  have z : f 1=0 := by by_contra ne; exact lt_irrefl 1 (hf.mem_support_unit ne).2
  simp [profile,z]

/-- Volterra representation of each test by weighted threshold indicators. -/
theorem represent (f : ℝ→ℝ) (hf : FiniteModelWeight f) (u : ℝ) :
    (∫ r, deriv (profile f) r*step r u ∂unitMeasure)= -f u := by
  by_cases active : u∈Ioo (0:ℝ) 1
  · obtain ⟨up,ul⟩ := active
    have sm := profile_smooth hf
    have eq (r : ℝ) : deriv (profile f) r*step r u =
        (Ioi u).indicator (fun t => Real.sqrt u*deriv (profile f) t) r := by
      by_cases h : u<r
      · simp [step,up,ul.le,h,mul_comm]
      · simp [step,up,ul.le,h]
    have ints : Ioc (0:ℝ) 1 ∩ Ioi u=Ioc u 1 := by ext x; simp only [mem_inter_iff,mem_Ioc,mem_Ioi]; grind
    unfold unitMeasure
    simp_rw [eq]
    rw [setIntegral_indicator measurableSet_Ioi,ints,← intervalIntegral.integral_of_le ul.le,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_deriv_eq_sub' (profile f) rfl
      (fun _ _ => sm.differentiable (by decide) _) (sm.continuous_deriv (by decide)).continuousOn,
      profile_end hf]
    unfold profile
    field_simp [(Real.sqrt_pos.mpr up).ne']
    simp
  · have z : f u=0 := by by_contra ne; exact active (hf.mem_support_unit ne)
    rw [z,neg_zero]
    apply integral_eq_zero_of_ae
    unfold unitMeasure
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have out : ¬(0<u ∧ u<r ∧ u≤1) := fun h => active ⟨h.1,h.2.1.trans_le hr.2⟩
    simp [step,out]

def derivativePair (f : ℝ→ℝ) (p : ℝ×ℝ) := deriv (profile f) p.1*deriv (profile f) p.2

/-- The two thresholds give a rectangular primitive of the test product. -/
theorem represent_pair (f : ℝ→ℝ) (hf : FiniteModelWeight f) (u v : ℝ) :
    (∫ p, derivativePair f p*(step p.1 u*step p.2 v) ∂thresholds)=f u*f v := by
  have eq (p : ℝ×ℝ) : derivativePair f p*(step p.1 u*step p.2 v)=
      (deriv (profile f) p.1*step p.1 u)*(deriv (profile f) p.2*step p.2 v) := by dsimp [derivativePair]; ring
  unfold thresholds
  simp_rw [eq]
  rw [integral_prod_mul (fun r => deriv (profile f) r*step r u) (fun r => deriv (profile f) r*step r v),
    represent f hf,represent f hf,neg_mul_neg]

private lemma profile_bound {f : ℝ→ℝ} (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0≤C ∧ ∀ r : ℝ, |deriv (profile f) r|≤C := by
  have compact : HasCompactSupport (profile f) := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun x h => hf.mem_support_interval (u:=x) (by intro z; exact h (by simp [profile,z])))
  obtain ⟨C,h⟩ := ((profile_smooth hf).continuous_deriv (by decide)).bounded_above_of_compact_support compact.deriv
  exact ⟨C,(abs_nonneg _).trans (h 0),h⟩

private lemma tensor_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (u v : α→ℝ) (hu : Measurable u) (hv : Measurable v) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    Integrable (fun z : α×(ℝ×ℝ) => derivativePair f z.2*(step z.2.1 (u z.1)*step z.2.2 (v z.1))) (μ.prod thresholds) := by
  let k (x : α) (p : ℝ×ℝ) := derivativePair f p*(step p.1 (u x)*step p.2 (v x))
  have dc := (profile_smooth hf).continuous_deriv (by decide)
  have dh : Measurable (derivativePair f) := (dc.measurable.comp measurable_fst).mul (dc.measurable.comp measurable_snd)
  have mk : Measurable (Function.uncurry k) := (dh.comp measurable_snd).mul
    ((step_measurable (measurable_fst.comp measurable_snd) (hu.comp measurable_fst)).mul
      (step_measurable (measurable_snd.comp measurable_snd) (hv.comp measurable_fst)))
  obtain ⟨C,cp,bc⟩ := profile_bound hf
  apply (integrable_const (C*C)).mono' mk.aestronglyMeasurable
  filter_upwards with z
  change ‖derivativePair f z.2*(step z.2.1 (u z.1)*step z.2.2 (v z.1))‖≤C*C
  simp only [Real.norm_eq_abs,derivativePair,abs_mul,abs_of_nonneg (step_bounds _ _).1]
  apply mul_le_of_le_one_right _ ((mul_le_mul (step_bounds _ _).2 (step_bounds _ _).2 (step_bounds _ _).1 zero_le_one).trans_eq (one_mul 1)) |>.trans
  · exact mul_le_mul (bc _) (bc _) (abs_nonneg _) cp
  · positivity

lemma weighted_pair_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (u v : α→ℝ) (hu : Measurable u) (hv : Measurable v) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    Integrable (fun p => derivativePair f p*(∫ x, step p.1 (u x)*step p.2 (v x) ∂μ)) thresholds := by
  apply (tensor_integrable μ u v hu hv f hf).integral_prod_right.congr
  filter_upwards with p
  exact integral_const_mul _ _

lemma atom_integrable (f : ℝ→ℝ) (hf : FiniteModelWeight f) (u v : ℝ) :
    Integrable (fun p => derivativePair f p*(step p.1 u*step p.2 v)) thresholds := by
  have h := weighted_pair_integrable (Measure.dirac ()) (fun _ => u) (fun _ => v) measurable_const measurable_const f hf
  simpa only [integral_const,Measure.real,Measure.dirac_apply_of_mem (Set.mem_univ ()),ENNReal.toReal_one,one_smul] using h

/-- An arbitrary finite positive measure on pairs can be inserted. This
also applies to each affine line of the Li–Liu singular-series term. -/
theorem integrate_pairs {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (u v : α→ℝ) (hu : Measurable u) (hv : Measurable v) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    (∫ x, f (u x)*f (v x) ∂μ) =
      ∫ p, derivativePair f p*(∫ x, step p.1 (u x)*step p.2 (v x) ∂μ) ∂thresholds := by
  let k (x : α) (p : ℝ×ℝ) := derivativePair f p*(step p.1 (u x)*step p.2 (v x))
  have ik := tensor_integrable μ u v hu hv f hf
  calc
    _ = ∫ x, ∫ p, k x p ∂thresholds ∂μ := integral_congr_ae (Eventually.of_forall (fun x => (represent_pair f hf (u x) (v x)).symm))
    _ = ∫ p, ∫ x, k x p ∂μ ∂thresholds := integral_integral_swap ik
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      exact integral_const_mul _ _

#print axioms integrate_pairs
end GoldbachSpectral435.CumulativeKernel
