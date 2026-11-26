module
public import PhysicalTests
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Separation by the operator 1+d/dt on an open right half-line. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set
open scoped Topology ContDiff
namespace GoldbachSpectral435.PhysicalTests

/-- Solve the first-order equation with a delayed compensating translate.
Both sides are supported strictly above the same left endpoint. -/
theorem translated_primitive {A B : ℝ} {φ : ℝ→ℝ} (hφ : ContDiff ℝ ∞ φ)
    (supp : Function.support φ⊆Icc A B) (d : ℝ) (dp : 0≤d) :
    ∃ g : ℝ→ℝ, ContDiff ℝ ∞ g ∧ Function.support g⊆Icc A (B+d) ∧
      ∀ t, g t+deriv g t=φ t-Real.exp (-d)*φ (t-d) := by
  let F := fun t : ℝ => Real.exp t*φ t
  let P := fun t : ℝ => ∫ s in (0:ℝ)..t, F s
  have sm : ContDiff ℝ ∞ F := Real.contDiff_exp.mul hφ
  have der (t : ℝ) : HasDerivAt P (F t) t := (sm.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have sp : ContDiff ℝ ∞ P := contDiff_infty_iff_deriv.mpr ⟨fun t => (der t).differentiableAt,
    (funext (fun t => (der t).deriv)) ▸ sm⟩
  let g := fun t : ℝ => Real.exp (-t)*(P t-P (t-d))
  have shift : ContDiff ℝ ∞ (fun t : ℝ => t-d) := contDiff_id.sub contDiff_const
  refine ⟨g,(Real.contDiff_exp.comp contDiff_id.neg).mul (sp.sub (sp.comp shift)),?_,?_⟩
  · intro t ht
    by_contra outside
    have vanish : P t-P (t-d)=0 := by
      rw [show P t-P (t-d)=∫ s in t-d..t, F s from
        intervalIntegral.integral_interval_sub_left (sm.continuous.intervalIntegrable 0 t)
          (sm.continuous.intervalIntegrable 0 (t-d))]
      apply intervalIntegral.integral_zero_ae
      filter_upwards with s hs
      rw [uIoc_of_le (by linarith : t-d≤t)] at hs
      have z : φ s=0 := by
        by_contra ne
        obtain ⟨l,r⟩ := supp ne
        exact outside ⟨l.trans hs.2,by linarith [hs.1]⟩
      simp [F,z]
    exact ht (by simp [g,vanish])
  · intro t
    have en : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_id t).neg.exp
    have dd : HasDerivAt (fun x => P x-P (x-d)) (F t-F (t-d)) t := by
      convert (der t).sub ((der (t-d)).comp t ((hasDerivAt_id t).sub_const d)) using 1 <;> first | rfl | ring
    have eq : deriv g t=_ := (en.mul dd).deriv
    have e1 : Real.exp (-t)*Real.exp t=1 := by rw [← Real.exp_add]; simp
    have e2 : Real.exp (-t)*Real.exp (t-d)=Real.exp (-d) := by rw [← Real.exp_add]; congr 1; ring
    rw [eq]
    dsimp only [g,F]
    linear_combination φ t*e1-φ (t-d)*e2

/-- On a right half-line the compact smooth range of 1+d/dt separates all
locally tested integrable densities, even at a fixed left endpoint. -/
theorem halfLine_separation (L : ℝ) (v : ℝ→ℂ) (iv : IntegrableOn v (Ioi L))
    (ann : ∀ {A B : ℝ}, L<A → A≤B → ∀ g : ℝ→ℝ, ContDiff ℝ 6 g →
      Function.support g⊆Icc A B → (∫ t, v t*((g t+deriv g t:ℝ):ℂ))=0) :
    ∀ᵐ t : ℝ, t∈Ioi L → v t=0 := by
  apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero iv.locallyIntegrableOn
  intro φ smooth compact inside
  obtain ⟨A,la,lower⟩ := compact.exists_forall_le' (f:=id) continuous_id.continuousOn (fun t ht => inside ht)
  obtain ⟨b,hb⟩ := compact.bddAbove
  let B := max A b
  have ab : A≤B := le_max_left _ _
  have sp : Function.support φ⊆Icc A B := fun t ht => ⟨lower t (subset_tsupport _ ht),
    (hb (subset_tsupport _ ht)).trans (le_max_right ..)⟩
  obtain ⟨C,bound⟩ := smooth.continuous.bounded_above_of_compact_support compact
  have cp : 0≤C := (abs_nonneg _).trans (bound 0)
  let μ : Measure ℝ := volume.restrict (Ioi L)
  let W := fun (n : ℕ) t => φ t-Real.exp (-(n:ℝ))*φ (t-n)
  have wc (n : ℕ) : Continuous (W n) := smooth.continuous.sub
    (continuous_const.mul (smooth.continuous.comp (continuous_id.sub continuous_const)))
  have cutoff (n : ℕ) (t : ℝ) (h : t∉Ioi L) : W n t=0 := by
    have nt : t≤L := le_of_not_gt h
    have zero {s : ℝ} (lt : s<A) : φ s=0 := by by_contra ne; exact (not_le_of_gt lt) (sp ne).1
    simp [W,zero (nt.trans_lt la),zero (show t-(n:ℝ)<A by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have ints (n : ℕ) : (∫ t, v t*(W n t:ℂ) ∂μ)=0 := by
    obtain ⟨g,cg,sg,eq⟩ := translated_primitive smooth sp (n:ℝ) (Nat.cast_nonneg _)
    have h := ann la (by linarith [Nat.cast_nonneg (α:=ℝ) n] : A≤B+n) g (cg.of_le (by norm_num)) sg
    simp_rw [eq] at h
    change (∫ t in Ioi L, v t*(W n t:ℂ))=0
    rw [← integral_indicator measurableSet_Ioi]
    apply Eq.trans _ h
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t∈Ioi L
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht]
      change 0=v t*(W n t:ℂ)
      rw [cutoff n t ht]; simp
  have lim (t : ℝ) : Tendsto (fun n => W n t) atTop (𝓝 (φ t)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (t-A)] with n hn
    have z : φ (t-(n:ℝ))=0 := by by_contra ne; linarith [(sp ne).1]
    simp [W,z]
  have limint := tendsto_integral_of_dominated_convergence (μ:=μ) (fun t => ‖v t‖*(2*C))
    (fun n => iv.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp (wc n)).aestronglyMeasurable)
    (iv.norm.mul_const _) (fun n => Eventually.of_forall (fun t => by
      change ‖v t*(W n t:ℂ)‖≤‖v t‖*(2*C)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (abs_sub ..).trans
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      have small : Real.exp (-(n:ℝ))≤1 := Real.exp_le_one_iff.mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
      have cap (x : ℝ) : |φ x|≤C := by simpa only [Real.norm_eq_abs] using bound x
      linarith only [cap t,mul_le_mul small (cap (t-n)) (abs_nonneg _) zero_le_one]))
    (Eventually.of_forall (fun t => (Complex.continuous_ofReal.continuousAt.tendsto.comp (lim t)).const_mul (v t)))
  have z : (∫ t, v t*(φ t:ℂ) ∂μ)=0 := tendsto_nhds_unique limint
    (tendsto_const_nhds.congr (fun n => (ints n).symm))
  change (∫ t in Ioi L, v t*(φ t:ℂ))=0 at z
  rw [← integral_indicator measurableSet_Ioi] at z
  apply Eq.trans _ z
  apply integral_congr_ae
  filter_upwards with t
  by_cases h : t∈Ioi L
  · simp [h,Complex.real_smul,mul_comm]
  · have q : φ t=0 := by by_contra ne; exact h (inside (subset_tsupport _ ne))
    simp [h,q]

#print axioms halfLine_separation
end GoldbachSpectral435.PhysicalTests
