module
public import PhysicalTests
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Density of finite physical tests on the full original Hardy strip. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate InnerProductSpace ContDiff
namespace GoldbachSpectral435.PhysicalTests

private def bump : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩

private lemma transform_zero {a : ℝ} (v : HardySpace a beta) {s : ℝ} (sp : 0<s) (hs : s∈Ioo a beta)
    (ann : ∀ (g : ℝ→ℝ), ContDiff ℝ 6 g → ∀ {A B : ℝ}, A≤B → Function.support g⊆Icc A B →
      (∫ t : ℝ, v t*((g t+deriv g t:ℝ):ℂ))=0) :
    fourierLaplace v (s:ℂ)=0 := by
  let R (n : ℕ) : ℝ := n+1
  have pos (n : ℕ) : 0<R n := by dsimp [R]; positivity
  have one (n : ℕ) : 1≤R n := by dsimp [R]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have bs : ContDiff ℝ ∞ (bump:ℝ→ℝ) := bump.contDiff
  have dc : Continuous (deriv (bump:ℝ→ℝ)) := bs.continuous_deriv (by simp)
  obtain ⟨C,hC⟩ := dc.bounded_above_of_compact_support bump.hasCompactSupport.deriv
  let F (t : ℝ) : ℂ := v t*Complex.exp ((s:ℂ)*t)
  let H (n : ℕ) (t : ℝ) := Real.exp (s*t)*bump (t/R n)
  let B (n : ℕ) (t : ℝ) := (1+s)*bump (t/R n)+deriv (bump:ℝ→ℝ) (t/R n)/R n
  have intF : Integrable F := fourierLaplace_integrable v (show (s:ℂ)∈strip a beta from hs)
  have hsmooth (n : ℕ) : ContDiff ℝ 6 (H n) := by
    apply ContDiff.mul
    · fun_prop
    · apply bump.contDiff.comp
      fun_prop
  have support (n : ℕ) : Function.support (H n)⊆Icc (-2*R n) (2*R n) := by
    intro t ht
    have live : bump (t/R n)≠0 := (mul_ne_zero_iff.mp ht).2
    have m : t/R n ∈ Function.support (bump:ℝ→ℝ) := live
    rw [bump.support_eq] at m
    have d := Metric.mem_ball.mp m
    change dist (t/R n) 0<2 at d
    rw [Real.dist_eq,sub_zero,abs_lt] at d
    exact ⟨((lt_div_iff₀ (pos n)).mp d.1).le,((div_lt_iff₀ (pos n)).mp d.2).le⟩
  have hd (n : ℕ) (t : ℝ) : H n t+deriv (H n) t=Real.exp (s*t)*B n t := by
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (s*u)) (Real.exp (s*t)*s) t := by
      simpa using ((hasDerivAt_id t).const_mul s).exp
    have h2 : HasDerivAt (fun u : ℝ => bump (u/R n)) (deriv (bump:ℝ→ℝ) (t/R n)*(1/R n)) t :=
      (bs.differentiable (by simp) _).hasDerivAt.comp t ((hasDerivAt_id t).div_const (R n))
    have eq : deriv (H n) t=_ := (h1.mul h2).deriv
    rw [eq]
    dsimp [H,B]
    ring
  have zero (n : ℕ) : (∫ t : ℝ, F t*(B n t:ℂ))=0 := by
    have z := ann (H n) (hsmooth n) (show -2*R n≤2*R n by linarith [pos n]) (support n)
    convert z using 1
    apply integral_congr_ae
    filter_upwards with t
    rw [hd,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_mul]
    dsimp [F]; ring
  have bc (n : ℕ) : Continuous (B n) := by
    apply Continuous.add
    · exact continuous_const.mul (bs.continuous.comp (continuous_id.div_const _))
    · exact (dc.comp (continuous_id.div_const _)).div_const _
  have major (n : ℕ) (t : ℝ) : |B n t| ≤ (1+s)+C := by
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_of_pos (show 0<1+s by linarith),abs_of_nonneg bump.nonneg,abs_div,abs_of_pos (pos n)]
    exact add_le_add (mul_le_of_le_one_right (by linarith) bump.le_one)
      ((div_le_self (abs_nonneg _) (one n)).trans (hC _))
  have b0 : bump 0=1 := bump.one_of_mem_closedBall (by simp [bump])
  have iv : Tendsto (fun n : ℕ => 1/R n) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have blim (t : ℝ) : Tendsto (fun n : ℕ => B n t) atTop (𝓝 (1+s)) := by
    have time : Tendsto (fun n : ℕ => t/R n) atTop (𝓝 0) := by
      simpa only [mul_zero,mul_one_div] using iv.const_mul t
    have first := ((bs.continuous.continuousAt.tendsto.comp time).const_mul (1+s))
    have second := (dc.continuousAt.tendsto.comp time).mul iv
    simpa only [Function.comp_apply,B,b0,mul_one,mul_zero,add_zero,mul_one_div] using first.add second
  have lim := tendsto_integral_of_dominated_convergence (fun t => ‖F t‖*((1+s)+C))
    (fun n => intF.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp (bc n)).aestronglyMeasurable)
    (intF.norm.mul_const _) (fun n => Eventually.of_forall (fun t => by
      change ‖F t*(B n t:ℂ)‖≤‖F t‖*((1+s)+C)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (major n t) (norm_nonneg _)))
    (Eventually.of_forall (fun t => ((Complex.continuous_ofReal.continuousAt.tendsto.comp (blim t)).const_mul (F t))))
  have value : (∫ t : ℝ, F t*(((1+s:ℝ):ℂ)))=0 :=
    tendsto_nhds_unique lim (tendsto_const_nhds.congr (fun n => (zero n).symm))
  rw [integral_mul_const] at value
  have nn : (((1+s:ℝ):ℂ))≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have z := (mul_eq_zero.mp value).resolve_right nn
  unfold fourierLaplace
  rw [show (∫ t : ℝ, v t*Complex.exp ((s:ℂ)*t))=0 from z,mul_zero]

def tests (N : ℕ) [NeZero N] : Set (HardySpace (alpha N) beta) :=
  {x | ∃ (k : ℕ) (kp : 0<k) (f : ℝ→ℝ) (hf : FiniteModelWeight f),
    x=testVector N (k*N) (Nat.mul_pos kp (NeZero.pos N)) f hf}

/-- Compact original Mellin tests at all integral dilations span a dense
complex subspace of the entire critical Hardy space. -/
theorem dense_tests (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) :
    Dense (↑(Submodule.span ℂ (tests N)) : Set (HardySpace (alpha N) beta)) := by
  let K := Submodule.span ℂ (tests N)
  have orth : Kᗮ=⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have ann (g : ℝ→ℝ) (cg : ContDiff ℝ 6 g) {A B : ℝ} (ab : A≤B) (sg : Function.support g⊆Icc A B) :
        (∫ t : ℝ, v t*((g t+deriv g t:ℝ):ℂ))=0 := by
      obtain ⟨k,kp,f,hf,h⟩ := time_test N big ab g cg sg
      let x := testVector N (k*N) (Nat.mul_pos kp (NeZero.pos N)) f hf
      have incl : x∈K := Submodule.subset_span (show x∈tests N from ⟨k,kp,f,hf,rfl⟩)
      have zero : paperInner v x=0 := hv _ incl
      rw [h v] at zero
      exact (mul_eq_zero.mp zero).resolve_left (inv_ne_zero (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.mpr (by positivity)).ne'))
    have ap := large_alpha_pos big
    have hab := (large_parameters big).2.2
    let c := (alpha N+beta)/2
    have ac : alpha N<c := by dsimp [c]; linarith
    have cb : c<beta := by dsimp [c]; linarith
    have lift : Tendsto ((↑) : ℝ→ℂ) (𝓝[>] c) (𝓝[≠] (c:ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun e => (ne_of_gt ht) (Complex.ofReal_inj.mp e)
    have zeros : ∀ᶠ t : ℝ in 𝓝[>] c, fourierLaplace v (t:ℂ)=0 := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds cb)] with t lo hi
      exact transform_zero v ((ap.trans ac).trans lo) ⟨ac.trans lo,hi⟩ ann
    have freq : ∃ᶠ s in 𝓝[≠] (c:ℂ), fourierLaplace v s=0 := lift.frequently zeros.frequently
    have isopen : IsOpen (strip (alpha N) beta) := isOpen_Ioo.preimage Complex.continuous_re
    have connected : IsPreconnected (strip (alpha N) beta) :=
      ((convex_halfSpace_re_gt (alpha N)).inter (convex_halfSpace_re_lt beta)).isPreconnected
    have all := ((fourierLaplace_differentiableOn v).analyticOnNhd isopen).eqOn_zero_of_preconnected_of_frequently_eq_zero
      connected (show (c:ℂ)∈strip (alpha N) beta from ⟨ac,cb⟩) freq
    apply (Submodule.mem_bot ℂ).mpr
    apply fourierLaplace_injective_strip hab
    intro s hs
    rw [evaluationVector_spec hs (0 : HardySpace (alpha N) beta)]
    simpa [paperInner] using all hs
  rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
  exact orth

#print axioms dense_tests
end GoldbachSpectral435.PhysicalTests
