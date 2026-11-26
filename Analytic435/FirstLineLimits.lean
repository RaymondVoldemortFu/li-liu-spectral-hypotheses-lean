module
public import GoldbachIntervals
public import SingleScaleCriterion
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Consequences for the actual first-line prime measure of uniform
smallness of the original residual on a growing sequence of moduli. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Finset
open scoped Topology
namespace GoldbachSpectral435.FirstLineLimits
open GoldbachPrimitive GoldbachSieve

def observed (N : ℕ) (f : ℝ→ℝ) : ℝ := (∑ n∈range N, mass N n*f (n/(N:ℝ)))/singularSeries N

def mean (f : ℝ→ℝ) : ℝ := ∫ u in (0:ℝ)..1, f u

private lemma weight_upper (N : ℕ) (np : 0<N) (big : Real.exp 10<(N:ℝ)) {u : ℝ}
    (up : 0<u) (u1 : u≤1) : energyWeight N (alpha N) u≤Real.exp 2 := by
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have l := (large_parameters big).2.1
  have ap := large_alpha_pos big
  rw [weight_eq np up]
  calc
    _ ≤ ((N:ℝ)*u)^(2*alpha N) := div_le_self (by positivity) (by have := Real.rpow_nonneg (mul_nonneg nr.le up.le) (-2*(beta-alpha N)); linarith)
    _ ≤ (N:ℝ)^(2*alpha N) := Real.rpow_le_rpow (by positivity) (by simpa using mul_le_mul_of_nonneg_left u1 nr.le) (by positivity)
    _ = _ := by rw [Real.rpow_def_of_pos nr]; congr 1; unfold alpha; field_simp

theorem fixed_energy (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 0<N → Real.exp 10<(N:ℝ) → normFunctional N f (alpha N)≤C := by
  let Q := ∫ t in (0:ℝ)..1, (physicalDensity f t)^2
  have cont : Continuous (physicalDensity f) :=
    (hf.continuous.div_const _).sub (continuous_id.mul (hf.smooth.continuous_deriv (by decide)))
  have q : 0≤Q := intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
  refine ⟨1+(2*Real.pi)⁻¹*(Real.exp 2*Q),by positivity,?_⟩
  intro N np big
  have ha := (large_parameters big).2.2
  rw [norm_integral N np f hf]
  have cmp : (∫ t in (0:ℝ)..1, energyWeight N (alpha N) t*(physicalDensity f t)^2)≤Real.exp 2*Q := by
    dsimp only [Q]
    rw [← intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_of_le zero_le_one]
    apply integral_mono_ae (((energyWeight_continuous N ha).mul (cont.pow 2)).intervalIntegrable 0 1).1
      (((cont.pow 2).const_mul (Real.exp 2)).intervalIntegrable 0 1).1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_le_mul_of_nonneg_right (weight_upper N np big ht.1 ht.2) (sq_nonneg _)
  linarith only [mul_le_mul_of_nonneg_left cmp (show 0≤(2*Real.pi)⁻¹ by positivity)]

theorem reflected_entry (N : ℕ) [NeZero N] (he : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let x := testVector N N (NeZero.pos N) f hf
    paperInner (residualOperator ha N x) x=
      ((singularSeries N*(mean (reflected f)-observed N (reflected f)):ℝ):ℂ) := by
  intro x
  rw [ReflectionModel.smooth_residual N he big grh ha f hf]
  apply Complex.ofReal_inj.mpr
  have sumEq : (∑ n∈range N, if n.Coprime N then sampleValue N n f*sampleValue N (N-n) f else 0)=
      ∑ n∈range N, mass N n*reflected f (n/(N:ℝ)) := by
    apply sum_congr rfl
    intro n hn
    have le := (mem_range.mp hn).le
    have nr : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
    have arg : ((N-n:ℕ):ℝ)/N=1-(n:ℝ)/N := by rw [Nat.cast_sub le]; field_simp
    by_cases cop : n.Coprime N
    · simp only [ite_eq_left cop,mass,reflected,sampleValue,arg]
      rw [div_mul_div_comm,← sq,Real.sq_sqrt (Nat.cast_nonneg N)]
      ring
    · simp [mass,cop]
  rw [sumEq]
  change mean (reflected f)*singularSeries N-_=singularSeries N*(mean (reflected f)-_/singularSeries N)
  field_simp [(singularSeries_pos N).ne']

def FirstScaleDecay (n : ℕ→ℕ) : Prop := ∀ ε : ℝ, 0<ε →
  ∀ᶠ j in atTop, PhysicalTests.ScaleBound (n j) 1 (ε*singularSeries (n j))

theorem first_scale_of_exists (h : ∃ h, HypothesisS h) {n : ℕ→ℕ} [∀ j, NeZero (n j)]
    (ng : Tendsto n atTop atTop) (he : ∀ j, Even (n j)) (g : ∀ j, GRH (n j)) :
    FirstScaleDecay n := by
  intro ε ep
  obtain ⟨K,cap⟩ := FiniteDiscrepancy.some_S_iff.mp h ε ep
  filter_upwards [ng.eventually_ge_atTop K] with j hj
  exact cap (n j) hj (he j) (g j) 1 zero_lt_one

/-- Every fixed smooth reflected test measures its Lebesgue mass in the
limit if the first-scale form is uniformly small. -/
theorem reflected_limit {n : ℕ→ℕ} [∀ j, NeZero (n j)] (h : FirstScaleDecay n)
    (ng : Tendsto n atTop atTop) (he : ∀ j, Even (n j)) (g : ∀ j, GRH (n j))
    (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    Tendsto (fun j => observed (n j) (reflected f)) atTop (𝓝 (mean (reflected f))) := by
  obtain ⟨C,cp,energy⟩ := fixed_energy f hf
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  obtain ⟨K,H⟩ := evenEventually_large
  filter_upwards [ng.eventually_ge_atTop K,h (ε/(2*C)) (by positivity)] with j hj small
  let N := n j
  have : NeZero N := inferInstanceAs (NeZero (n j))
  have big := H N hj (he j)
  have ha := (large_parameters big).2.2
  have hb := small f hf
  change ‖FiniteDiscrepancy.arithmetic N (1*N) f-FiniteDiscrepancy.continuousModel N 1 f‖≤
    ε/(2*C)*singularSeries N*normFunctional (1*N) f (alpha N) at hb
  rw [← (FiniteDiscrepancy.exact_form N 1 zero_lt_one (he j) big (g j) ha f hf).2] at hb
  simp only [one_mul] at hb
  rw [reflected_entry N (he j) big (g j) ha f hf,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_pos (singularSeries_pos N)] at hb
  have ss := singularSeries_pos N
  have total := hb.trans (mul_le_mul_of_nonneg_left (energy N (NeZero.pos N) big) (by positivity))
  rw [Real.dist_eq,abs_sub_comm]
  change |mean (reflected f)-observed N (reflected f)|<ε
  apply lt_of_le_of_lt _ (half_lt_self ep)
  apply le_of_mul_le_mul_left _ ss
  exact total.trans_eq (by field_simp)

#print axioms fixed_energy
#print axioms reflected_limit
end GoldbachSpectral435.FirstLineLimits
