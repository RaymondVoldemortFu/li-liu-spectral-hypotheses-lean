module
public import HalfLineTests
public import PhysicalCriterion

/-! At one sampling scale the test vectors are dense in the corresponding
physical half-line, including all complex input directions there. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PhysicalTests

private lemma integrableOn_right (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ))
    (v : HardySpace (alpha N) beta) (L : ℝ) : IntegrableOn (v:ℝ→ℂ) (Ioi L) := by
  let s : ℝ := 1/9
  have h := (hardy_weighted_line_integrable (sample_line big) v).norm.const_mul (Real.exp (-(s*L)))
  apply h.integrableOn.mono' (hardySpace_aestronglyMeasurable v).restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖v t‖≤Real.exp (-(s*L))*‖(Real.exp (s*t):ℂ)*v t‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← mul_assoc,← Real.exp_add]
  apply le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr _)
  have st : L<t := ht
  dsimp [s]
  linarith

private lemma fixed_time (N M : ℕ) [NeZero N] (mp : 0<M) (big : Real.exp 10<(N:ℝ))
    {A B : ℝ} (lt : -Real.log M<A) (ab : A≤B) (g : ℝ→ℝ) (cg : ContDiff ℝ 6 g)
    (sg : Function.support g⊆Icc A B) : ∃ (f : ℝ→ℝ) (hf : FiniteModelWeight f),
      ∀ v : HardySpace (alpha N) beta, paperInner v (testVector N M mp f hf)=
        (Real.sqrt (2*Real.pi):ℂ)⁻¹*∫ t : ℝ, v t*((g t+deriv g t:ℝ):ℂ) := by
  have pos : 0<(M:ℝ) := by exact_mod_cast mp
  have cut : Real.exp (-A)<M := (Real.lt_log_iff_exp_lt pos).mp (by linarith)
  let f := fromTime M g
  let hf := timeWeight mp ab cut g cg sg
  refine ⟨f,hf,?_⟩
  intro v
  rw [← testVector_rep N _ mp f hf (1/9) (by norm_num) (sample_line big) v,
    finiteFunctionalValue_density _ mp _ ((FiniteModel.companion_contDiff hf).of_le (by norm_num))
      _ _ (FiniteModel.companion_support_subset hf) _ (by norm_num) (sample_line big)]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [show mellinD (companion f) (Real.exp (-t)/M)=_ from
    derivative_identity mp g (cg.differentiable (by norm_num)) t]

/-- All Hardy vectors supported above -log M lie in the closure of the
complex span of real smooth tests at M itself. -/
theorem single_scale_density (N M : ℕ) [NeZero N] (mp : 0<M) (big : Real.exp 10<(N:ℝ))
    (x : HardySpace (alpha N) beta) (support : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log M → x t=0) :
    x∈(Submodule.span ℂ {z | AtScale N M mp z}).topologicalClosure := by
  let K := Submodule.span ℂ {z | AtScale N M mp z}
  change x∈K.topologicalClosure
  rw [← K.orthogonal_orthogonal_eq_closure]
  intro v hv
  have van : ∀ᵐ t : ℝ, t∈Ioi (-Real.log (M:ℝ)) → v t=0 := by
    apply halfLine_separation _ _ (integrableOn_right N big v _)
    intro A B lt ab g cg sg
    obtain ⟨f,hf,eq⟩ := fixed_time N M mp big lt ab g cg sg
    have belongs : testVector N M mp f hf∈K := Submodule.subset_span (show AtScale N M mp _ from ⟨f,hf,rfl⟩)
    have pair : paperInner v (testVector N M mp f hf)=0 := hv _ belongs
    rw [eq] at pair
    exact (mul_eq_zero.mp pair).resolve_left (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by positivity)).ne'))
  have ac : hardyMeasure (alpha N) beta≪volume := withDensity_absolutelyContinuous _ _
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [support,ac.ae_le van] with t hx h
  by_cases m : t≤ -Real.log M
  · simp [hx m]
  · simp [h (lt_of_not_ge m)]

#print axioms single_scale_density
end GoldbachSpectral435.PhysicalTests
