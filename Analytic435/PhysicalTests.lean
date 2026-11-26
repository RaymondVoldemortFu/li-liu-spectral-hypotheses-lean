module
public import ReflectionModel

/-! Compact real functions of Fourier time as original Li–Liu Mellin tests. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PhysicalTests

def fromTime (M : ℕ) (g : ℝ→ℝ) (u : ℝ) : ℝ := g (-Real.log (M*u))/Real.sqrt u

lemma time_support {M : ℕ} (mp : 0<M) {g : ℝ→ℝ} {A B : ℝ}
    (s : Function.support g⊆Icc A B) :
    Function.support (fromTime M g) ⊆ Icc (Real.exp (-B)/M) (Real.exp (-A)/M) := by
  intro u hu
  have m : 0<(M:ℝ) := by exact_mod_cast mp
  have h : g (-Real.log (M*u))/Real.sqrt u ≠ 0 := hu
  have up : 0<u := by
    by_contra! n
    exact h (by rw [Real.sqrt_eq_zero_of_nonpos n,div_zero])
  have live : g (-Real.log (M*u))≠0 := by intro z; exact h (by rw [z,zero_div])
  obtain ⟨lo,hi⟩ := s live
  have pos := mul_pos m up
  constructor
  · apply (div_le_iff₀ m).mpr
    rw [mul_comm u,← Real.exp_log pos]
    exact Real.exp_le_exp.mpr (by linarith)
  · apply (le_div_iff₀ m).mpr
    rw [mul_comm u,← Real.exp_log pos]
    exact Real.exp_le_exp.mpr (by linarith)

/-- A compact time profile can always be placed strictly inside the unit
Mellin interval by a sufficiently large sampling scale. -/
def timeWeight {M : ℕ} (mp : 0<M) {A B : ℝ} (ab : A≤B) (large : Real.exp (-A)<M)
    (g : ℝ→ℝ) (cg : ContDiff ℝ 6 g) (sg : Function.support g⊆Icc A B) :
    FiniteModelWeight (fromTime M g) := by
  have m : 0<(M:ℝ) := by exact_mod_cast mp
  have support := time_support mp sg
  have lo : 0<Real.exp (-B)/M := by positivity
  refine ⟨?_,_,_,lo,(div_lt_one m).mpr large,div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) m.le,support⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases h : x<Real.exp (-B)/M
  · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with u hu
    by_contra ne
    exact (not_lt_of_ge (support ne).1) hu
  · have xp := lo.trans_le (le_of_not_gt h)
    apply ContDiffAt.div _ (Real.contDiffAt_sqrt xp.ne') (Real.sqrt_pos.mpr xp).ne'
    apply cg.contDiffAt.comp x
    apply ContDiffAt.neg
    exact (Real.contDiffAt_log.mpr (mul_pos m xp).ne').comp x (contDiffAt_const.mul contDiffAt_id)

private lemma positive_identity (M : ℕ) (g : ℝ→ℝ) {u : ℝ} (up : 0<u) :
    companion (fromTime M g) u=g (-Real.log (M*u)) := by
  unfold companion fromTime
  field_simp [(Real.sqrt_pos.mpr up).ne']

/-- In Fourier time the Mellin derivative of this weight is g+g'. -/
theorem derivative_identity {M : ℕ} (mp : 0<M) (g : ℝ→ℝ) (dg : Differentiable ℝ g) (t : ℝ) :
    mellinD (companion (fromTime M g)) (Real.exp (-t)/M)=g t+deriv g t := by
  let u := Real.exp (-t)/M
  have m : 0<(M:ℝ) := by exact_mod_cast mp
  have up : 0<u := by dsimp [u]; positivity
  have mu : (M:ℝ)*u=Real.exp (-t) := by dsimp [u]; field_simp
  have tu : -Real.log (M*u)=t := by rw [mu,Real.log_exp,neg_neg]
  have loc : (companion (fromTime M g)) =ᶠ[𝓝 u] (fun x => g (-Real.log (M*x))) := by
    filter_upwards [Ioi_mem_nhds up] with x hx
    exact positive_identity M g hx
  have prod : HasDerivAt (fun x : ℝ => (M:ℝ)*x) (M:ℝ) u := by
    simpa using (hasDerivAt_id u).const_mul (M:ℝ)
  have lg := (prod.log (mul_pos m up).ne').neg
  have dd := ((dg (-Real.log (M*u))).hasDerivAt.comp u lg).congr_of_eventuallyEq loc
  unfold mellinD
  change companion (fromTime M g) u-u*deriv (companion (fromTime M g)) u=_
  rw [positive_identity M g up,dd.deriv,tu]
  field_simp
  ring

/-- Every compact smooth real time profile is detected by a Mellin weight
at an integral multiple of the original modulus. -/
theorem time_test (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) {A B : ℝ}
    (ab : A≤B) (g : ℝ→ℝ) (cg : ContDiff ℝ 6 g) (sg : Function.support g⊆Icc A B) :
    ∃ (k : ℕ) (kp : 0<k) (f : ℝ→ℝ) (hf : FiniteModelWeight f),
      ∀ v : HardySpace (alpha N) beta, paperInner v (testVector N (k*N) (Nat.mul_pos kp (NeZero.pos N)) f hf) =
        (Real.sqrt (2*Real.pi):ℂ)⁻¹ * ∫ t : ℝ, v t*((g t+deriv g t:ℝ):ℂ) := by
  let k := ⌈Real.exp (-A)⌉₊+1
  have kp : 0<k := Nat.succ_pos _
  have mp := Nat.mul_pos kp (NeZero.pos N)
  have kn : k≤k*N := by
    simpa only [mul_one] using Nat.mul_le_mul_left k (show 1≤N from NeZero.pos N)
  have before : Real.exp (-A)<(k:ℝ) := (Nat.le_ceil _).trans_lt (by dsimp [k]; push_cast; linarith)
  have cutoff : Real.exp (-A)<(k*N:ℕ) := before.trans_le (Nat.cast_le.mpr kn)
  let f := fromTime (k*N) g
  let hf := timeWeight mp ab cutoff g cg sg
  refine ⟨k,kp,f,hf,?_⟩
  intro v
  have nr : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have lg := (Real.lt_log_iff_exp_lt nr).mpr big
  have hb : (1/9:ℝ)∈Ioo (alpha N) beta :=
    ⟨one_div_lt_one_div_of_lt (by norm_num) (by linarith),by norm_num [beta]⟩
  rw [← testVector_rep N _ mp f hf (1/9) (by norm_num) hb v,
    finiteFunctionalValue_density _ mp _ ((FiniteModel.companion_contDiff hf).of_le (by norm_num))
      _ _ (FiniteModel.companion_support_subset hf) _ (by norm_num) hb]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [show mellinD (companion f) (Real.exp (-t)/(k*N:ℕ))=_ from
    derivative_identity mp g (cg.differentiable (by norm_num)) t]

#print axioms time_test
#print axioms derivative_identity
end GoldbachSpectral435.PhysicalTests
