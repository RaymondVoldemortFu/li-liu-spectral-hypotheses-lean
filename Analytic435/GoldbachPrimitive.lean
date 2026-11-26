module
public import ReflectionModel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The cumulative discrepancy for the original first Goldbach line. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Finset
open scoped Topology InnerProductSpace
namespace GoldbachSpectral435.GoldbachPrimitive

def mass (N n : ℕ) : ℝ :=
  if n.Coprime N then mangoldt n*mangoldt (N-n)/N else 0

/-- The cumulative, unweighted Mangoldt-pair error in the variable n/N. -/
def primitive (N : ℕ) (u : ℝ) : ℝ :=
  (∑ n ∈ range N, if (n:ℝ)/N<u then mass N n else 0)-singularSeries N*u

def reflected (f : ℝ→ℝ) (u : ℝ) : ℝ := f u*f (1-u)

private lemma integration {N : ℕ} (np : 0<N) (F : ℝ→ℝ) (smooth : ContDiff ℝ 1 F)
    (endzero : F 1=0) :
    (∫ t in (0:ℝ)..1, primitive N t*deriv F t)=
      singularSeries N*(∫ t in (0:ℝ)..1, F t)-∑ n ∈ range N, mass N n*F (n/(N:ℝ)) := by
  let a (n : ℕ) : ℝ := n/(N:ℝ)
  let term (n : ℕ) := (Ioi (a n)).indicator (fun t => mass N n*deriv F t)
  have dc := smooth.continuous_deriv (by decide)
  have df := smooth.differentiable (by decide)
  have ti (n : ℕ) : IntervalIntegrable (term n) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
      (((dc.const_mul _).intervalIntegrable 0 1).1.mono_set Set.inter_subset_right)
  have single (n : ℕ) (hn : n∈range N) : (∫ t in (0:ℝ)..1, term n t)= -(mass N n*F (a n)) := by
    have nr : 0<(N:ℝ) := by exact_mod_cast np
    have ap : 0≤a n := by dsimp [a]; positivity
    have al : a n≤1 := (div_le_one nr).mpr (by exact_mod_cast (mem_range.mp hn).le)
    have sets : Ioc (0:ℝ) 1 ∩ Ioi (a n)=Ioc (a n) 1 := by ext x; simp only [Set.mem_inter_iff,Set.mem_Ioc,Set.mem_Ioi]; grind
    rw [intervalIntegral.integral_of_le zero_le_one,show term n=_ from rfl,
      setIntegral_indicator measurableSet_Ioi,sets,← intervalIntegral.integral_of_le al,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_deriv_eq_sub' F rfl
      (fun _ _ => df _) dc.continuousOn,endzero]
    ring
  have sumI : IntervalIntegrable (fun t => ∑ n ∈ range N, term n t) volume 0 1 :=
    by
      simpa only [← Finset.sum_apply] using IntervalIntegrable.sum (range N) (fun n _ => ti n)
  have intId := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (u:=fun t : ℝ => t) (u':=fun _ => (1:ℝ)) (v:=F) (v':=deriv F)
    continuous_id.continuousOn smooth.continuous.continuousOn (fun x _ => hasDerivAt_id x)
    (fun x _ => (df x).hasDerivAt) (by simp) (dc.intervalIntegrable ..)
  simp only [endzero,mul_zero,zero_mul,sub_zero,zero_sub,one_mul] at intId
  have pt (t : ℝ) : primitive N t*deriv F t =
      (∑ n ∈ range N, term n t)-singularSeries N*(t*deriv F t) := by
    unfold primitive
    rw [sub_mul,sum_mul,mul_assoc]
    congr 1
    apply sum_congr rfl
    intro n _
    by_cases h : a n<t
    · simp [term,a,h]
    · simp [term,a,h]
  simp_rw [pt]
  have ct : Continuous (fun t : ℝ => singularSeries N*(t*deriv F t)) := continuous_const.mul (continuous_id.mul dc)
  rw [intervalIntegral.integral_sub sumI (ct.intervalIntegrable ..),
    intervalIntegral.integral_finsetSum (fun n _ => ti n),intervalIntegral.integral_const_mul,intId]
  rw [sum_congr rfl single,Finset.sum_neg_distrib]
  ring

/-- The residual quadratic form on the first block is the pairing of
the cumulative Goldbach error with the derivative of the reflected test. -/
theorem exact_integral (N : ℕ) [NeZero N] (he : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let x := testVector N N (NeZero.pos N) f hf
    paperInner (residualOperator ha N x) x =
      ((∫ t in (0:ℝ)..1, primitive N t*deriv (reflected f) t : ℝ):ℂ) := by
  intro x
  have sm : ContDiff ℝ 1 (reflected f) := by
    have c := hf.smooth.of_le (by decide : (1:WithTop ℕ∞)≤6)
    exact c.mul (c.comp (contDiff_const.sub contDiff_id))
  have z : f 1=0 := by by_contra ne; exact (lt_irrefl 1) (hf.mem_support_unit ne).2
  rw [integration (NeZero.pos N) _ sm (by simp [reflected,z]),
    ReflectionModel.smooth_residual N he big g ha f hf]
  apply Complex.ofReal_inj.mpr
  rw [mul_comm (singularSeries N)]
  congr 1
  apply sum_congr rfl
  intro n hn
  have le := (mem_range.mp hn).le
  have nr : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
  have arg : ((N-n:ℕ):ℝ)/N=1-(n:ℝ)/N := by rw [Nat.cast_sub le]; field_simp
  by_cases cp : n.Coprime N
  · simp only [ite_eq_left cp,mass,reflected,sampleValue,arg]
    rw [div_mul_div_comm,← sq,Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  · simp [mass,cp]

private lemma increasing (N : ℕ) {u v : ℝ} (le : u≤v) :
    primitive N u+singularSeries N*u ≤ primitive N v+singularSeries N*v := by
  simp only [primitive,sub_add_cancel]
  apply sum_le_sum
  intro n _
  by_cases p : (n:ℝ)/N<u
  · simp [p,p.trans_le le]
  · simp only [ite_eq_right p]
    split
    · unfold mass
      split
      · exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg _)
      · rfl
    · rfl

/-- Ordered positive prime masses control every threshold between mesh
points. The interpolation loss is independent of the modulus. -/
theorem between_mesh_points (N m : ℕ) (mp : 0<m) (D : ℝ)
    (mesh : ∀ j : ℕ, j≤m → |primitive N (j/(m:ℝ))|≤D)
    (t : ℝ) (ht : t∈Set.Icc 0 1) :
    |primitive N t|≤D+singularSeries N/m := by
  have mr : 0<(m:ℝ) := by exact_mod_cast mp
  have sp := (singularSeries_pos N).le
  rcases ht.2.eq_or_lt with e|lt
  · rw [e]
    have endpoint := mesh m le_rfl
    rw [div_self mr.ne'] at endpoint
    exact endpoint.trans (le_add_of_nonneg_right (div_nonneg sp mr.le))
  let j := ⌊t*m⌋₊
  have jle : (j:ℝ)≤t*m := Nat.floor_le (mul_nonneg ht.1 mr.le)
  have upper : t*m<(j:ℝ)+1 := Nat.lt_floor_add_one _
  have jm : j<m := by
    exact_mod_cast jle.trans_lt (show t*m<(m:ℝ) by simpa using mul_lt_mul_of_pos_right lt mr)
  have lo : (j:ℝ)/m≤t := (div_le_iff₀ mr).mpr jle
  have hi : t≤((j+1:ℕ):ℝ)/m := (le_div_iff₀ mr).mpr (by simpa using upper.le)
  have l := increasing N lo
  have h := increasing N hi
  have lbound := (abs_le.mp (mesh j jm.le)).1
  have hbound := (abs_le.mp (mesh (j+1) jm)).2
  have step : ((j+1:ℕ):ℝ)/m=(j:ℝ)/m+1/m := by push_cast; ring
  rw [step] at h hbound hi
  have tone := mul_le_mul_of_nonneg_left lo sp
  have ttwo := mul_le_mul_of_nonneg_left hi sp
  rw [mul_add] at h ttwo
  apply abs_le.mpr
  constructor <;> linarith [show singularSeries N*(1/(m:ℝ))=singularSeries N/m by ring]

/-- A finite collection of cumulative prime counts bounds the spectral
entry for every first-scale test, including weights chosen after N. -/
theorem mesh_bound (N m : ℕ) [NeZero N] (he : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (mp : 0<m) (D : ℝ)
    (mesh : ∀ j : ℕ, j≤m → |primitive N (j/(m:ℝ))|≤D)
    (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let x := testVector N N (NeZero.pos N) f hf
    ‖paperInner (residualOperator ha N x) x‖ ≤
      (D+singularSeries N/m)*(∫ t in (0:ℝ)..1, |deriv (reflected f) t|) := by
  intro x
  rw [exact_integral N he big g ha f hf,Complex.norm_real]
  have c := hf.smooth.of_le (by decide : (1:WithTop ℕ∞)≤6)
  have sm : ContDiff ℝ 1 (reflected f) := c.mul (c.comp (contDiff_const.sub contDiff_id))
  rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,
    ← integral_const_mul]
  apply norm_integral_le_of_norm_le
  · exact (((sm.continuous_deriv (by decide)).abs.const_mul _).intervalIntegrable 0 1).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (between_mesh_points N m mp D mesh t ⟨ht.1.le,ht.2⟩) (abs_nonneg _)

#print axioms mesh_bound
#print axioms exact_integral
end GoldbachSpectral435.GoldbachPrimitive
