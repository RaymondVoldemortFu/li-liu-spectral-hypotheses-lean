module
public import GoldbachPrimitive

/-! Uniform variation bounds for a reflected Goldbach test. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set
namespace GoldbachSpectral435.GoldbachPrimitive

private def edge (f : ℝ→ℝ) (u : ℝ) := f u/(1-u)

private lemma vanishes_near_one {f : ℝ→ℝ} (hf : FiniteModelWeight f) :
    f =ᶠ[nhds (1:ℝ)] fun _ => 0 := by
  filter_upwards [Ioi_mem_nhds hf.upper_lt_one] with u h
  by_contra nz
  exact (not_le_of_gt h) (hf.mem_support_interval nz).2

private lemma edge_smooth {f : ℝ→ℝ} (hf : FiniteModelWeight f) : ContDiff ℝ 1 (edge f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases e : x=1
  · subst x
    apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [vanishes_near_one hf] with u h
    simp [edge,h]
  · exact (hf.smooth.of_le (by decide : (1:WithTop ℕ∞)≤6)).contDiffAt.div
      (contDiff_const.sub contDiff_id).contDiffAt (sub_ne_zero.mpr (Ne.symm e))

private lemma edge_primitive {f : ℝ→ℝ} (hf : FiniteModelWeight f) (u : ℝ) :
    HasDerivAt (fun t => t*f t*edge f t)
      (edge f u^2+2*(u*deriv f u)*edge f u) u := by
  by_cases e : u=1
  · subst u
    have z := (vanishes_near_one hf).eq_of_nhds
    simp only [edge,sub_self,div_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero]
    apply (hasDerivAt_const 1 (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [vanishes_near_one hf] with t h
    simp [h]
  · have df := (hf.smooth.differentiable (by decide) u).hasDerivAt
    have nz := sub_ne_zero.mpr (Ne.symm e)
    have de := df.div ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)) nz
    convert! (((hasDerivAt_id u).mul df).mul de) using 1
    simp only [edge,Pi.div_apply,Pi.sub_apply,Pi.mul_apply,id_eq]
    field_simp
    ring

/-- A weighted Hardy inequality with constant four. Compact support removes
the boundary term in the derivative of u f(u)^2/(1-u). -/
theorem boundary_hardy (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    (∫ t in (0:ℝ)..1, (f t/(1-t))^2) ≤ 4*(∫ t in (0:ℝ)..1, (t*deriv f t)^2) := by
  let A := fun t : ℝ => t*deriv f t
  let B := edge f
  let P := fun t : ℝ => B t^2+2*A t*B t
  have ca : Continuous A := continuous_id.mul (hf.smooth.continuous_deriv (by decide))
  have cb : Continuous B := (edge_smooth hf).continuous
  have cp : Continuous P := (cb.pow 2).add ((continuous_const.mul ca).mul cb)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=(0:ℝ)) (b:=1) (f:=fun t => t*f t*edge f t) (f':=P)
    (fun u _ => edge_primitive hf u) (cp.intervalIntegrable ..)
  have z : (∫ u in (0:ℝ)..1, P u)=0 := by simpa [edge] using h
  change (∫ t in (0:ℝ)..1, B t^2)≤_
  calc
    _ ≤ ∫ t in (0:ℝ)..1, 4*(A t)^2+2*P t := by
      apply intervalIntegral.integral_mono_on zero_le_one ((cb.pow 2).intervalIntegrable ..)
        ((((ca.pow 2).const_mul 4).add (cp.const_mul 2)).intervalIntegrable ..)
      intro u _
      change B u^2≤4*A u^2+2*(B u^2+2*A u*B u)
      nlinarith only [sq_nonneg (2*A u+B u)]
    _ = _ := by
      rw [intervalIntegral.integral_add (f:=fun t => 4*A t^2) (g:=fun t => 2*P t) (((ca.pow 2).const_mul 4).intervalIntegrable ..)
        ((cp.const_mul 2).intervalIntegrable ..),intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,z,mul_zero,add_zero]

/-- Reflection turns the degenerate first derivative at the left endpoint
into a Dirichlet condition at the right endpoint. -/
theorem variation_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    (∫ t in (0:ℝ)..1, |deriv (reflected f) t|) ≤
      4*(∫ t in (0:ℝ)..1, (f t/2-t*deriv f t)^2) := by
  let A := fun t : ℝ => t*deriv f t
  let B := edge f
  let C := fun t : ℝ => |deriv f t*f (1-t)|
  let P := fun t : ℝ => f t^2+2*A t*f t
  let J := fun t : ℝ => (f t/2-A t)^2
  have df := hf.smooth.differentiable (by decide)
  have dc := hf.smooth.continuous_deriv (by decide)
  have cf := hf.smooth.continuous
  have ca : Continuous A := continuous_id.mul dc
  have cb : Continuous B := (edge_smooth hf).continuous
  have flip : Continuous (fun t : ℝ => 1-t) := continuous_const.sub continuous_id
  have cc : Continuous C := (dc.mul (cf.comp flip)).abs
  have cp : Continuous P := (cf.pow 2).add ((continuous_const.mul ca).mul cf)
  have cj : Continuous J := ((cf.div_const 2).sub ca).pow 2
  have f1 : f 1=0 := (vanishes_near_one hf).eq_of_nhds
  have drForm (u : ℝ) : HasDerivAt (reflected f)
      (deriv f u*f (1-u)-f u*deriv f (1-u)) u := by
    have der := (df u).hasDerivAt.mul ((df (1-u)).hasDerivAt.comp u
      ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)))
    convert! der using 1
    simp only [Function.comp_apply]; ring
  have main : (∫ t in (0:ℝ)..1, |deriv (reflected f) t|)≤2*(∫ t in (0:ℝ)..1, C t) := by
    have s1 := hf.smooth.of_le (by decide : (1:WithTop ℕ∞)≤6)
    have cr' : ContDiff ℝ 1 (reflected f) := s1.mul (s1.comp (contDiff_const.sub contDiff_id))
    calc
      _ ≤ ∫ t in (0:ℝ)..1, C t+C (1-t) := by
        apply intervalIntegral.integral_mono_on zero_le_one ((cr'.continuous_deriv (by decide)).abs.intervalIntegrable ..)
          ((cc.add (cc.comp flip)).intervalIntegrable ..)
        intro u _
        rw [(drForm u).deriv]
        change _≤|deriv f u*f (1-u)| + |deriv f (1-u)*f (1-(1-u))|
        rw [sub_sub_cancel,mul_comm (deriv f (1-u))]
        exact abs_sub _ _
      _ = _ := by
        rw [intervalIntegral.integral_add (f:=C) (g:=fun t => C (1-t)) (cc.intervalIntegrable ..) ((cc.comp flip).intervalIntegrable ..),
          intervalIntegral.integral_comp_sub_left,sub_self,sub_zero,two_mul]
  have cBound : (∫ t in (0:ℝ)..1, 2*C t)≤
      2*(∫ t in (0:ℝ)..1, (A t)^2)+(1/2)*(∫ t in (0:ℝ)..1, (B t)^2) := by
    calc
      _ ≤ ∫ t in (0:ℝ)..1, 2*(A t)^2+(1/2)*(B (1-t))^2 := by
        apply intervalIntegral.integral_mono_on zero_le_one ((cc.const_mul 2).intervalIntegrable ..)
          ((((ca.pow 2).const_mul 2).add (((cb.comp flip).pow 2).const_mul (1/2))).intervalIntegrable ..)
        intro u _
        have id : u*B (1-u)=f (1-u) := by
          dsimp [B,edge]
          rw [sub_sub_cancel]
          by_cases e : u=0
          · simp [e,f1]
          · field_simp
        have pc : C u=|A u| * |B (1-u)| := by
          dsimp only [C,A]
          rw [← abs_mul,← id]
          congr 1
          ring
        change 2*C u≤2*A u^2+(1/2)*B (1-u)^2
        rw [pc]
        nlinarith only [sq_nonneg (2*|A u|-|B (1-u)|),sq_abs (A u),sq_abs (B (1-u))]
      _ = _ := by
        rw [intervalIntegral.integral_add (f:=fun t => 2*A t^2) (g:=fun t => (1/2)*B (1-t)^2) (((ca.pow 2).const_mul 2).intervalIntegrable ..)
          ((((cb.comp flip).pow 2).const_mul (1/2)).intervalIntegrable ..),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_sub_left (fun v => B v^2) 1,sub_self,sub_zero]
  have pd (u : ℝ) : HasDerivAt (fun t => t*(f t)^2) (P u) u := by
    convert! (hasDerivAt_id u).mul ((df u).hasDerivAt.pow 2) using 1
    dsimp [P,A]
    ring
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (fun u _ => pd u) (cp.intervalIntegrable ..)
  have zero : (∫ t in (0:ℝ)..1, P t)=0 := by simpa [f1] using eq
  have energy : (∫ t in (0:ℝ)..1, A t^2) ≤ ∫ t in (0:ℝ)..1, J t+(1/2)*P t := by
    apply intervalIntegral.integral_mono_on zero_le_one ((ca.pow 2).intervalIntegrable ..)
      ((cj.add (cp.const_mul (1/2))).intervalIntegrable ..)
    intro u _
    change A u^2≤(f u/2-A u)^2+(1/2)*(f u^2+2*A u*f u)
    nlinarith only [sq_nonneg (f u)]
  rw [intervalIntegral.integral_add (f:=J) (g:=fun t => (1/2)*P t) (cj.intervalIntegrable ..) ((cp.const_mul (1/2)).intervalIntegrable ..),
    intervalIntegral.integral_const_mul,zero,mul_zero,add_zero] at energy
  have hard : (∫ t in (0:ℝ)..1, B t^2)≤4*(∫ t in (0:ℝ)..1, (A t)^2) := boundary_hardy f hf
  rw [intervalIntegral.integral_const_mul] at cBound
  change _≤4*(∫ t in (0:ℝ)..1, J t)
  linarith only [main,cBound,hard,energy]

#print axioms boundary_hardy
#print axioms variation_bound
end GoldbachSpectral435.GoldbachPrimitive
