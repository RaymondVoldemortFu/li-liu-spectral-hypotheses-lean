module
public import PrimitiveEndpoints

/-! Weighted Hardy estimates for all first-scale tests, including those
with support below the first integer. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set
namespace GoldbachSpectral435.GoldbachPrimitive

def average (f : ℝ→ℝ) : ℝ := ∫ t in (0:ℝ)..1, f t

lemma average_le {f g : ℝ→ℝ} (cf : Continuous f) (cg : Continuous g)
    (h : ∀ t∈Icc (0:ℝ) 1, f t≤g t) : average f≤average g :=
  intervalIntegral.integral_mono_on zero_le_one (cf.intervalIntegrable ..) (cg.intervalIntegrable ..) h

lemma average_linear {f g : ℝ→ℝ} (cf : Continuous f) (cg : Continuous g) (a b : ℝ) :
    average (fun t => a*f t+b*g t)=a*average f+b*average g := by
  unfold average
  rw [intervalIntegral.integral_add (f:=fun t => a*f t) (g:=fun t => b*g t)
    ((cf.const_mul a).intervalIntegrable ..) ((cg.const_mul b).intervalIntegrable ..),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

lemma average_flip (f : ℝ→ℝ) : average (fun t => f (1-t))=average f := by
  unfold average
  rw [intervalIntegral.integral_comp_sub_left,sub_self,sub_zero]

def weightedTest (N : ℕ) (f : ℝ→ℝ) (u : ℝ) := cutoffWeight N u*f u

def weightedTestWeight (N : ℕ) {f : ℝ→ℝ} (hf : FiniteModelWeight f) :
    FiniteModelWeight (weightedTest N f) :=
  ⟨(cutoff_smooth N).mul hf.smooth,_,_,hf.lower_pos,hf.upper_lt_one,hf.lower_le_upper,
    fun _ h => hf.mem_support_interval (mul_ne_zero_iff.mp h).2⟩

private def slope (N : ℕ) (f : ℝ→ℝ) (u : ℝ) := cutoffWeight N u*(u*deriv f u)
private def weightSlope (N : ℕ) (f : ℝ→ℝ) (u : ℝ) := (u*deriv (cutoffWeight N) u)*f u
def energyDensity (N : ℕ) (f : ℝ→ℝ) (u : ℝ) := (cutoffWeight N u*physicalDensity f u)^2

private lemma slopes {N : ℕ} {f : ℝ→ℝ} (hf : FiniteModelWeight f) (u : ℝ) :
    u*deriv (weightedTest N f) u=slope N f u+weightSlope N f u := by
  have d := ((cutoff_deriv N u).mul (hf.smooth.differentiable (by decide) u).hasDerivAt).deriv
  change u*deriv (fun t => cutoffWeight N t*f t) u=_
  rw [show deriv (fun t => cutoffWeight N t*f t) u=_ from d]
  dsimp [slope,weightSlope]
  rw [(cutoff_deriv N u).deriv]
  ring

private lemma weightSlope_sq {N : ℕ} {f : ℝ→ℝ} {u : ℝ} (up : 0≤u) :
    weightSlope N f u^2≤weightedTest N f u^2 := by
  have p : 0≤u*deriv (cutoffWeight N) u := by rw [(cutoff_deriv N u).deriv]; positivity
  unfold weightSlope weightedTest
  rw [mul_pow (u*deriv (cutoffWeight N) u),mul_pow (cutoffWeight N u)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ p (cutoff_bounds N up).2.2.2.2 _) (sq_nonneg _)

private lemma slope_cont (N : ℕ) {f : ℝ→ℝ} (hf : FiniteModelWeight f) : Continuous (slope N f) :=
  (cutoff_smooth N).continuous.mul (continuous_id.mul (hf.smooth.continuous_deriv (by decide)))

private lemma energy_cont (N : ℕ) {f : ℝ→ℝ} (hf : FiniteModelWeight f) :
    Continuous (energyDensity N f) :=
  ((cutoff_smooth N).continuous.mul ((hf.continuous.div_const 2).sub
    (continuous_id.mul (hf.smooth.continuous_deriv (by decide))))).pow 2

private lemma coercivity (N : ℕ) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    average (fun u => slope N f u^2)+(3/4)*average (fun u => weightedTest N f u^2)
      ≤ average (energyDensity N f) := by
  let A := slope N f
  let V := weightedTest N f
  let Q := energyDensity N f
  let H := fun t : ℝ => V t^2+2*t*V t*deriv V t
  have cV := (weightedTestWeight N hf).smooth
  have cA := slope_cont N hf
  have cQ := energy_cont N hf
  have cH : Continuous H := (cV.continuous.pow 2).add (((continuous_const.mul continuous_id).mul cV.continuous).mul
    (cV.continuous_deriv (by decide)))
  have hd (u : ℝ) : HasDerivAt (fun t => t*V t^2) (H u) u := by
    convert! (hasDerivAt_id u).mul ((cV.differentiable (by decide) u).hasDerivAt.pow 2) using 1
    dsimp [H]; ring
  have f1 : V 1=0 := by
    by_contra nz
    exact lt_irrefl 1 ((weightedTestWeight N hf).mem_support_unit nz).2
  have hz : average H=0 := by
    simpa [average,f1] using intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
      (fun u _ => hd u) (cH.intervalIntegrable ..)
  have cmp : average (fun t => 1*(A t)^2+(3/4)*(V t)^2)≤average (fun t => 1*Q t+(1/2)*H t) := by
    apply average_le (((cA.pow 2).const_mul 1).add ((cV.continuous.pow 2).const_mul (3/4)))
      ((cQ.const_mul 1).add (cH.const_mul (1/2)))
    intro u hu
    have ident : Q u=(V u/2-A u)^2 := by dsimp [Q,V,A,energyDensity,physicalDensity,weightedTest,slope]; ring
    have der : u*deriv V u=A u+weightSlope N f u := slopes hf u
    have non : 0≤V u*weightSlope N f u := by
      dsimp [V,weightedTest,weightSlope]
      rw [show cutoffWeight N u*f u*(u*deriv (cutoffWeight N) u*f u)=
        (cutoffWeight N u*u*deriv (cutoffWeight N) u)*f u^2 by ring,(cutoff_deriv N u).deriv]
      exact mul_nonneg (mul_nonneg (mul_nonneg (cutoff_bounds N hu.1).1 hu.1)
        (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)) (sq_nonneg _)
    change 1*A u^2+(3/4)*V u^2≤1*Q u+(1/2)*H u
    have h : H u=V u^2+2*V u*(A u+weightSlope N f u) := by dsimp [H]; rw [← der]; ring
    rw [ident,h]
    nlinarith only [non]
  rw [average_linear (f:=fun t => A t^2) (g:=fun t => V t^2) (cA.pow 2) (cV.continuous.pow 2),
    average_linear (f:=Q) (g:=H) cQ cH,hz] at cmp
  simpa using cmp

lemma weighted_energy_le (N : ℕ) (np : 0<N) {a : ℝ} (ap : 0≤a) (ab : a<beta)
    (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    average (energyDensity N f)≤4*Real.pi*normFunctional N f a := by
  have c : Continuous (physicalDensity f) := (hf.continuous.div_const 2).sub
    (continuous_id.mul (hf.smooth.continuous_deriv (by decide)))
  have cmp : average (energyDensity N f)≤average (fun t => 2*(energyWeight N a t*(physicalDensity f t)^2)) := by
    apply average_le (energy_cont N hf) (((energyWeight_continuous N ab).mul (c.pow 2)).const_mul 2)
    intro u hu
    change (cutoffWeight N u*physicalDensity f u)^2≤2*(energyWeight N a u*(physicalDensity f u)^2)
    rw [mul_pow,← mul_assoc]
    exact mul_le_mul_of_nonneg_right (cutoff_sq_le N np ap ab hu.1) (sq_nonneg _)
  unfold average at cmp
  rw [intervalIntegral.integral_const_mul] at cmp
  apply cmp.trans_eq
  rw [norm_integral N np f hf a]
  field_simp
  ring

private lemma reflected_product (A B : ℝ→ℝ) (ca : Continuous A) (cb : Continuous B) :
    2*average (fun t => |A t*B (1-t)|)≤average (fun t => A t^2)+average (fun t => B t^2) := by
  have flip : Continuous (fun t : ℝ => 1-t) := continuous_const.sub continuous_id
  let L := fun t : ℝ => |A t*B (1-t)|
  have cL : Continuous L := (ca.mul (cb.comp flip)).abs
  have cmp : average (fun t => 2*L t+0*L t)≤average (fun t => 1*(A t)^2+1*(B (1-t))^2) := by
    apply average_le ((cL.const_mul 2).add (cL.const_mul 0))
      (((ca.pow 2).const_mul 1).add (((cb.comp flip).pow 2).const_mul 1))
    intro u _
    change 2*|A u*B (1-u)|+0*L u≤1*A u^2+1*B (1-u)^2
    rw [abs_mul]
    nlinarith only [sq_nonneg (|A u|-|B (1-u)|),sq_abs (A u),sq_abs (B (1-u))]
  rw [average_linear (f:=L) (g:=L) cL cL,
    average_linear (f:=fun u => A u^2) (g:=fun u => B (1-u)^2) (ca.pow 2) ((cb.comp flip).pow 2),
    average_flip (fun u => B u^2)] at cmp
  simpa only [zero_mul,add_zero,one_mul] using cmp

private lemma symmetrize {q L : ℝ→ℝ} (cq : Continuous q) (cL : Continuous L) (c : ℝ)
    (point : ∀ t∈Icc (0:ℝ) 1, q t≤c*L t+c*L (1-t)) : average q≤c*(2*average L) := by
  have flip : Continuous (fun t : ℝ => 1-t) := continuous_const.sub continuous_id
  have h := average_le (f:=q) (g:=fun t => c*L t+c*L (1-t)) cq ((cL.const_mul c).add ((cL.comp flip).const_mul c)) point
  rw [average_linear (f:=L) (g:=fun t => L (1-t)) cL (cL.comp flip),average_flip] at h
  exact h.trans_eq (by ring)

private lemma cutoff_ge_half_coordinate {N : ℕ} (np : 0<N) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    t/2≤cutoffWeight N t := by
  apply le_trans _ (cutoff_lower N ht.1)
  split_ifs
  · linarith [ht.2]
  · have := mul_le_mul_of_nonneg_right (by exact_mod_cast np : (1:ℝ)≤N) ht.1
    linarith

/-- Simultaneous weighted variation and mass estimates, with absolute
constants independent of how close the support comes to zero. -/
theorem weighted_bounds (N : ℕ) (np : 0<N) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    average (fun t => cutoffWeight N t*cutoffWeight N (1-t)*|deriv (reflected f) t|)≤12*average (energyDensity N f) ∧
      average (fun t => |reflected f t|)≤48*average (energyDensity N f) := by
  let v := cutoffWeight N
  let g := weightedTest N f
  let A := slope N f
  let B := fun t : ℝ => g t/(1-t)
  let Q := energyDensity N f
  have hg := weightedTestWeight N hf
  have cg : Continuous g := hg.continuous
  have cv : Continuous v := (cutoff_smooth N).continuous
  have ca : Continuous A := slope_cont N hf
  have flip : Continuous (fun t : ℝ => 1-t) := continuous_const.sub continuous_id
  have cb : Continuous B := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases eq : x=1
    · subst x
      apply (continuousAt_const (y:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hg.upper_lt_one] with t h
      have z : g t=0 := by by_contra nz; exact (not_le_of_gt h) (hg.mem_support_interval nz).2
      simp [B,z]
    · exact cg.continuousAt.div flip.continuousAt (sub_ne_zero.mpr (Ne.symm eq))
  have g1 : g 1=0 := by by_contra nz; exact lt_irrefl 1 (hg.mem_support_unit nz).2
  have recover (u : ℝ) : u*B (1-u)=g (1-u) := by
    dsimp [B]
    rw [sub_sub_cancel]
    by_cases z : u=0
    · simp [z,g1]
    · field_simp
  have core := coercivity N f hf
  have hard : average (fun u => B u^2)≤4*average (fun u => (u*deriv g u)^2) := boundary_hardy g hg
  have derivB : average (fun u => (u*deriv g u)^2) ≤ 2*average (fun u => A u^2)+2*average (fun u => g u^2) := by
    rw [← average_linear (f:=fun u => A u^2) (g:=fun u => g u^2) (ca.pow 2) (cg.pow 2)]
    apply average_le ((continuous_id.mul (hg.smooth.continuous_deriv (by decide))).pow 2)
      (((ca.pow 2).const_mul 2).add ((cg.pow 2).const_mul 2))
    intro u hu
    change (u*deriv g u)^2≤2*A u^2+2*g u^2
    rw [show u*deriv g u=A u+weightSlope N f u from slopes hf u]
    nlinarith only [sq_nonneg (A u-weightSlope N f u),weightSlope_sq (N:=N) (f:=f) hu.1]
  have hA : 0≤average (fun u => A u^2) := intervalIntegral.integral_nonneg zero_le_one (fun u _ => sq_nonneg _)
  have hg0 : 0≤average (fun u => g u^2) := intervalIntegral.integral_nonneg zero_le_one (fun u _ => sq_nonneg _)
  change average (fun t => A t^2)+(3/4)*average (fun t => g t^2)≤average Q at core
  have t1 := hf.smooth.of_le (by decide : (1:WithTop ℕ∞)≤6)
  have refl : ContDiff ℝ 1 (reflected f) := t1.mul (t1.comp (contDiff_const.sub contDiff_id))
  constructor
  · let L := fun t : ℝ => |A t*B (1-t)|
    have cL : Continuous L := (ca.mul (cb.comp flip)).abs
    have single (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
        v t*v (1-t)*|deriv f t*f (1-t)|=L t := by
      have eq : A t*B (1-t)=v t*v (1-t)*(deriv f t*f (1-t)) := by
        calc
          _ = v t*deriv f t*(t*B (1-t)) := by dsimp [A,slope,v]; ring
          _ = _ := by rw [recover]; dsimp [g,weightedTest,v]; ring
      dsimp only [L]
      rw [eq,abs_mul (v t*v (1-t)),abs_of_nonneg (mul_nonneg (cutoff_bounds N ht.1).1 (cutoff_bounds N (sub_nonneg.mpr ht.2)).1)]
    have d (t : ℝ) : deriv (reflected f) t=deriv f t*f (1-t)-f t*deriv f (1-t) := by
      have df := hf.smooth.differentiable (by decide)
      have der := (df t).hasDerivAt.mul ((df (1-t)).hasDerivAt.comp t
        ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)))
      exact der.deriv.trans (by simp only [Function.comp_apply]; ring)
    have main := symmetrize (q:=fun t => v t*v (1-t)*|deriv (reflected f) t|)
      ((cv.mul (cv.comp flip)).mul ((refl.continuous_deriv (by decide)).abs)) cL 1 (by
        intro t ht
        have ht' : 1-t∈Icc (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
        have other := single (1-t) ht'
        rw [sub_sub_cancel,mul_comm (v (1-t)),mul_comm (deriv f (1-t))] at other
        rw [one_mul,one_mul,← single t ht,← other,d,← mul_add]
        exact mul_le_mul_of_nonneg_left (abs_sub ..) (mul_nonneg (cutoff_bounds N ht.1).1 (cutoff_bounds N ht'.1).1))
    have prod : 2*average L≤average (fun u => A u^2)+average (fun u => B u^2) := reflected_product A B ca cb
    change _≤12*average Q
    linarith only [main,prod,hard,derivB,core,hA,hg0]
  · let L := fun t : ℝ => |g t*B (1-t)|
    have cL : Continuous L := (cg.mul (cb.comp flip)).abs
    have main := symmetrize (q:=fun t => |reflected f t|) refl.continuous.abs cL 4 (by
      intro t ht
      have r : 1-t∈Icc (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
      by_cases tz : t=0
      · subst t
        simp [reflected,hf.eq_zero_of_nonpos le_rfl,L]
        positivity
      by_cases teq : t=1
      · subst t
        simp [reflected,hf.eq_zero_of_nonpos le_rfl,L]
        positivity
      have tp := lt_of_le_of_ne ht.1 (Ne.symm tz)
      have rp := sub_pos.mpr (lt_of_le_of_ne ht.2 teq)
      have prod := mul_le_mul (cutoff_ge_half_coordinate np ht) (cutoff_ge_half_coordinate np r)
        (div_nonneg r.1 (by norm_num)) (cutoff_bounds N ht.1).1
      have factor : t*(1-t)≤4*(v t*v (1-t)) := by linarith
      have par : t*(1-t)*(L t+L (1-t))=(v t*v (1-t))*|reflected f t| := by
        unfold L B g weightedTest reflected
        rw [sub_sub_cancel]
        simp only [abs_mul,abs_div,abs_of_nonneg (cutoff_bounds N ht.1).1,abs_of_nonneg (cutoff_bounds N r.1).1,
          abs_of_nonneg ht.1,abs_of_nonneg r.1]
        dsimp only [v]
        field_simp
        ring
      apply le_of_mul_le_mul_left (a:=t*(1-t)) _ (mul_pos tp rp)
      have pay := mul_le_mul_of_nonneg_right factor (abs_nonneg (reflected f t))
      linarith only [show t*(1-t)*(4*L t+4*L (1-t))=4*(v t*v (1-t))*|reflected f t| by linear_combination 4*par,pay])
    have prod : 2*average L≤average (fun u => g u^2)+average (fun u => B u^2) := reflected_product g B cg cb
    change _≤48*average Q
    linarith only [main,prod,hard,derivB,core,hA,hg0]

#print axioms weighted_bounds
#print axioms weighted_energy_le
end GoldbachSpectral435.GoldbachPrimitive
