module
public import WeightedReflection

/-! A bound on the original first-scale quadratic form with no restriction
on the distance of the test support from either endpoint. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Finset
namespace GoldbachSpectral435.GoldbachPrimitive

private lemma bridge_measurable (N : ℕ) : Measurable (bridge N) := by
  unfold bridge primitive
  apply Measurable.sub _ (measurable_id.mul measurable_const)
  apply Measurable.sub _ (measurable_const.mul measurable_id)
  apply Finset.measurable_fun_sum
  intro n _
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const

/-- A single Kolmogorov discrepancy bound at the first scale controls the
quadratic form on every original real-weight test in its own Hardy norm. -/
theorem first_scale_bound (N : ℕ) [NeZero N] (he : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (D : ℝ)
    (bound : ∀ t∈Set.Icc (0:ℝ) 1, |primitive N t|≤D)
    (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let x := testVector N N (NeZero.pos N) f hf
    ‖paperInner (residualOperator ha N x) x‖≤
      576*Real.pi*(D+singularSeries N/N)*‖x‖^2 := by
  intro x
  let K := D+singularSeries N/N
  let S := primitive N 1
  let F := reflected f
  let v := cutoffWeight N
  let P := fun t : ℝ => v t*v (1-t)*|deriv F t|
  let Q := average (energyDensity N f)
  let H := normFunctional N f (alpha N)
  have n2 : 2≤N := by have := (large_parameters big).1; omega
  have ep : |S|≤D := bound 1 ⟨zero_le_one,le_rfl⟩
  have dp := (abs_nonneg _).trans ep
  have dk : D≤K := le_add_of_nonneg_right (div_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N))
  have kp := dp.trans dk
  have s1 := hf.smooth.of_le (by decide : (1:WithTop ℕ∞)≤6)
  have cF : ContDiff ℝ 1 F := s1.mul (s1.comp (contDiff_const.sub contDiff_id))
  have dc := cF.continuous_deriv (by decide)
  have cv : Continuous v := (cutoff_smooth N).continuous
  have cP : Continuous P := (cv.mul (cv.comp (continuous_const.sub continuous_id))).mul dc.abs
  have ct : Continuous (fun t : ℝ => S*(t*deriv F t)) := (continuous_id.mul dc).const_mul _
  have compare (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) : ‖bridge N t*deriv F t‖≤8*K*P t := by
    rw [Real.norm_eq_abs,abs_mul]
    apply (mul_le_mul_of_nonneg_right (bridge_bound N n2 D bound ht) (abs_nonneg _)).trans_eq
    dsimp [P,K,v]; ring
  have mi : Measurable (fun t => bridge N t*deriv F t) := (bridge_measurable N).mul dc.measurable
  have integ : IntervalIntegrable (fun t : ℝ => bridge N t*deriv F t) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    apply ((cP.const_mul (8*K)).intervalIntegrable 0 1).1.mono' mi.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact compare t ⟨ht.1.le,ht.2⟩
  have pay : |average (fun t => bridge N t*deriv F t)|≤8*K*average P := by
    unfold average
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,← integral_const_mul]
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le ((cP.const_mul (8*K)).intervalIntegrable 0 1).1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact compare t ⟨ht.1.le,ht.2⟩
  have fzero : F 1=0 := by simp [F,reflected,hf.eq_zero_of_nonpos le_rfl]
  have integrate := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (u:=fun t : ℝ => t) (u':=fun _ => (1:ℝ)) (v:=F) (v':=deriv F)
    continuous_id.continuousOn cF.continuous.continuousOn (fun t _ => hasDerivAt_id t)
    (fun t _ => (cF.differentiable (by decide) t).hasDerivAt) (by simp) (dc.intervalIntegrable ..)
  simp only [fzero,mul_zero,zero_mul,sub_zero,zero_sub,one_mul] at integrate
  have orig : average (fun t => primitive N t*deriv F t)=
      average (fun t => bridge N t*deriv F t)-S*average F := by
    have pt (t : ℝ) : primitive N t*deriv F t=bridge N t*deriv F t+S*(t*deriv F t) := by
      dsimp [bridge,S]; ring
    unfold average
    simp_rw [pt]
    rw [intervalIntegral.integral_add (f:=fun t => bridge N t*deriv F t) (g:=fun t => S*(t*deriv F t))
      integ (ct.intervalIntegrable ..),intervalIntegral.integral_const_mul,integrate]
    ring
  obtain ⟨var,mass⟩ := weighted_bounds N (NeZero.pos N) f hf
  change average P≤12*Q at var
  change average (fun t => |F t|)≤48*Q at mass
  have energy : Q≤4*Real.pi*H := weighted_energy_le N (NeZero.pos N) (large_alpha_pos big).le ha f hf
  have absF : |average F|≤average (fun t => |F t|) := by
    simpa only [average,Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f:=F) (μ:=volume) (a:=(0:ℝ)) (b:=1) zero_le_one
  have cut := (FiniteDiscrepancy.exact_form N 1 zero_lt_one he big grh ha f hf).1
  simp only [one_mul] at cut
  rw [exact_integral N he big grh ha f hf,Complex.norm_real,Real.norm_eq_abs]
  change |average (fun t => primitive N t*deriv F t)|≤576*Real.pi*K*‖testVector N N (NeZero.pos N) f hf‖^2
  rw [cut,orig]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  calc
    _ ≤ 8*K*(12*Q)+K*(48*Q) := add_le_add (pay.trans (mul_le_mul_of_nonneg_left var (by positivity)))
      (mul_le_mul (ep.trans dk) (absF.trans mass) (abs_nonneg _) kp)
    _ = 144*K*Q := by ring
    _ ≤ 144*K*(4*Real.pi*H) := mul_le_mul_of_nonneg_left energy (by positivity)
    _ = _ := by dsimp [H]; ring

/-- A certificate from an arbitrary finite uniform mesh, in the norm used
by S and uniformly over all individual first-scale test weights. -/
theorem first_scale_mesh (N m : ℕ) [NeZero N] (he : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (mp : 0<m) (D : ℝ)
    (mesh : ∀ j : ℕ, j≤m → |primitive N (j/(m:ℝ))|≤D)
    (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let x := testVector N N (NeZero.pos N) f hf
    ‖paperInner (residualOperator ha N x) x‖≤
      576*Real.pi*(D+singularSeries N/m+singularSeries N/N)*‖x‖^2 :=
  first_scale_bound N he big grh ha _ (between_mesh_points N m mp D mesh) f hf

#print axioms first_scale_bound
#print axioms first_scale_mesh
end GoldbachSpectral435.GoldbachPrimitive
