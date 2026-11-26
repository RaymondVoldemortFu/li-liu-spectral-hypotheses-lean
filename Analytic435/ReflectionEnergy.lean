module
public import ReflectionVariation
public import Energy
public import FiniteDiscrepancy

/-! The first-block mesh estimate in the original Hilbert norm. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set
namespace GoldbachSpectral435.GoldbachPrimitive

/-- Continuous form of the multiplier in the physical energy. -/
def energyWeight (N : ℕ) (a u : ℝ) : ℝ :=
  ((N:ℝ)*max u 0)^(2*beta)/(1+((N:ℝ)*max u 0)^(2*(beta-a)))

lemma energyWeight_continuous (N : ℕ) {a : ℝ} (ha : a<beta) : Continuous (energyWeight N a) := by
  let p := fun u : ℝ => (N:ℝ)*max u 0
  have c : Continuous p := continuous_const.mul (continuous_id.max continuous_const)
  have pos (u : ℝ) : 0≤p u := mul_nonneg (Nat.cast_nonneg _) (le_max_right ..)
  have e : 0<2*beta := by norm_num [beta]
  have d : 0<2*(beta-a) := by linarith
  exact (c.rpow_const (fun _ => Or.inr e.le)).div (continuous_const.add (c.rpow_const (fun _ => Or.inr d.le)))
    (fun u => ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg (pos u) _)))

lemma weight_eq {N : ℕ} (np : 0<N) {u : ℝ} (up : 0<u) (a : ℝ) :
    energyWeight N a u=((N:ℝ)*u)^(2*a)/(1+((N:ℝ)*u)^(-2*(beta-a))) := by
  let x := (N:ℝ)*u
  have xp : 0<x := mul_pos (by exact_mod_cast np) up
  unfold energyWeight
  rw [max_eq_left up.le]
  change x^(2*beta)/(1+x^(2*(beta-a)))=x^(2*a)/(1+x^(-2*(beta-a)))
  have exp : 2*beta=2*a+2*(beta-a) := by ring
  have neg : -2*(beta-a)= -(2*(beta-a)) := by ring
  rw [exp,Real.rpow_add xp,neg,Real.rpow_neg xp.le]
  have pp := Real.rpow_pos_of_pos xp (2*(beta-a))
  field_simp
  ring

private lemma zero_outside {f : ℝ→ℝ} {u : ℝ} (out : u∉tsupport f) :
    physicalDensity f u=0 := by
  simp [physicalDensity,(notMem_tsupport_iff_eventuallyEq.mp out).eq_of_nhds,deriv_of_notMem_tsupport out]

theorem norm_integral (N : ℕ) (np : 0<N) (f : ℝ→ℝ) (hf : FiniteModelWeight f) (a : ℝ) :
    normFunctional N f a = (2*Real.pi)⁻¹ *
      ∫ u in (0:ℝ)..1, energyWeight N a u*(physicalDensity f u)^2 := by
  unfold normFunctional
  congr 1
  rw [intervalIntegral.integral_of_le zero_le_one]
  let v := fun u : ℝ => energyWeight N a u*(physicalDensity f u)^2
  calc
    _ = ∫ u in Ioi (0:ℝ), v u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u up
      have up' : 0<u := up
      dsimp only [v]
      rw [weight_eq np up',derivativeWeight_eq_density (hf.smooth.differentiable (by decide)) up',
        mul_pow,Real.sq_sqrt up'.le]
      simp only [Real.rpow_eq_pow]
      have algebra (A D h : ℝ) : A*(u*h)/D/u=A/D*h := by
        rw [div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv]
        calc
          _ = (A*D⁻¹*h)*(u*u⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ up'.ne',mul_one]
      exact algebra _ _ _
    _ = _ := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun u hu => hu.1)
      intro u h
      have gt : 1<u := lt_of_not_ge (fun le => h.2 ⟨h.1,le⟩)
      have out : u∉tsupport f := fun m =>
        (not_le_of_gt gt) (((closure_minimal hf.support_subset isClosed_Icc m).2).trans hf.upper_lt_one.le)
      simp [v,zero_outside out]

lemma weight_lower {N : ℕ} (np : 0<N) {a u : ℝ} (ap : 0≤a) (ha : a≤beta) (up : 0<u)
    (big : 1≤(N:ℝ)*u) : 1/2≤energyWeight N a u := by
  rw [weight_eq np up a]
  have p := Real.one_le_rpow big (show 0≤2*a by positivity)
  have d := Real.rpow_le_one_of_one_le_of_nonpos big (show -2*(beta-a)≤0 by linarith)
  have nr : 0≤(N:ℝ)*u := zero_le_one.trans big
  apply (le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg nr _))).mpr
  linarith

/-- The physical derivative energy and the Hardy norm are uniformly
comparable from below on the part of the first block with Nu at least one. -/
theorem energy_le_norm (N : ℕ) (np : 0<N) (f : ℝ→ℝ) (hf : FiniteModelWeight f)
    {a : ℝ} (ap : 0≤a) (ha : a<beta) (support : Function.support f⊆Ici ((N:ℝ)⁻¹)) :
    (∫ u in (0:ℝ)..1, (physicalDensity f u)^2)≤4*Real.pi*normFunctional N f a := by
  have cf : Continuous (physicalDensity f) :=
    (hf.continuous.div_const _).sub (continuous_id.mul (hf.smooth.continuous_deriv (by decide)))
  have cv := (energyWeight_continuous N ha).mul (cf.pow 2)
  have cmp : (∫ u in (0:ℝ)..1, (physicalDensity f u)^2) ≤
      ∫ u in (0:ℝ)..1, 2*(energyWeight N a u*(physicalDensity f u)^2) := by
    apply intervalIntegral.integral_mono_on zero_le_one ((cf.pow 2).intervalIntegrable ..)
      ((cv.const_mul 2).intervalIntegrable ..)
    intro u _
    change (physicalDensity f u)^2≤2*(energyWeight N a u*(physicalDensity f u)^2)
    by_cases mem : u∈tsupport f
    · have nr : 0<(N:ℝ) := by exact_mod_cast np
      have lower : (N:ℝ)⁻¹≤u := closure_minimal support isClosed_Ici mem
      have large : 1≤(N:ℝ)*u := by
        rw [mul_comm]
        exact (div_le_iff₀ nr).mp (by simpa only [one_div] using lower : (1:ℝ)/N≤u)
      have b := weight_lower np ap ha.le ((inv_pos.mpr nr).trans_le lower) large
      nlinarith only [mul_nonneg (show 0≤2*energyWeight N a u-1 by linarith) (sq_nonneg (physicalDensity f u))]
    · simp [zero_outside mem]
  rw [intervalIntegral.integral_const_mul] at cmp
  rw [norm_integral N np f hf a]
  apply cmp.trans_eq
  field_simp
  ring

/-- The first-block discrepancy bound now has the energy normalization of
Hypothesis S and a constant independent of both the support and the modulus. -/
theorem normalized_mesh (N m : ℕ) [NeZero N] (he : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (mp : 0<m) (D : ℝ)
    (mesh : ∀ j : ℕ, j≤m → |primitive N (j/(m:ℝ))|≤D)
    (f : ℝ→ℝ) (hf : FiniteModelWeight f) (support : Function.support f⊆Ici ((N:ℝ)⁻¹)) :
    let x := testVector N N (NeZero.pos N) f hf
    ‖paperInner (residualOperator ha N x) x‖≤16*Real.pi*(D+singularSeries N/m)*‖x‖^2 := by
  intro x
  have b := mesh_bound N m he big g ha mp D mesh f hf
  have v := variation_bound f hf
  have e := energy_le_norm N (NeZero.pos N) f hf (large_alpha_pos big).le ha support
  have eq := (FiniteDiscrepancy.exact_form N 1 zero_lt_one he big g ha f hf).1
  simp only [one_mul] at eq
  have dp := (abs_nonneg _).trans (mesh 0 (Nat.zero_le _))
  have sr := div_nonneg (singularSeries_pos N).le (Nat.cast_nonneg m)
  change _≤_ * ‖testVector N N (NeZero.pos N) f hf‖^2
  rw [eq]
  apply b.trans
  change (∫ t in (0:ℝ)..1, |deriv (reflected f) t|)≤4*(∫ t in (0:ℝ)..1, (physicalDensity f t)^2) at v
  calc
    _ ≤ (D+singularSeries N/m)*(4*(4*Real.pi*normFunctional N f (alpha N))) :=
      mul_le_mul_of_nonneg_left (v.trans (mul_le_mul_of_nonneg_left e (by norm_num))) (add_nonneg dp sr)
    _ = _ := by ring

#print axioms normalized_mesh
end GoldbachSpectral435.GoldbachPrimitive
