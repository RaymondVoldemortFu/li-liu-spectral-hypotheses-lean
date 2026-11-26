module
public import ConditionalGoldbach.Proofs.PoleModel
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The linear term in the regularized Euler product governing the
conductor dependence of the Li–Liu model. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Set Complex
open scoped Topology
namespace GoldbachSpectral435.ConductorCorrection

def localCorrection (N : ℕ) : ℂ := ∑ p ∈ N.primeFactors, Complex.log (p:ℂ)/((p:ℂ)-1)

private lemma factor_flat (N p : ℕ) :
    HasDerivAt (fun w : ℂ => 1+baselineEulerTerm N p w) 0 0 := by
  let d := deriv (densityEulerTerm N p) 1
  have base : HasDerivAt (densityEulerTerm N p) d 1 :=
    (densityEulerTerm_differentiable N p 1).hasDerivAt
  have a : HasDerivAt (fun w : ℂ => 1+w) 1 0 := by simpa using (hasDerivAt_id (0:ℂ)).const_add 1
  have b : HasDerivAt (fun w : ℂ => 1+2*w) 2 0 := by simpa using ((hasDerivAt_id (0:ℂ)).const_mul 2).const_add 1
  have da := (by simpa using base : HasDerivAt (densityEulerTerm N p) d (1+(0:ℂ))).comp 0 a
  have db := (by simpa using base : HasDerivAt (densityEulerTerm N p) d (1+2*(0:ℂ))).comp 0 b
  convert (((da.const_mul 2).sub db).const_add 1) using 1
  · rfl
  · ring

private lemma infinite_flat (N : ℕ) :
    HasDerivAt (fun w : ℂ => ∏' p, (1+baselineEulerTerm N p w)) 0 0 := by
  have ho : IsOpen {w : ℂ | -(1/4:ℝ)<w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs : Summable (fun p => 9*‖LSeries.term 1 (3/2:ℂ) p‖) :=
    ((LSeriesSummable_one_iff.mpr (by norm_num : (1:ℝ)<(3/2:ℂ).re)).norm).mul_left 9
  have hu : TendstoLocallyUniformlyOn
      (fun k w => ∏ p ∈ Finset.range k, (1+baselineEulerTerm N p w))
      (fun w => ∏' p, (1+baselineEulerTerm N p w)) atTop {w : ℂ | -(1/4:ℝ)<w.re} := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact ho).2
    intro K hKU hK
    have hh := hs.hasProdUniformlyOn_nat_one_add hK
      (Eventually.of_forall (fun p w hw => baselineEulerTerm_bound N p w (hKU hw)))
      (fun p => (baselineEulerTerm_differentiable N p).continuous.continuousOn)
    exact hh.tendstoUniformlyOn_finsetRange
  have part (k : ℕ) : Differentiable ℂ (fun w : ℂ => ∏ p ∈ Finset.range k, (1+baselineEulerTerm N p w)) := by
    apply Differentiable.fun_finsetProd
    intro p _
    exact (differentiable_const (1:ℂ)).add (baselineEulerTerm_differentiable N p)
  have z : (0:ℂ)∈{w : ℂ | -(1/4:ℝ)<w.re} := by norm_num
  have lim := (hu.deriv (Eventually.of_forall (fun k => (part k).differentiableOn)) ho).tendsto_at z
  have finite (k : ℕ) : HasDerivAt (fun w : ℂ => ∏ p ∈ Finset.range k, (1+baselineEulerTerm N p w)) 0 0 := by
    simpa using HasDerivAt.fun_finsetProd (u:=Finset.range k) (fun p _ => factor_flat N p)
  have eq : deriv (fun w : ℂ => ∏' p, (1+baselineEulerTerm N p w)) 0=0 := by
    apply tendsto_nhds_unique lim
    exact (show Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0) from tendsto_const_nhds).congr (fun k => (finite k).deriv.symm)
  simpa only [eq] using ((baselineEulerProduct_differentiableOn N).differentiableAt (ho.mem_nhds z)).hasDerivAt

private lemma finite_derivative (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) :
    HasDerivAt (fun w : ℂ => ∏ p ∈ P, (1-(p:ℂ)^(-1-w)))
      ((∏ p ∈ P, (1-(p:ℂ)^(-1-(0:ℂ))))*(∑ p ∈ P, Complex.log (p:ℂ)/((p:ℂ)-1))) 0 := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa using hasDerivAt_const (0:ℂ) (1:ℂ)
  | @insert p S fresh ih =>
    have pp := pr p (Finset.mem_insert_self ..)
    have pc : (p:ℂ)≠0 := by exact_mod_cast pp.ne_zero
    have one : (p:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast pp.ne_one)
    have h := ((hasDerivAt_const (0:ℂ) (-1:ℂ)).sub (hasDerivAt_id 0)).const_cpow (c:=(p:ℂ)) (Or.inl pc)
    have deriv : HasDerivAt (fun w : ℂ => 1-(p:ℂ)^(-1-w))
        ((1-(p:ℂ)^(-1-(0:ℂ)))*(Complex.log (p:ℂ)/((p:ℂ)-1))) 0 := by
      convert (hasDerivAt_const (0:ℂ) (1:ℂ)).sub h using 1
      all_goals first | rfl | (dsimp; simp only [sub_zero,Complex.cpow_neg_one,zero_sub]; field_simp)
    simp only [Finset.prod_insert fresh,Finset.sum_insert fresh]
    convert deriv.mul (ih (fun v hv => pr v (Finset.mem_insert_of_mem hv))) using 1
    ring

/-- The normalized product has value one at zero. Its derivative sees only
the primes in the conductor, with no contribution from any other prime. -/
theorem normalized_product_derivative (N : ℕ) (he : Even N) (np : 0<N) :
    HasDerivAt (fun w : ℂ => (singularSeries N:ℂ)*baselineProductR N w) (localCorrection N) 0 := by
  let F := fun w : ℂ => ∏ p ∈ N.primeFactors, (1-(p:ℂ)^(-1-w))
  let G := fun w : ℂ => ∏' p, (1+baselineEulerTerm N p w)
  have eq (w : ℂ) : baselineProductR N w = F w*G w := by
    unfold baselineProductR F G
    congr 1
    exact (tprod_congr (fun p => baselineEulerTerm_eq N p w)).symm
  have val := baselineProductR_zero N he np
  rw [eq] at val
  have a : HasDerivAt F (F 0*localCorrection N) 0 :=
    finite_derivative _ (fun _ h => Nat.prime_of_mem_primeFactors h)
  have d := (a.mul (infinite_flat N)).const_mul (singularSeries N:ℂ)
  simp_rw [eq]
  convert d using 1
  change localCorrection N=(singularSeries N:ℂ)*(F 0*localCorrection N*G 0+F 0*0)
  linear_combination -(localCorrection N)*val

/-- Constant term after removing the pole of the original continued
density. The limit approaches zero from the open right half-plane. -/
theorem density_finite_part (N : ℕ) (he : Even N) (np : 0<N) :
    Tendsto (fun w : ℂ => continuedDensity N w+(2*w)⁻¹)
      (𝓝[{w : ℂ | 0<w.re}] 0)
      (𝓝 (-(Complex.log (2*(Real.pi:ℂ)) + (Real.eulerMascheroniConstant:ℂ) + localCorrection N)/2)) := by
  let F := fun w : ℂ => (singularSeries N:ℂ)*baselineProductR N w
  let H := fun w : ℂ => F w*riemannZeta w*riemannZeta₁ (1+w)
  have f0 : F 0=1 := baselineProductR_zero N he np
  have h0 : H 0=(-1/2:ℂ) := by simp [H,f0,riemannZeta_zero,riemannZeta₁_one]
  have z := (differentiableAt_riemannZeta (by norm_num : (0:ℂ)≠1)).hasDerivAt
  have a : HasDerivAt (fun w : ℂ => 1+w) 1 0 := by simpa using (hasDerivAt_id (0:ℂ)).const_add 1
  have b := (differentiable_riemannZeta₁ (1+(0:ℂ))).hasDerivAt.comp 0 a
  have dh : HasDerivAt H
      (-(Complex.log (2*(Real.pi:ℂ))+(Real.eulerMascheroniConstant:ℂ)+localCorrection N)/2) 0 := by
    have first : HasDerivAt F (localCorrection N) 0 := normalized_product_derivative N he np
    convert (first.mul z).mul b using 1
    all_goals first | rfl | (simp only [Function.comp_apply,Pi.mul_apply,f0,riemannZeta_zero,deriv_riemannZeta_zero,add_zero,riemannZeta₁_one,
      deriv_riemannZeta₁_one,mul_one,one_mul]; ring)
  have region : {w : ℂ | 0<w.re} ⊆ ({0}:Set ℂ)ᶜ := by
    intro w h eq
    have wz : w=0 := eq
    simp [wz] at h
  apply ((hasDerivAt_iff_tendsto_slope_zero.mp dh).mono_left (nhdsWithin_mono _ region)).congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have wp : 0<w.re := hw
  have wn : w≠0 := fun e => by simp [e] at wp
  have wo : 1+w≠(1:ℂ) := by simpa using wn
  rw [zero_add,h0,smul_eq_mul]
  unfold continuedDensity
  rw [densityEulerProduct_eq_zeta_baseline N he np wp,riemannZeta_eq_inv_sub_mul wo]
  dsimp [H,F]
  rw [add_sub_cancel_left]
  field_simp
  ring

#print axioms density_finite_part
#print axioms normalized_product_derivative
end GoldbachSpectral435.ConductorCorrection
