module
public import PeriodicModel

/-! Squarefree denominator truncations for the singular series. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Finset Filter ConditionalGoldbach
namespace GoldbachSpectral435.GoldbachSieve
open GoldbachSpectral PhysicalTests
open MathlibNt.SieveTheory.MertensTheorem (primeProduct)

def localCoefficient (H p : ℕ) : ℝ :=
  if p∣H then 1/((p:ℝ)-1) else -(1/((p:ℝ)-1)^2)

def denominatorSum (H Q : ℕ) : ℝ :=
  ∑ T∈(smallPrimes Q).powerset,
    if (∏ p∈T,p)≤Q then ∏ p∈T,localCoefficient H p else 0

lemma signed_product (H Q : ℕ) (hp : 0<H) (ev : Even H) (qq : 2≤Q) :
    (∏ p∈smallPrimes Q, (1+localCoefficient H p))=truncatedSeries H Q := by
  have pos (p : ℕ) (mem : p∈smallPrimes Q) : (1:ℝ)<p := by exact_mod_cast (mem_filter.mp mem).2.one_lt
  have fac (p : ℕ) (mem : p∈smallPrimes Q) :
      (1-1/(p:ℝ))^2*(1+localCoefficient H p)=1-localDensity H p := by
    have gt := pos p mem
    have np : (p:ℝ)≠0 := by linarith
    have de : (p:ℝ)-1≠0 := by linarith
    unfold localCoefficient localDensity
    split_ifs <;> field_simp <;> ring
  have wpos : 0<primeProduct Q := prod_pos (fun p mem =>
    sub_pos.mpr ((div_lt_one (by linarith only [pos p mem])).mpr (pos p mem)))
  apply mul_left_cancel₀ (pow_pos wpos 2).ne'
  rw [← density_identity H Q hp ev qq,survivingDensity]
  change (∏ p∈smallPrimes Q,(1-1/(p:ℝ)))^2*_ = _
  rw [← prod_pow,← prod_mul_distrib]
  exact prod_congr rfl fac

private lemma finite_twin (P : Finset ℕ) : (1/2:ℝ)≤∏ p∈P,twinFactor p := by
  apply twin_convergence.2.trans
  apply le_of_tendsto twin_convergence.1.hasProd
  filter_upwards [eventually_ge_atTop P] with S h
  exact prod_anti_set_of_le_one₀ (fun p => (twinFactor_unit p).1) (fun p => (twinFactor_unit p).2) h

lemma absolute_product (H : ℕ) (ev : Even H) (P : Finset ℕ) (pr : ∀ p∈P,p.Prime) :
    (∏ p∈P,(1+|localCoefficient H p|))≤4*∏ p∈P,(1+localCoefficient H p) := by
  let w := localCoefficient H
  have fac (p : ℕ) (mem : p∈P) : (1+|w p|)*twinFactor p^2≤1+w p := by
    have one : (1:ℝ)<p := by exact_mod_cast (pr p mem).one_lt
    have den : 0<(p:ℝ)-1 := by linarith
    by_cases d : p∣H
    · have wp : 0≤w p := by simp only [w,localCoefficient,ite_eq_left d]; positivity
      rw [abs_of_nonneg wp]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (twinFactor_unit p).1 (twinFactor_unit p).2)
    · have gt : 2<p := by
        have t := (pr p mem).two_le
        by_contra! le
        have eq : p=2 := by omega
        exact d (eq ▸ even_iff_two_dvd.mp ev)
      let a := 1/((p:ℝ)-1)^2
      have an : 0≤a := by dsimp [a]; positivity
      have id : twinFactor p=1-a := ite_eq_left ⟨pr p mem,gt⟩
      have wp : w p= -a := ite_eq_right d
      rw [wp,abs_neg,abs_of_nonneg an, id]
      have ap := (twinFactor_unit p).1
      rw [id] at ap
      nlinarith only [mul_nonneg (sq_nonneg a) ap]
  have cmp := prod_le_prod₀ (fun p (_ : p∈P) => mul_nonneg (by positivity : 0≤1+|w p|) (sq_nonneg (twinFactor p))) fac
  rw [prod_mul_distrib,prod_pow] at cmp
  have lo := finite_twin P
  have sq : (1/4:ℝ)≤(∏ p∈P,twinFactor p)^2 := by nlinarith only [sq_nonneg ((∏ p∈P,twinFactor p)-1/2),lo]
  have mass : 0≤∏ p∈P,(1+|w p|) := prod_nonneg fun _ _ => by positivity
  change (∏ p∈P,(1+|w p|))≤4*∏ p∈P,(1+w p)
  linarith only [cmp,mul_le_mul_of_nonneg_left sq mass]

/-- Relative truncation error from the logarithmic first moment of the absolute weights. -/
theorem denominator_tail (H Q : ℕ) (hp : 0<H) (ev : Even H) (qq : 2≤Q) (D : ℝ)
    (score : (∑ p∈smallPrimes Q, |localCoefficient H p| *Real.log p/(1+|localCoefficient H p|))≤D) :
    |denominatorSum H Q-truncatedSeries H Q| *Real.log Q≤4*truncatedSeries H Q*D := by
  classical
  let P := smallPrimes Q
  let v := localCoefficient H
  let w := fun p => |v p|
  let d := fun T : Finset ℕ => ∏ p∈T,p
  let m := fun T : Finset ℕ => ∏ p∈T,v p
  have pr (p : ℕ) (mem : p∈P) : p.Prime := (mem_filter.mp mem).2
  have lg (p : ℕ) (mem : p∈P) : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (pr p mem).pos)
  have logQ : 0≤Real.log (Q:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Q by omega))
  have dp : 0≤D := (sum_nonneg (fun p mem => div_nonneg (mul_nonneg (abs_nonneg _) (lg p mem)) (by positivity))).trans score
  have moment := subset_moment P w (fun p => Real.log p) fun p _ => abs_nonneg _
  have norm (T : Finset ℕ) : |m T|=∏ p∈T,w p := by simp [m,w,Finset.abs_prod]
  have loc (T : Finset ℕ) (h : T∈P.powerset) :
      |(if d T≤Q then m T else 0)-m T| *Real.log Q≤(∏ p∈T,w p)*(∑ p∈T,Real.log p) := by
    have sub := mem_powerset.mp h
    by_cases sm : d T≤Q
    · simp only [ite_eq_left sm,sub_self,abs_zero,zero_mul]
      exact mul_nonneg (prod_nonneg fun _ _ => abs_nonneg _) (sum_nonneg fun p mem => lg p (sub mem))
    · simp only [ite_eq_right sm,zero_sub,abs_neg,norm]
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun _ _ => abs_nonneg _)
      have l := Real.log_le_log (show 0<(Q:ℝ) by exact_mod_cast (show 0<Q by omega))
        (Nat.cast_le.mpr (le_of_lt (lt_of_not_ge sm)))
      change Real.log (Q:ℝ)≤Real.log ((∏ p∈T,p : ℕ):ℝ) at l
      rwa [Nat.cast_prod,Real.log_prod (fun p (mem : p∈T) => (Nat.cast_pos.mpr (pr p (sub mem)).pos : 0<(p:ℝ)).ne')] at l
  have small := (sum_le_sum loc).trans_eq moment
  have total : ∑ T∈P.powerset,m T=truncatedSeries H Q := (prod_one_add P).symm.trans (signed_product H Q hp ev qq)
  rw [← total,denominatorSum]
  change |(∑ T∈P.powerset,if d T≤Q then m T else 0)-(∑ T∈P.powerset,m T)| *Real.log Q≤_
  rw [← sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs ..) logQ).trans
  rw [sum_mul]
  apply small.trans
  have cmp := absolute_product H ev P pr
  rw [signed_product H Q hp ev qq] at cmp
  rw [total]
  exact mul_le_mul cmp score (sum_nonneg fun p mem => div_nonneg (mul_nonneg (abs_nonneg _) (lg p mem)) (by positivity))
    ((prod_nonneg fun _ _ => by positivity).trans cmp)

#print axioms denominator_tail
end GoldbachSpectral435.GoldbachSieve
