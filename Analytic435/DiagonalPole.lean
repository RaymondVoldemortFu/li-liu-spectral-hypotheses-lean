module
public import ConditionalGoldbach.Proofs.PoleDiagonalComparison
public import ConditionalGoldbach.Proofs.PoleZeta
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! The arithmetic diagonal has no simple pole at the central boundary.
Only proper prime powers and the primes dividing the modulus contribute to
the difference from the derivative of the zeta logarithmic derivative. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Set Complex
open scoped Topology
namespace GoldbachSpectral435.DiagonalPole

private def index (z : Nat.Primes × ℕ) : ℕ := (z.1:ℕ)^(z.2+2)

private lemma injective_index : Function.Injective index := by
  intro x y e
  obtain ⟨p,k⟩ := x.1.prop.pow_inj' y.1.prop (by omega : x.2+2≠0) (by omega : y.2+2≠0) e
  exact Prod.ext (Subtype.ext p) (by omega)

private def proper (n : ℕ) : ℝ := by
  classical
  exact if n∈Set.range index then (n:ℝ)^(-(3/4:ℝ)) else 0

private lemma proper_nonneg (n : ℕ) : 0≤proper n := by unfold proper; split <;> positivity

private lemma proper_summable : Summable proper := by
  classical
  apply (injective_index.summable_iff (f:=proper) (fun n hn => by simp [proper,hn])).mp
  let r := (2:ℝ)^(-(3/4:ℝ))
  have r0 : 0≤r := by dsimp [r]; positivity
  have r1 : r<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsum : Summable (fun z : Nat.Primes×ℕ => ((z.1:ℕ):ℝ)^(-(3/2:ℝ))*r^z.2) :=
    ((Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)).subtype Nat.Prime).mul_of_nonneg
      (summable_geometric_of_lt_one r0 r1) (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun _ => by positivity)
  apply hsum.of_nonneg_of_le (fun z => proper_nonneg (index z))
  intro z
  rw [proper,ite_eq_left (Set.mem_range_self z)]
  simp only [index,Nat.cast_pow]
  have pp : 0<((z.1:ℕ):ℝ) := by exact_mod_cast z.1.prop.pos
  have e : (((z.1:ℕ):ℝ)^(z.2+2))^(-(3/4:ℝ)) =
      ((z.1:ℕ):ℝ)^(-(3/2:ℝ))*(((z.1:ℕ):ℝ)^(-(3/4:ℝ)))^z.2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul pp.le,← Real.rpow_natCast,← Real.rpow_mul pp.le,← Real.rpow_add pp]
    push_cast; ring_nf
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<2)
    (by exact_mod_cast z.1.prop.two_le) (by norm_num)) _

private lemma nonprime_mem {n : ℕ} (hp : IsPrimePow n) (comp : ¬n.Prime) : n∈Set.range index := by
  obtain ⟨p,k,h,hk,rfl⟩ := (isPrimePow_nat_iff _).mp hp
  have two : 2≤k := by
    by_contra! ne
    have k1 : k=1 := by omega
    simp [k1,h] at comp
  exact ⟨(⟨p,h⟩,k-2),by simp [index,Nat.sub_add_cancel two]⟩

private def excess (N n : ℕ) : ℝ := Real.log n*mangoldt n -
  if n.Coprime N then (mangoldt n)^2 else 0

private lemma excess_nonneg (N n : ℕ) : 0≤excess N n := by
  have m : 0≤mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have h : mangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  unfold excess
  split <;> nlinarith only [mul_nonneg (sub_nonneg.mpr h) m,sq_nonneg (mangoldt n)]

private lemma excess_summable (N : ℕ) (np : 0<N) : Summable (fun n : ℕ => excess N n/(n:ℝ)) := by
  classical
  let exceptional := fun n : ℕ => if n∈N.primeFactors then (Real.log n)^2/(n:ℝ) else 0
  have finite : Summable exceptional := by
    apply summable_of_ne_finset_zero (s:=N.primeFactors)
    intro n hn
    exact ite_eq_right hn
  have bd (n : ℕ) (pn : 0<n) : (Real.log n)^2/(n:ℝ) ≤ 64*(n:ℝ)^(-(3/4:ℝ)) := by
    have x : 0<(n:ℝ) := by exact_mod_cast pn
    have lo : 0≤Real.log n := Real.log_nonneg (by exact_mod_cast pn)
    have z := Real.log_le_rpow_div x.le (by norm_num : (0:ℝ)<1/8)
    have sq := pow_le_pow_left₀ lo z 2
    apply (div_le_div_of_nonneg_right sq x.le).trans_eq
    rw [div_pow,← Real.rpow_natCast,← Real.rpow_mul x.le]
    norm_num
    rw [div_eq_mul_inv,← Real.rpow_neg_one]
    rw [show (-(3/4:ℝ))=(1/4:ℝ)+(-1) by norm_num,Real.rpow_add x]
    ring
  apply (finite.add (proper_summable.mul_left 64)).of_nonneg_of_le
    (fun n => div_nonneg (excess_nonneg N n) (Nat.cast_nonneg n))
  intro n
  have m : 0≤mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have h : mangoldt n≤Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have cap : excess N n ≤ (Real.log n)^2 := by
    have key := mul_le_mul_of_nonneg_left h (m.trans h)
    unfold excess
    split <;> nlinarith only [key,sq_nonneg (mangoldt n)]
  change _ ≤ exceptional n + 64*proper n
  by_cases exc : n∈N.primeFactors
  · exact (div_le_div_of_nonneg_right cap (Nat.cast_nonneg _)).trans
      (by simp only [exceptional,exc,ite_true]; linarith only [proper_nonneg n])
  · simp only [exceptional,exc,ite_false,zero_add]
    by_cases pr : n.Prime
    · have cop := pr.coprime_iff_not_dvd.mpr (fun d => exc (Nat.mem_primeFactors.mpr ⟨pr,d,np.ne'⟩))
      have v : mangoldt n=Real.log n := ArithmeticFunction.vonMangoldt_apply_prime pr
      rw [excess,ite_eq_left cop,v,sq,sub_self,zero_div]
      exact mul_nonneg (by norm_num) (proper_nonneg n)
    · by_cases isp : IsPrimePow n
      · rw [proper,ite_eq_left (nonprime_mem isp pr)]
        exact (div_le_div_of_nonneg_right cap (Nat.cast_nonneg n)).trans (bd n isp.pos)
      · have v : mangoldt n=0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr isp
        simp only [excess,v,mul_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,
          ite_self,sub_self,zero_div]
        exact mul_nonneg (by norm_num) (proper_nonneg n)

private theorem zeta_diagonal_gap (N : ℕ) (np : 0<N) (w : ℝ) (wp : 0<w) :
    ‖deriv (logDeriv riemannZeta) (1+(w:ℂ))-diagonalSeries N w‖ ≤
      ∑' n : ℕ, excess N n/(n:ℝ) := by
  have hr : 1 < (1+(w:ℂ)).re := by simpa using wp
  have hab : LSeries.abscissaOfAbsConv (fun n : ℕ => (mangoldt n:ℂ)) < (1+(w:ℂ)).re :=
    mangoldt_abscissa_le_one.trans_lt (by exact_mod_cast hr)
  have hs := LSeriesSummable_logMul_of_lt_re hab
  have hd : Summable (fun n : ℕ => if 0<n ∧ n.Coprime N then
      (mangoldt n:ℂ)^2/(n:ℂ)^(1+(w:ℂ)) else 0) := by
    apply Summable.of_norm
    simpa only [apply_ite norm,norm_zero] using diagonalSeries_summable N (w:=(w:ℂ)) wp
  rw [deriv_logDeriv_zeta_eq_mangoldt_log hr,diagonalSeries,LSeries,← hs.tsum_sub hd]
  apply (norm_tsum_le_tsum_norm (hs.sub hd).norm).trans
  apply Summable.tsum_le_tsum _ (hs.sub hd).norm (excess_summable N np)
  intro n
  by_cases zero : n=0
  · subst n; simp [LSeries.term,excess]
  have pn := Nat.pos_of_ne_zero zero
  have nr : 0<(n:ℝ) := by exact_mod_cast pn
  have n1 : (1:ℝ)≤n := by exact_mod_cast pn
  have expo : 1+(w:ℂ)=((1+w:ℝ):ℂ) := by push_cast; rfl
  have id : LSeries.term (LSeries.logMul (fun j : ℕ => (mangoldt j:ℂ))) (1+w) n -
      (if 0<n ∧ n.Coprime N then (mangoldt n:ℂ)^2/(n:ℂ)^(1+(w:ℂ)) else 0) =
      ((excess N n / ((n:ℝ)^(1+w)):ℝ):ℂ) := by
    rw [LSeries.term_of_ne_zero zero,expo,← Complex.ofReal_natCast,← Complex.ofReal_cpow nr.le]
    unfold excess LSeries.logMul
    by_cases cop : n.Coprime N
    · rw [ite_eq_left ⟨pn,cop⟩,ite_eq_left cop]
      push_cast; ring
    · rw [ite_eq_right (fun h => cop h.2),ite_eq_right cop]
      push_cast; ring
  rw [id,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (excess_nonneg ..) (by positivity))]
  exact div_le_div_of_nonneg_left (excess_nonneg ..) nr
    (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le n1 (show (1:ℝ)≤1+w by linarith))

private lemma zeta_regular :
    ∃ h : ℂ → ℂ, ContinuousAt h 1 ∧
      ∀ᶠ z : ℂ in 𝓝[≠] 1, deriv (logDeriv riemannZeta) z = ((z-1)^2)⁻¹+h z := by
  obtain ⟨f,hf,e⟩ := logDeriv_principal_part (riemannZeta_meromorphicAt_re_pos (by norm_num)) (-1) riemannZeta_order_one
  refine ⟨deriv f,hf.deriv.continuousAt,?_⟩
  filter_upwards [e.nhdsNE_deriv,hf.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with z hz ha ne
  have d := ((hasDerivAt_const z ((-1:ℤ):ℂ)).div ((hasDerivAt_id' z).sub_const 1) (sub_ne_zero.mpr ne)).add ha.differentiableAt.hasDerivAt
  change HasDerivAt (fun w : ℂ => ((-1:ℤ):ℂ)/(w-1)+f w) _ z at d
  rw [hz,d.deriv]
  push_cast; ring

/-- The full diagonal, with all imprimitive Euler factors removed according
to the actual modulus, differs from its double pole by a bounded quantity. -/
theorem diagonal_bounded_remainder (N : ℕ) (np : 0<N) :
    ∃ B : ℝ, 0<B ∧ ∀ᶠ w : ℝ in 𝓝[>] 0, ‖diagonalSeries N w-((w:ℂ)^2)⁻¹‖ ≤ B := by
  obtain ⟨h,hc,eq⟩ := zeta_regular
  let C := ∑' n : ℕ, excess N n/(n:ℝ)
  have c0 : 0≤C := tsum_nonneg (fun n => div_nonneg (excess_nonneg N n) (Nat.cast_nonneg _))
  refine ⟨C+‖h 1‖+1,by positivity,?_⟩
  have map : Tendsto (fun w : ℝ => 1+(w:ℂ)) (𝓝[>] 0) (𝓝[≠] (1:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have cont : Continuous (fun w : ℝ => 1+(w:ℂ)) := by fun_prop
      simpa using (cont.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w wp
      change 1+(w:ℂ)≠1
      simpa using Complex.ofReal_ne_zero.mpr (ne_of_gt (show 0<w from wp))
  have small := (hc.tendsto.comp (map.mono_right nhdsWithin_le_nhds)).norm.eventually_lt_const
    (show ‖h 1‖<‖h 1‖+1 by linarith)
  filter_upwards [map.eventually eq,small,self_mem_nhdsWithin] with w hw small wp
  have dist := zeta_diagonal_gap N np w wp
  rw [norm_sub_rev,hw,add_sub_cancel_left] at dist
  have same (u v z : ℂ) : u-z=(u-(z+v))+v := by ring
  rw [same _ (h (1+w))]
  exact (norm_add_le _ _).trans ((add_le_add dist small.le).trans_eq (by dsimp [C]; ring))

theorem diagonal_no_simple_pole (N : ℕ) (np : 0<N) :
    Tendsto (fun w : ℝ => (w:ℂ)*(diagonalSeries N w-((w:ℂ)^2)⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨B,_,bound⟩ := diagonal_bounded_remainder N np
  have lim : Tendsto (fun w : ℝ => w*B) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id (α:=ℝ) (x:=𝓝 0)).mul_const B).mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ lim
  filter_upwards [bound,self_mem_nhdsWithin] with w hb wp
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (le_of_lt (show 0<w from wp))]
  exact mul_le_mul_of_nonneg_left hb (le_of_lt (show 0<w from wp))

#print axioms diagonal_no_simple_pole
end GoldbachSpectral435.DiagonalPole
