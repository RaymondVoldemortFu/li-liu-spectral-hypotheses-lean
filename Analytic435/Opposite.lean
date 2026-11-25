module
public import Energy
public import SpectralTests.TestEnergy
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral MeasureTheory Set
open scoped ContDiff
namespace GoldbachSpectral435

def broad : ContDiffBump (1/2:ℝ) := ⟨1/16,1/8,by norm_num,by norm_num⟩

theorem broad_support : Function.support (broad:ℝ → ℝ) ⊆ Ioo (3/8:ℝ) (5/8) := by
  rw [broad.support_eq]
  intro u hu
  have d : |u-1/2|<1/8 := (Metric.mem_ball.mp hu : dist u (1/2:ℝ)<broad.rOut)
  obtain ⟨l,r⟩ := abs_lt.mp d
  exact ⟨by linarith,by linarith⟩

def broadWeight : FiniteModelWeight (broad : ℝ → ℝ) :=
  ⟨broad.contDiff,3/8,5/8,by norm_num,by norm_num,by norm_num,
    broad_support.trans Ioo_subset_Icc_self⟩

private def plusWeight {f g : ℝ → ℝ} (s : FiniteModelWeight f) (t : FiniteModelWeight g) :
    FiniteModelWeight (f+g) where
  smooth := s.smooth.add t.smooth
  lower := min s.lower t.lower
  upper := max s.upper t.upper
  lower_pos := lt_min s.lower_pos t.lower_pos
  upper_lt_one := max_lt s.upper_lt_one t.upper_lt_one
  lower_le_upper := (min_le_left _ _).trans (s.lower_le_upper.trans (le_max_left _ _))
  support_subset := by
    intro u nu
    by_cases p : f u=0
    · have h := t.mem_support_interval (u := u) (by intro z; apply nu; simp [p,z])
      exact ⟨(min_le_right _ _).trans h.1,h.2.trans (le_max_right _ _)⟩
    · have h := s.mem_support_interval p
      exact ⟨(min_le_left _ _).trans h.1,h.2.trans (le_max_left _ _)⟩

private theorem physical_samples {N : ℕ} {P : ℝ} (np : 0<N) (small : P<(N:ℝ)/20) (b : ℝ → ℝ)
    (sf : Function.support b ⊆ Icc P (2*P)) :
    let M := 2*N
    let f := fun u : ℝ => b ((M:ℝ)*u)
    (∑ m ∈ Finset.range M, weights M f m*
      (if m.Coprime N then weights M broad (N+m)-weights M broad (N-m) else 0)) =
      -((oppositeSum N b:ℝ):ℂ)/(M:ℂ) := by
  intro M f
  have mp : 0<(M:ℝ) := by dsimp [M]; positivity
  have nz : (M:ℂ)≠0 := by exact_mod_cast mp.ne'
  have sn : (Real.sqrt (M:ℝ):ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr mp).ne'
  have sq : (Real.sqrt (M:ℝ):ℂ)^2=(M:ℂ) := by exact_mod_cast Real.sq_sqrt mp.le
  have samp (m : ℕ) : weights M f m = ((mangoldt m*b m / Real.sqrt M:ℝ):ℂ) := by
    simp [weights,sampleValue,f,mul_div_cancel₀ _ mp.ne',mul_div_assoc]
  let W := fun m : ℕ => if m.Coprime N then mangoldt m*b m*(mangoldt (N-m)-mangoldt (N+m)) else 0
  have point (m : ℕ) : weights M f m*(if m.Coprime N then weights M broad (N+m)-weights M broad (N-m) else 0) =
      -(W m:ℂ)/(M:ℂ) := by
    rw [samp]
    by_cases z : b m=0
    · simp [z,W]
    · obtain ⟨_,h₂⟩ := sf z
      have ml : m < N := by exact_mod_cast (by linarith : (m:ℝ)<N)
      have flat (u : ℝ) (near : |u-1/2|≤1/16) : broad u=1 :=
        broad.one_of_mem_closedBall (by exact near : u ∈ Metric.closedBall (1/2:ℝ) broad.rIn)
      have plus : broad ((N+m:ℕ)/(M:ℝ))=1 := by
        apply flat
        apply abs_le.mpr
        constructor
        · have h : 1/2-1/16 ≤ ((N+m:ℕ):ℝ)/(M:ℝ) := (le_div_iff₀ mp).mpr (by dsimp [M]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m])
          linarith
        · have h : ((N+m:ℕ):ℝ)/(M:ℝ) ≤ 1/2+1/16 := (div_le_iff₀ mp).mpr (by dsimp [M]; push_cast; linarith)
          linarith
      have minus : broad ((N-m:ℕ)/(M:ℝ))=1 := by
        apply flat
        have lo : 1/2-1/16 ≤ ((N-m:ℕ):ℝ)/(M:ℝ) := (le_div_iff₀ mp).mpr (by dsimp [M]; push_cast [ml.le]; linarith)
        have hi : ((N-m:ℕ):ℝ)/(M:ℝ) ≤ 1/2+1/16 := (div_le_iff₀ mp).mpr (by dsimp [M]; push_cast [ml.le]; linarith [Nat.cast_nonneg (α := ℝ) m])
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      by_cases hc : m.Coprime N
      · simp only [W,ite_eq_left hc,weights,sampleValue,plus,minus,mul_one,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_sub]
        field_simp
        rw [← sq]
        ring
      · simp [W,hc]
  simp_rw [point]
  rw [← Finset.sum_div,Finset.sum_neg_distrib,← Complex.ofReal_sum]
  have truncate : ∑ m ∈ Finset.range M,W m = ∑ m ∈ Finset.range N,W m := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.range_mono (by dsimp [M]; omega))
    intro m _ outside
    have le : N ≤ m := by simpa using outside
    have z : b m=0 := by by_contra h; have rb := (sf h).2; linarith [show (N:ℝ)≤m by exact_mod_cast le]
    simp [W,z]
  rw [truncate]
  rfl

/-- Uniform transfer from the actual signed von Mangoldt sum to the norm
of the original Hardy operator. Only the paper's local GRH is assumed. -/
theorem actual_transfer :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ [NeZero N], Even N → Real.exp 10<(N:ℝ) → GRH N →
      ∀ ha : alpha N<beta, ∀ H P : ℝ, ∀ b : ℝ → ℝ, ShiftTest N H P b →
      H*(oppositeSum N b)^2 ≤ C*P^2*N*‖residualOperator ha N‖^2 := by
  let A := (2*Real.pi)⁻¹*Real.exp 4
  have ap : 0<A := by dsimp [A]; positivity
  let J := A*physicalEnergy broad+1
  have epos : 0≤physicalEnergy broad := integral_nonneg (fun _ => sq_nonneg _)
  have jp : 0<J := by dsimp [J]; positivity
  refine ⟨18*A*J,by positivity,?_⟩
  intro N inst he lar grh ha H P b test
  let M := 2*N
  let f := fun u : ℝ => b ((M:ℝ)*u)
  have np := NeZero.pos N
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have mp : 0<(M:ℝ) := by dsimp [M]; positivity
  have hp : 0<H := zero_lt_one.trans_le test.one_le
  have pp := hp.trans_le test.width_le
  have compactB := HasCompactSupport.of_support_subset_isCompact isCompact_Icc test.band
  have smooth := test.smooth
  have fsm : ContDiff ℝ 6 f := (smooth.comp (contDiff_const.mul contDiff_id)).of_le (by norm_num)
  have kb : Function.support f ⊆ Icc (P/M) (2*P/M) := by
    intro u hu
    obtain ⟨l,r⟩ := test.band hu
    exact ⟨(div_le_iff₀ mp).mpr (by linarith only [l,mul_comm (M:ℝ) u]),(le_div_iff₀ mp).mpr (by linarith only [r,mul_comm (M:ℝ) u])⟩
  have cap : 2*P/(M:ℝ)<1/8 := (div_lt_iff₀ mp).mpr (by dsimp [M]; push_cast; linarith [test.small])
  let F : FiniteModelWeight f := ⟨fsm,_,_,div_pos pp mp,by linarith,div_le_div_of_nonneg_right (by linarith) mp.le,kb⟩
  have inF : Function.support f ⊆ Ioo (0:ℝ) (1/8) :=
    fun _ h => ⟨(div_pos pp mp).trans_le (kb h).1,(kb h).2.trans_lt cap⟩
  have refl (u : ℝ) : broad (1-u)=broad u := by
    have eqn := broad.sub (u-1/2)
    simpa only [show 1/2-(u-1/2)=1-u by ring,show 1/2+(u-1/2)=u by ring] using eqn
  have log10 : 10<Real.log (N:ℝ) := by simpa using Real.log_lt_log (Real.exp_pos _) lar
  have linein : sigmaStar ∈ Ioo (alpha N) beta := by
    unfold sigmaStar alpha beta
    constructor
    · exact (one_div_lt_one_div_of_lt (by norm_num) (by linarith))
    · norm_num
  have h := opposite_entry_bound N he lar grh ha f broad F broadWeight (plusWeight F broadWeight)
    inF broad_support refl sigmaStar (by norm_num [sigmaStar]) linein (by norm_num [sigmaStar])
  let sum := ∑ m ∈ Finset.range M, weights M f m*(if m.Coprime N then weights M broad (N+m)-weights M broad (N-m) else 0)
  have phys : sum = -((oppositeSum N b:ℝ):ℂ)/(M:ℂ) := physical_samples np test.small b test.band
  change ‖sum‖ ≤ ‖residualOperator ha N‖*Real.sqrt (normFunctional M f (alpha N))*Real.sqrt (normFunctional M broad (alpha N)) at h
  rw [phys,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast] at h
  have xnorm := norm_at_double_le N lar f F
  have ynorm := norm_at_double_le N lar broad broadWeight
  have bd := smooth.differentiable (by simp)
  have scaled := physical_rescale b bd (M:ℝ) mp
  change normFunctional M f (alpha N) ≤ A*physicalEnergy f at xnorm
  rw [scaled] at xnorm
  have c : Continuous (physicalDensity b) := (smooth.continuous.div_const _).sub
    (continuous_id.mul (smooth.continuous_deriv (by simp)))
  have c₁ : HasCompactSupport (fun u => b u/2) := by simp only [div_eq_mul_inv]; exact compactB.mul_right
  have c₂ : HasCompactSupport (physicalDensity b) := c₁.sub compactB.deriv.mul_left
  have ib : Integrable (fun u => (physicalDensity b u)^2) := (c.pow 2).integrable_of_hasCompactSupport
    (by simp only [pow_two]; exact c₂.mul_right)
  have eb : physicalEnergy b ≤ energy b := setIntegral_le_integral ib
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have ene := (mul_le_mul_of_nonneg_right eb hp.le).trans (shift_energy test ib)
  have xp : 0≤normFunctional M f (alpha N) := by
    rw [← (doubled_quadratic N he lar grh ha f F sigmaStar (by norm_num [sigmaStar]) linein (by norm_num [sigmaStar])).1]
    positivity
  have yp : 0≤normFunctional M broad (alpha N) := by
    rw [← (doubled_quadratic N he lar grh ha broad broadWeight sigmaStar (by norm_num [sigmaStar]) linein (by norm_num [sigmaStar])).1]
    positivity
  have X : normFunctional M f (alpha N)*M*H ≤ A*(9*P^2) := by
    have val := (le_div_iff₀ mp).mp (xnorm.trans_eq (mul_div_assoc ..).symm)
    exact (mul_le_mul_of_nonneg_right val hp.le).trans ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left ene ap.le))
  have Y : normFunctional M broad (alpha N)≤J := by dsimp [J]; linarith only [ynorm,show (0:ℝ)≤1 by norm_num]
  have mag := (div_le_iff₀ mp).mp h
  have sq := pow_le_pow_left₀ (abs_nonneg _) mag 2
  rw [sq_abs] at sq
  simp only [mul_pow,Real.sq_sqrt xp,Real.sq_sqrt yp] at sq
  have stat := mul_le_mul X Y yp (mul_nonneg ap.le (by positivity))
  have final := mul_le_mul_of_nonneg_right stat (sq_nonneg ‖residualOperator ha N‖)
  have hsq := mul_le_mul_of_nonneg_left sq hp.le
  have result : H*(oppositeSum N b)^2 ≤ A*(9*P^2)*J*‖residualOperator ha N‖^2*M := by
    apply hsq.trans
    calc
      _ = (normFunctional M f (alpha N)*M*H * normFunctional M broad (alpha N)*‖residualOperator ha N‖^2)*M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right final mp.le
  dsimp [M] at result
  push_cast at result
  exact result.trans_eq (by ring)

#print axioms actual_transfer
end GoldbachSpectral435

