module
public import PerronHardy
public import ConditionalGoldbach.Proofs.SpectralDiagonalBound

/-! The same prime cutoff removes the diagonal to smaller order than the
operator-norm approximation of the odd-character contribution. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex MeasureTheory Filter Set InnerProductSpace
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PerronApproximation

def primeDiagonal (N m : ℕ) :
    HardySpace (alpha N) beta →L[ℂ] HardySpace (alpha N) beta :=
  ∑ j ∈ Finset.range ⌊cutoff N m⌋₊,
    ((smoothedPerronWeight (cutoff N m) (j+1):ℂ)^2) •
      rankOne ℂ (diagonalRankVector N j) (diagonalRankVector N j)

/-- A uniform bound on the discarded positive diagonal series. -/
theorem diagonal_error (N : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ))
    (ha : alpha N < beta) (m : ℕ) (hm : 1≤m) (hcut : 100*Real.log (Real.log N) ≤ m) :
    ‖diagonalOperator ha N - primeDiagonal N m‖ ≤
      (16*Real.pi*(Real.log 4+4))/(Real.log N)^18 := by
  classical
  let a := alpha N
  let L := Real.log N
  let X := cutoff N m
  let y := (N:ℝ)^m
  let w (j : ℕ) := smoothedPerronWeight X (j+1)
  let R (j : ℕ) := rankOne ℂ (diagonalRankVector (a:=a) N j) (diagonalRankVector (a:=a) N j)
  let P (j : ℕ) := ((w j:ℂ)^2) • R j
  let E (j : ℕ) := R j-P j
  have ap : 0<a := large_alpha_pos big
  have au : a≤1 := ha.le.trans (by norm_num [beta])
  have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have L1 : 1≤L := by dsimp [L]; linarith [(Real.lt_log_iff_exp_lt np).mpr big]
  have lp : 0<L := lt_of_lt_of_le zero_lt_one L1
  have np1 : 1<(N:ℝ) := (Real.log_pos_iff np.le).mp lp
  have y1 : 1<y := one_lt_pow₀ np1 (by omega)
  have X1 : 1<X := one_lt_pow₀ y1 (by decide)
  have sx : Real.sqrt X = y := Real.sqrt_sq (by positivity : 0≤y)
  have wp (j : ℕ) := smoothedPerronWeight_nonneg_le_one X1 (j+1)
  have vnorm (j : ℕ) : ‖R j‖=‖diagonalRankVector (a:=a) N j‖^2 := by simp only [R,norm_rankOne,pow_two]
  have rs : Summable (fun j => ‖R j‖) := by
    simpa only [vnorm] using diagonalRankVector_summable ha ap N
  have scal (j : ℕ) : 0≤1-(w j)^2 ∧ 1-(w j)^2≤1 := by
    have h : 0≤w j ∧ w j≤1 := wp j
    constructor <;> nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2),sq_nonneg (w j)]
  have enorm (j : ℕ) : ‖E j‖ = (1-(w j)^2)*‖R j‖ := by
    have id : E j = ((1-(w j)^2:ℝ):ℂ) • R j := by
      simp only [E,P,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow,sub_smul,one_smul]
    rw [id,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (scal j).1]
  have es : Summable (fun j => ‖E j‖) := rs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
    rw [enorm]; exact mul_le_of_le_one_left (norm_nonneg _) (scal j).2)
  have finite (j : ℕ) (hj : j ∉ Finset.range ⌊X⌋₊) : P j = 0 := by
    have nv : X < ((j+1:ℕ):ℝ) := (Nat.lt_floor_add_one X).trans_le (by exact_mod_cast
      (show ⌊X⌋₊+1≤j+1 by simpa using Nat.succ_le_succ (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h)))))
    have sy : Real.sqrt X ≤ X := Real.sqrt_le_self_iff.mpr (Or.inr X1.le)
    have ww : w j = 0 := by
      change (if ((j+1:ℕ):ℝ) ≤ Real.sqrt X then _ else if ((j+1:ℕ):ℝ) ≤ X then _ else _) = _
      rw [ite_eq_right (not_le.mpr (sy.trans_lt nv)),ite_eq_right (not_le.mpr nv)]
    simp [P,ww]
  have ps : Summable P := summable_of_ne_finset_zero finite
  have small (n : ℝ) (hn : y<n) : n^(-a) ≤ (L^20)⁻¹ := by
    have logy : Real.log y = (m:ℝ)*L := Real.log_pow _ _
    have logL := Real.log_nonneg L1
    have eqv : Real.log y*(-a) = -(m:ℝ) := by
      rw [logy]
      change (m:ℝ)*L * (-(1/L)) = _
      field_simp [lp.ne']
    calc
      _ ≤ y^(-a) := Real.rpow_le_rpow_of_nonpos (by linarith) hn.le (neg_nonpos.mpr ap.le)
      _ = Real.exp (-(m:ℝ)) := by rw [Real.rpow_def_of_pos (by linarith : 0<y),eqv]
      _ ≤ Real.exp (-(20*Real.log L)) := Real.exp_le_exp.mpr (by change 100*Real.log L ≤ _ at hcut; linarith)
      _ = _ := by rw [Real.exp_neg,show (20:ℝ)*Real.log L = Real.log (L^20) by rw [Real.log_pow]; norm_num,
                        Real.exp_log (by positivity)]
  have term (j : ℕ) : ‖E j‖ ≤ (2*Real.pi/(L^20))*
      (diagonalCoefficient N j * ((j+1:ℕ):ℝ)^(-2*(a/2))) := by
    let n := ((j+1:ℕ):ℝ)
    have hn : 1≤n := by dsimp [n]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hn0 : 0<n := zero_lt_one.trans_le hn
    have dc := diagonalCoefficient_nonneg N j
    have pospow : 0≤n^(-a) := Real.rpow_nonneg hn0.le _
    by_cases low : n≤y
    · have ww : w j = 1 := ite_eq_left (by simpa only [sx] using low : n≤Real.sqrt X)
      rw [enorm,ww]; simp only [one_pow,sub_self,zero_mul]
      positivity
    · have rate := small n (lt_of_not_ge low)
      have ab := Real.rpow_le_rpow_of_exponent_le hn (show -2*beta≤ -2*a by linarith)
      have h1 : n^(-2*a)/(1+a) ≤ n^(-2*a) := div_le_self (by positivity) (by linarith)
      have h2 : n^(-2*beta)/(1+beta) ≤ n^(-2*a) :=
        (div_le_self (by positivity) (by norm_num [beta])).trans ab
      have dec : n^(-2*a) ≤ (L^20)⁻¹*n^(-2*(a/2)) := by
        rw [show -2*a=(-a)+(-a) by ring,Real.rpow_add hn0,show -2*(a/2)=-a by ring]
        exact mul_le_mul_of_nonneg_right rate pospow
      apply (show ‖E j‖≤‖R j‖ by rw [enorm]; exact mul_le_of_le_one_left (norm_nonneg _) (scal j).2).trans
      rw [vnorm,diagonalRankVector_norm_sq,diagonalHardyVector_norm_sq ha ap.le _ (by omega)]
      change diagonalCoefficient N j * (Real.pi*(n^(-2*a)/(1+a)+n^(-2*beta)/(1+beta))) ≤ _
      have d := mul_le_mul_of_nonneg_left (add_le_add (h1.trans dec) (h2.trans dec)) (mul_nonneg dc Real.pi_pos.le)
      convert d using 1 <;> dsimp only [n] <;> ring
  have hsum := diagonalCoefficient_power_summable N (a/2) (by positivity)
  rw [diagonalOperator_eq_rankSeries ha ap N]
  change ‖(∑' j, R j) - ∑ j ∈ Finset.range ⌊X⌋₊, P j‖ ≤ _
  have sumP : (∑' j, P j) = ∑ j ∈ Finset.range ⌊X⌋₊, P j := tsum_eq_sum finite
  rw [← sumP,← rs.of_norm.tsum_sub ps]
  apply (norm_tsum_le_tsum_norm es).trans
  apply (es.tsum_le_tsum term (hsum.mul_left _)).trans
  rw [tsum_mul_left]
  apply (mul_le_mul_of_nonneg_left (diagonalCoefficient_series_bound N (a/2) (by positivity))
    (by positivity : 0≤2*Real.pi/L^20)).trans
  have hu : 1+a/2≤2 := by linarith
  have G : 0≤Real.log 4+4 := by positivity
  calc
    _ ≤ (2*Real.pi/L^20)*(2*(Real.log 4+4)/(a/2)^2) := by gcongr
    _ = _ := by dsimp [a,alpha,L]; field_simp; ring

#print axioms diagonal_error
end GoldbachSpectral435.PerronApproximation
