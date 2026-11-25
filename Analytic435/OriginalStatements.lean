module
public import SpectralRefutation

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral Filter
namespace GoldbachSpectral435

theorem norm_lower_on_original (grh : ∀ N, GRH N) (d K : ℕ) :
    ∃ N≥K, Even N ∧ ∃ inst : NeZero N, ∃ ha : alpha N<beta,
      Real.log N ^ d < (N:ℝ)*‖@residualOperator (alpha N) ha N inst‖^2 := by
  obtain ⟨F,large⟩ := evenEventually_large
  obtain ⟨N,hn,he,low⟩ := cofinal_growth grh d (max F K)
  obtain ⟨four,_,ha⟩ := large_parameters (large N (by omega) he)
  let inst : NeZero N := ⟨by omega⟩
  refine ⟨N,by omega,he,inst,ha,?_⟩
  rw [← eligibleNorm_spec N ha (grh N)]
  exact low (grh N)

/-- Actual real zeros, with explicit location and the original quaternionic
function. Both the modulus and its Hilbert-space instance are quantified. -/
theorem cofinal_original_zeros (grh : ∀ N, GRH N) (j K : ℕ) :
    ∃ N≥K, Even N ∧ ∃ inst : NeZero N, ∃ ha : alpha N<beta, ∃ x : ℝ,
      1-logWidth j N<x ∧ x<1 ∧
        spectralQuaternion N (@residualOperator (alpha N) ha N inst) (x:Quaternion ℝ)=0 := by
  classical
  obtain ⟨ok,fails⟩ := prescribed_failure grh j
  by_contra no
  apply fails
  refine ⟨ok,?_⟩
  obtain ⟨F,large⟩ := evenEventually_large
  obtain ⟨L,cap⟩ := ok.2.2
  refine ⟨max (max K F) L,?_⟩
  intro N hn ev g inst ha q qr zero
  have big := large N (by omega) ev
  obtain ⟨four,logp,_⟩ := large_parameters big
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have width : zeroFreeWidth N (prescribedH j)=logWidth j N := by
    unfold zeroFreeWidth
    rw [original_series]
    exact prescribed_width j N (by omega)
  have small := cap N (by omega) ev
  change zeroFreeWidth N (prescribedH j)≤1/4 at small
  rw [width] at small qr
  let T := residualOperator ha N
  have hT := residualOperator_has_spectral_data N ev big g ha
  have δ := spectralScale_pos N np (singularSeries_pos N) logp
  obtain ⟨i,nonzero,quad⟩ := (spectralQuaternion_eq_zero_iff N T hT δ.ne' q).mp zero
  have real := quaternion_quadratic_real_of_off_critical q _ quad (by linarith)
  apply no
  refine ⟨N,by omega,ev,inst,ha,q.re,qr,?_,?_⟩
  · rw [real] at quad
    have val := congrArg (fun q : Quaternion ℝ => q.re) quad
    simp only [Quaternion.re_mul,Quaternion.re_coe,Quaternion.imI_coe,Quaternion.imJ_coe,
      Quaternion.imK_coe,Quaternion.re_sub,Quaternion.re_one,Quaternion.imI_sub,
      Quaternion.imI_one,Quaternion.imJ_sub,Quaternion.imJ_one,Quaternion.imK_sub,
      Quaternion.imK_one,zero_mul,sub_zero] at val
    have pos : 0<spectralScale N^2/(4*eigenvalues T i^2) := by positivity
    by_contra! ge
    nlinarith only [val,pos,mul_nonneg (zero_le_one.trans ge) (sub_nonneg.mpr ge)]
  · rw [← real]
    exact zero

/-- The external interface uses only the standard Mathlib character and
L-function, through exactly the primitive GRH statement verified separately. -/
theorem primitive_GRH_spectral_consequences
    (input : ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive →
      ∀ z : ℂ, 0<z.re → z.re<1 → χ.LFunction z=0 → z.re=1/2) :
    ¬HypothesisR ∧ ∀ j, IsAdmissible (prescribedH j) ∧ ¬HypothesisS (prescribedH j) :=
  ⟨refute_R (all_local_of_primitive input),prescribed_failure (all_local_of_primitive input)⟩

/-- One sequence detects every fixed inverse power of the logarithm. Its
selection is independent of any function used to prescribe a zero-free region. -/
theorem common_zero_sequence (grh : ∀ N, GRH N) :
    ∃ (N : ℕ → ℕ) (x : ℕ → ℝ), StrictMono N ∧
      (∀ i, Even (N i) ∧ x i<1 ∧ ∃ inst : NeZero (N i), ∃ ha : alpha (N i)<beta,
        spectralQuaternion (N i) (@residualOperator (alpha (N i)) ha (N i) inst)
          (x i:Quaternion ℝ)=0) ∧
      (∀ j : ℕ, Filter.Tendsto (fun i => Real.log (N i)^j*(1-x i)) Filter.atTop
        (nhds 0)) ∧
      ∀ h, HypothesisS h → ∀ᶠ i in Filter.atTop, zeroFreeWidth (N i) h≤1-x i := by
  classical
  let hit (j n : ℕ) := Even n ∧ ∃ x : ℝ, 1-logWidth j n<x ∧ x<1 ∧
    ∃ inst : NeZero n, ∃ ha : alpha n<beta,
      spectralQuaternion n (@residualOperator (alpha n) ha n inst) (x:Quaternion ℝ)=0
  have supply (j K : ℕ) : ∃ n≥K, hit j n := by
    obtain ⟨n,high,even,inst,ha,x,lo,hi,z⟩ := cofinal_original_zeros grh j K
    exact ⟨n,high,even,x,lo,hi,inst,ha,z⟩
  choose pick high good using supply
  let N : ℕ → ℕ := Nat.rec (pick 0 1) (fun i prev => pick (i+1) (prev+1))
  have inc : StrictMono N := strictMono_nat_of_lt_succ fun i => high (i+1) (N i+1)
  have hits (i : ℕ) : hit i (N i) := by
    cases i with
    | zero => exact good 0 1
    | succ i => exact good (i+1) (N i+1)
  choose x lower upper inst strip zero using fun i => (hits i).2
  refine ⟨N,x,inc,fun i => ⟨(hits i).1,upper i,inst i,strip i,zero i⟩,?_,?_⟩
  · intro j
    have logs : Filter.Tendsto (fun i : ℕ => Real.log (@Nat.cast ℝ Real.instNatCast (N i))) Filter.atTop Filter.atTop :=
      by simpa only [Function.comp_def] using
          (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).comp inc.tendsto_atTop
    have decay : Filter.Tendsto (fun i : ℕ => (Real.log (@Nat.cast ℝ Real.instNatCast (N i)))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp logs
    apply squeeze_zero' _ _ decay
    · filter_upwards [logs.eventually_ge_atTop 1] with i pos
      exact mul_nonneg (pow_nonneg (by linarith) _) (sub_nonneg.mpr (upper i).le)
    · filter_upwards [logs.eventually_ge_atTop 1,Filter.eventually_ge_atTop (j+1)] with i pos big
      let l : ℝ := Real.log (@Nat.cast ℝ Real.instNatCast (N i))
      change 1≤l at pos
      have lp : 0<l := by linarith
      have b := lower i
      change 1-1/(4*l^i)<x i at b
      have u : (1-x i)*(4*l^i)<1 := (lt_div_iff₀ (by positivity)).mp (by linarith only [b])
      have p := pow_le_pow_right₀ pos big
      have m := mul_le_mul_of_nonneg_left p (sub_nonneg.mpr (upper i).le)
      change l^j*(1-x i)≤l⁻¹
      rw [← one_div,le_div_iff₀ lp]
      rw [pow_succ] at m
      nlinarith only [u,m,mul_nonneg (sub_nonneg.mpr (upper i).le) (pow_nonneg lp.le i)]
  · intro h S
    obtain ⟨K,hK⟩ := S.2
    filter_upwards [inc.tendsto_atTop.eventually_ge_atTop K] with i hi
    have exclusion := hK (N i) hi (hits i).1 (grh _) (inst i) (strip i)
    by_contra! wide
    exact exclusion (x i:Quaternion ℝ) (by change 1-zeroFreeWidth (N i) h<x i; linarith) (zero i)

#print axioms common_zero_sequence
#print axioms norm_lower_on_original
#print axioms cofinal_original_zeros
#print axioms primitive_GRH_spectral_consequences
end GoldbachSpectral435

