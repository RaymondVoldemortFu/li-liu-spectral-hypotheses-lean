module
public import AtWindow
public import OriginalBounds
public import SpectralTests.Widths

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral GoldbachSpectral.BandSieve Filter
open scoped Topology
namespace GoldbachSpectral435

/-- Growth forced by the arithmetically selected pairs of opposite shifts. -/
theorem growth_from_shift_transfer (global : ∀ n, GRH n) {m : ℕ → ℝ}
    (transfer : ShiftTransfer m GRH) : LiuInput m GRH := by
  obtain ⟨C,cp,F,estimate⟩ := transfer
  intro d K
  let k := 2*(9*d+1)+1
  have od : Odd k := ⟨9*d+1,rfl⟩
  obtain ⟨L,lp,supply⟩ := large_shift global k od
  let A := amplification k
  have ap : 0<(A:ℝ) := by dsimp [A,amplification]; positivity
  let J : ℝ := L^2*C*(A:ℝ)^2
  have jp : 0<J := by dsimp [J]; positivity
  obtain ⟨t,hit,far,big⟩ := (supply.and ((eventually_ge_atTop (4*max K F+4)).and
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (J*64^d)))).exists
  obtain ⟨N,limit,ev,above,b,test,bias⟩ := hit
  have tM : t≤window t := (large_root t).trans (Nat.le_self_pow (by decide : 64≠0) _)
  have nk : max K F≤N := by omega
  have tn : 1≤t := by omega
  have tr : 1≤(t:ℝ) := by exact_mod_cast tn
  have tp : 0<(t:ℝ) := zero_lt_one.trans_le tr
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have logn := Real.log_nonneg (show 1≤(N:ℝ) by exact_mod_cast (show 1≤N by omega))
  let H := sieveHeight t k
  let B := oppositeSum N b
  have hR : (H:ℝ)=(t:ℝ)^(4*k) := by dsimp [H,sieveHeight]; push_cast; rfl
  have hp : 0<(H:ℝ) := hR ▸ pow_pos tp _
  have tc : ShiftTest N (3*(H:ℝ)) ((A:ℝ)*H) b := by simpa [H,A] using test
  have mn := estimate N (by omega) ev (global N) _ _ b tc
  change 3*(H:ℝ)*B^2 ≤ C*((A:ℝ)*H)^2*N*(m N)^2 at mn
  have sq := pow_le_pow_left₀ (pow_nonneg tp.le _) bias 2
  change ((t:ℝ)^(3*k))^2 ≤ (L*B)^2 at sq
  rw [← pow_mul,mul_pow,show 3*k*2=6*k by omega] at sq
  have prod := mul_le_mul_of_nonneg_right sq hp.le
  have trans := mul_le_mul_of_nonneg_left mn (sq_nonneg L)
  have base : (t:ℝ)^(2*k)*(H:ℝ)^2 ≤ J*((N:ℝ)*(m N)^2)*H^2 := by
    have id : (t:ℝ)^(2*k)*(H:ℝ)^2=(t:ℝ)^(6*k)*H := by
      rw [hR,← pow_mul,← pow_add,← pow_add]
      congr 1; omega
    rw [id]
    dsimp only [J]
    nlinarith only [prod,trans,mul_nonneg (mul_nonneg (sq_nonneg L) hp.le) (sq_nonneg B)]
  have lower := (mul_le_mul_iff_left₀ (sq_pos_of_pos hp)).mp base
  have lg := (Real.log_le_log np (by exact_mod_cast limit.le : (N:ℝ)≤window t)).trans (window_log t)
  have bound := pow_le_pow_left₀ logn lg d
  rw [mul_pow,← pow_mul] at bound
  have hi := mul_lt_mul_of_pos_right big (pow_pos tp (9*d))
  have monot := pow_le_pow_right₀ tr (by dsimp [k]; omega : 9*d+1≤2*k)
  rw [pow_succ'] at monot
  have up : J*(Real.log N)^d < J*((N:ℝ)*(m N)^2) := by
    apply ((mul_le_mul_of_nonneg_left bound jp.le).trans_lt _).trans_le (monot.trans lower)
    simpa only [mul_assoc] using hi
  exact ⟨N,by omega,ev,fun _ => (mul_lt_mul_iff_right₀ jp).mp up⟩

/-- Applied to the exact residual operator at the paper's normalization. -/
theorem cofinal_growth (global : ∀ n, GRH n) : LiuInput eligibleNorm GRH :=
  growth_from_shift_transfer global shiftTransfer_original

theorem refute_R (global : ∀ N, GRH N) : ¬ HypothesisR :=
  actual_R_failure_of_growth global (cofinal_growth global)

theorem refute_S (global : ∀ N, GRH N) (h : ℕ → ℝ) (j : ℕ)
    (width : EvenEventually (fun N => logWidth j N≤zeroFreeWidth N h)) : ¬ HypothesisS h :=
  actual_S_failure_of_growth global (cofinal_growth global) h j width

theorem prescribed_failure (global : ∀ N, GRH N) (j : ℕ) :
    IsAdmissible (prescribedH j) ∧ ¬HypothesisS (prescribedH j) := by
  obtain ⟨positive,diverges,cap⟩ := prescribed_admissible j
  have same (N : ℕ) : zeroFreeWidth N (prescribedH j) = GoldbachSpectral.width N (singular N) (prescribedH j N) := by
    unfold zeroFreeWidth GoldbachSpectral.width
    rw [original_series]
  have admiss : IsAdmissible (prescribedH j) := by
    refine ⟨fun N _ _ => positive N,fun B => ?_,?_⟩
    · obtain ⟨K,hK⟩ := eventually_atTop.mp (diverges.eventually_ge_atTop B)
      exact ⟨K,fun N hn _ => hK N hn⟩
    · obtain ⟨K,hK⟩ := eventually_atTop.mp cap
      exact ⟨K,fun N hn _ => (same N).le.trans (hK N hn)⟩
  refine ⟨admiss,refute_S global _ j ⟨2,?_⟩⟩
  intro N hn _
  rw [same,prescribed_width j N (by omega)]

#print axioms prescribed_failure
#print axioms refute_R
#print axioms refute_S
end GoldbachSpectral435

