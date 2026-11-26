module
public import WindowTightness

/-! Removing the logarithmic von Mangoldt weights on genuine prime pairs.
A finite Abel summation uses the translated sieve and keeps both endpoints. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset
namespace GoldbachSpectral435.GoldbachSieve

def pairIndicator (N n : ℕ) : ℝ := if n.Prime ∧ (N-n).Prime then 1 else 0

lemma pairIndicator_nonneg (N n : ℕ) : 0≤pairIndicator N n := by unfold pairIndicator; split <;> norm_num

private def increment (v : ℕ) := Real.log (v+1:ℕ)-Real.log v

private lemma increment_sum (N : ℕ) : ∑ v∈range N, increment v=Real.log N := by
  simpa only [increment, Nat.cast_zero,Real.log_zero,sub_zero] using sum_range_sub (fun v : ℕ => Real.log v) N

private lemma increment_bounds (v : ℕ) : 0 ≤ increment v ∧ ((v:ℝ)+1)*increment v≤2 := by
  rcases Nat.eq_zero_or_pos v with rfl|pos
  · norm_num [increment]
  have vp : 0<(v:ℝ) := by exact_mod_cast pos
  have one : 1≤(v:ℝ) := by exact_mod_cast pos
  have logpos := Real.log_le_log vp (show (v:ℝ)≤v+1 by linarith)
  have b := Real.log_le_sub_one_of_pos (div_pos (show 0<(v:ℝ)+1 by positivity) vp)
  rw [Real.log_div (by positivity) vp.ne'] at b
  simp only [increment,Nat.cast_add,Nat.cast_one]
  refine ⟨by linarith,?_⟩
  have a : (v:ℝ)+1≤2*v := by linarith
  have c := mul_le_mul_of_nonneg_left b (by positivity : 0≤(v:ℝ)+1)
  apply c.trans
  rw [show ((v:ℝ)+1)/v-1=1/v by field_simp; ring,mul_one_div]
  exact (div_le_iff₀ vp).mpr (by linarith)

private lemma prefix_count (N v : ℕ) (lt : v<N) :
    ∑ n∈range N, (if n≤v then pairIndicator N n else 0)=primePairs N 0 (v+1) := by
  have inds : (range N).filter (fun n => n≤v)=range (v+1) := by ext n; simp; omega
  rw [← sum_filter,inds]
  simp [primePairs,pairIndicator,Nat.Ico_zero_eq_range]

private lemma abel (N : ℕ) :
    ∑ n∈range N, pairIndicator N n*(Real.log N-Real.log n)=
      ∑ v∈range N, increment v*primePairs N 0 (v+1) := by
  have each (n : ℕ) (hn : n∈range N) :
      Real.log N-Real.log n=∑ v∈range N, if n≤v then increment v else 0 := by
    have inds : (range N).filter (fun v => n≤v)=Ico n N := by ext v; simp; tauto
    rw [← sum_filter,inds,sum_Ico_eq_sub _ (mem_range.mp hn).le,increment_sum,increment_sum]
  rw [sum_congr rfl (fun n hn => congrArg (pairIndicator N n * ·) (each n hn))]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  rw [← prefix_count N v (mem_range.mp hv),mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> ring

/-- The log loss at one endpoint, summed over all actual prime pairs, is
small enough to remove both prime weights in the normalized first block. -/
theorem pair_log_loss :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 2^64≤N → Even N →
      (Real.log N)^2*(∑ n∈range N, pairIndicator N n*(Real.log N-Real.log n))≤
        C*N*singularSeries N+6*Real.sqrt N*(Real.log N)^3 := by
  obtain ⟨C,cp,cap⟩ := prime_window
  refine ⟨2*C,by positivity,?_⟩
  intro N big ev
  let L := Real.log (N:ℝ)
  have ss := singularSeries_pos N
  have point (v : ℕ) (hv : v∈range N) :
      L^2*(increment v*primePairs N 0 (v+1))≤2*C*singularSeries N+(6*Real.sqrt N*L^2)*increment v := by
    have inc : 0+(v+1)≤N+1 := by have := mem_range.mp hv; omega
    have b := mul_le_mul_of_nonneg_right (cap N 0 (v+1) big ev inc) (increment_bounds v).1
    push_cast at b
    have a := mul_le_mul_of_nonneg_left (increment_bounds v).2 (mul_nonneg cp.le ss.le)
    change L^2*_≤_
    dsimp only [L] at *
    nlinarith only [a,b]
  rw [abel,mul_sum]
  apply (sum_le_sum point).trans_eq
  rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,← mul_sum,increment_sum]
  dsimp [L]
  ring

#print axioms pair_log_loss
end GoldbachSpectral435.GoldbachSieve
