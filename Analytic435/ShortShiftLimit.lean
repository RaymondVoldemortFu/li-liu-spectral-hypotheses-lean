module
public import PaperPremise

@[expose] public section
set_option autoImplicit false
noncomputable section
open GoldbachSpectral ArithmeticFunction Finset Filter
open scoped Topology
namespace GoldbachSpectral435

/-- A size bound uniform over all normalized tests in the opposite-shift identity. -/
theorem opposite_size {N : ℕ} (hn : 2 ≤ N) {H P : ℝ} {b : ℝ → ℝ} (test : ShiftTest N H P b) :
    |oppositeSum N b| ≤ 28 * P * Real.log N := by
  classical
  have one := test.one_le.trans test.width_le
  have pos : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have lg : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  let L := 2 * Real.log N
  have lp : 0 ≤ L := by dsimp [L]; positivity
  have upper (u : ℕ) (hu : u ≤ 2*N) : vonMangoldt u ≤ L := by
    by_cases z : u=0
    · simpa [z] using lp
    · have cap : Real.log (2*(N:ℝ)) ≤ L := by
        rw [Real.log_mul (by norm_num) pos.ne']
        dsimp [L]
        linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) (show 2≤(N:ℝ) by exact_mod_cast hn)]
      exact vonMangoldt_le_log.trans ((Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero z)
        (by exact_mod_cast hu)).trans cap)
  let term := fun m : ℕ => if m.Coprime N then vonMangoldt m * b m *
    (vonMangoldt (N-m) - vonMangoldt (N+m)) else 0
  let M := min N (⌊2*P⌋₊+1)
  have sub : range M ⊆ range N := range_mono (min_le_left ..)
  have cut : oppositeSum N b = ∑ m ∈ range M, term m := by
    apply Eq.symm
    apply sum_subset sub
    intro m incl outside
    have hm := mem_range.mp incl
    have out := Nat.le_of_not_gt (fun h => outside (mem_range.mpr h))
    have beyond : ⌊2*P⌋₊ < m := by dsimp [M] at out; omega
    have bz : b m = 0 := by
      by_contra nz
      have bound := Nat.le_floor (test.band nz).2
      omega
    simp [term,bz]
  have each (m : ℕ) (hm : m ∈ range M) : |term m| ≤ vonMangoldt m * L := by
    have small := mem_range.mp (sub hm)
    dsimp only [term]
    split
    · rw [abs_mul,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
      have diff : |vonMangoldt (N-m) - vonMangoldt (N+m)| ≤ L :=
        abs_le.mpr ⟨by linarith [upper (N+m) (by omega),vonMangoldt_nonneg (n := N-m)],
          by linarith [upper (N-m) (by omega),vonMangoldt_nonneg (n := N+m)]⟩
      exact mul_le_mul (mul_le_of_le_one_right vonMangoldt_nonneg (test.normalized m).1)
        diff (abs_nonneg _) vonMangoldt_nonneg
    · simpa using mul_nonneg (vonMangoldt_nonneg (n := m)) lp
  have mass : ∑ m ∈ range M, vonMangoldt m ≤ Chebyshev.psi (2*P) := by
    calc
      _ ≤ ∑ m ∈ range (⌊2*P⌋₊+1), vonMangoldt m :=
        sum_le_sum_of_subset_of_nonneg (range_mono (min_le_right ..)) (fun _ _ _ => vonMangoldt_nonneg)
      _ = _ := by
        have ids : range (⌊2*P⌋₊+1) = insert 0 (Ioc 0 ⌊2*P⌋₊) := by ext m; simp
        rw [ids,sum_insert (by simp)]
        simp [Chebyshev.psi]
  have crude := Chebyshev.psi_le_const_mul_self (show 0 ≤ 2*P by linarith)
  have coeff := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  have total : ∑ m ∈ range M, vonMangoldt m ≤ 14*P := mass.trans (crude.trans (by
    nlinarith only [mul_le_mul_of_nonneg_right coeff (by linarith : 0 ≤ P)]))
  rw [cut]
  calc
    _ ≤ ∑ m ∈ range M, |term m| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ m ∈ range M, vonMangoldt m * L := sum_le_sum each
    _ = (∑ m ∈ range M, vonMangoldt m)*L := (sum_mul ..).symm
    _ ≤ (14*P)*L := mul_le_mul_of_nonneg_right total lp
    _ = _ := by dsimp [L]; ring

/-- Explicit upper bound for the squared test certificate at the logarithmic scale. -/
theorem shift_log_scale_cap {N : ℕ} (hn : 2 ≤ N) {H P : ℝ} {b : ℝ → ℝ} (test : ShiftTest N H P b) :
    H * (oppositeSum N b)^2 * (Real.log N)^2 ≤ 784 * P^3 * (Real.log N)^4 := by
  have pp : 0 ≤ P := zero_le_one.trans (test.one_le.trans test.width_le)
  have bs := pow_le_pow_left₀ (abs_nonneg _) (opposite_size hn test) 2
  rw [sq_abs] at bs
  exact (mul_le_mul_of_nonneg_right (mul_le_mul test.width_le bs (sq_nonneg _) pp)
    (sq_nonneg (Real.log N))).trans_eq (by ring)

/-- At the logarithmic S scale every test with P² ≤ N has a vanishing
normalized lower-bound certificate, uniformly in H, P and b. -/
theorem short_shifts_below_log_scale (ε : ℝ) (ep : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ H P b, ShiftTest N H P b → P^2 ≤ N →
      H * (oppositeSum N b)^2 * (Real.log N)^2 ≤ ε * P^2 * N := by
  have decay := (Real.isLittleO_pow_log_id_atTop (n := 8)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),decay.eventually_lt_const (show 0 < (ε/784)^2 by positivity)] with N hn small
  intro H P b test window
  have pos : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have pp : 0 < P := zero_lt_one.trans_le (test.one_le.trans test.width_le)
  let l := Real.log N
  change l^8 / (N:ℝ) < (ε/784)^2 at small
  have small' := (div_lt_iff₀ pos).mp small
  have sq : (784*P*l^4)^2 ≤ (ε*N)^2 := calc
    _ = (784^2*l^8)*P^2 := by ring
    _ ≤ (784^2*l^8)*N := mul_le_mul_of_nonneg_left window (by positivity)
    _ ≤ (ε*N)^2 := by nlinarith only [mul_le_mul_of_nonneg_right small'.le pos.le]
  have threshold : 784*P*l^4 ≤ ε*N := by nlinarith only [sq,mul_pos ep pos,sq_nonneg (784*P*l^4-ε*N)]
  calc
    _ ≤ 784*P^3*l^4 := shift_log_scale_cap hn test
    _ = (784*P*l^4)*P^2 := by ring
    _ ≤ (ε*N)*P^2 := mul_le_mul_of_nonneg_right threshold (sq_nonneg _)
    _ = _ := by ring

#print axioms opposite_size
#print axioms short_shifts_below_log_scale
end GoldbachSpectral435
