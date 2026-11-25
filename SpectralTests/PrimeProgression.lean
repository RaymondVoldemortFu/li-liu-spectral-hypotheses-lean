module
public import SpectralTests.ShiftDefinitions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section
namespace GoldbachSpectral
open Set ArithmeticFunction
open scoped ContDiff

private theorem fixed_weight :
    ∃ b : ℝ → ℝ, 0 < b 3 ∧ (∀ m : ℕ, m ≠ 3 → b m = 0) ∧
      ∀ N : ℕ, 40 < N → ShiftTest N 1 2 b := by
  let f : ContDiffBump (3:ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  have smooth : ContDiff ℝ ∞ (f : ℝ → ℝ) := f.contDiff
  obtain ⟨C,hC⟩ := (smooth.continuous_deriv (by simp)).bounded_above_of_compact_support
    f.hasCompactSupport.deriv
  let K := max C 1
  have hk : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have shape : ∀ u : ℝ, f u ≠ 0 → 5/2 < u ∧ u < 7/2 := by
    intro u hu
    have mem : u ∈ Function.support f := hu
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq] at mem
    change |u-3| < 1/2 at mem
    obtain ⟨hl,hr⟩ := abs_lt.mp mem
    exact ⟨by linarith,by linarith⟩
  refine ⟨fun u => f u/K, ?_, ?_, ?_⟩
  · change 0 < f 3/K
    rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)]
    positivity
  · intro m hm
    suffices hh : f (m:ℝ)=0 by simp [hh]
    by_contra hh
    obtain ⟨hl,hr⟩ := shape _ hh
    have h1 : 2 < m := by exact_mod_cast (show (2:ℝ) < m by linarith)
    have h2 : m < 4 := by exact_mod_cast (show (m:ℝ) < 4 by linarith)
    omega
  · intro N hn
    have hn' : (40:ℝ)<N := by exact_mod_cast hn
    refine ⟨le_rfl,by norm_num,by linarith,smooth.div_const _,?_,?_,?_⟩
    · intro u hu
      have hh := shape u (fun hz => hu (by simp [hz]))
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
    · refine ⟨5/2,fun u hu => ?_⟩
      have hh := shape u (fun hz => hu (by simp [hz]))
      exact ⟨hh.1.le,by linarith [hh.2]⟩
    · intro u
      rw [abs_div, abs_of_pos hk, abs_of_nonneg f.nonneg, deriv_div_const,
        abs_div, abs_of_pos hk, one_mul]
      constructor
      · exact (div_le_one hk).mpr (f.le_one.trans (le_max_right _ _))
      · exact (div_le_one hk).mpr ((hC u).trans (le_max_left _ _))

private theorem prime_shifts {p : ℕ} (hp : 40 < p) (pr : Nat.Prime p)
    (hmod : p ≡ 29 [MOD 35]) :
    Even (p+3) ∧ (3 : ℕ).Coprime (p+3) ∧ ¬ IsPrimePow (p+6) := by
  have h35 : 35 ∣ p+6 :=
    Nat.modEq_zero_iff_dvd.mp ((hmod.add_right 6).trans (by decide : 29+6 ≡ 0 [MOD 35]))
  have notpow : ¬ IsPrimePow (p+6) := by
    intro h
    obtain ⟨_,_,unique⟩ := isPrimePow_iff_unique_prime_dvd.mp h
    have h5 := unique 5 ⟨by decide, (by decide : 5 ∣ 35).trans h35⟩
    have h7 := unique 7 ⟨by decide, (by decide : 7 ∣ 35).trans h35⟩
    omega
  have cp : (3:ℕ).Coprime (p+3) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hh
    have h3 : 3 ∣ p := by omega
    rcases (Nat.dvd_prime pr).mp h3 with h|h <;> omega
  obtain ⟨k,hk⟩ := pr.odd_of_ne_two (by omega)
  exact ⟨⟨k+2,by omega⟩,cp,notpow⟩

/-- An unconditional progression and one fixed smooth weight. No GRH,
Hardy-space identity, or Maier estimate occurs in this theorem. -/
theorem unconditional_shift :
    ∃ b : ℝ → ℝ, 0 < b 3 ∧
      (∀ K : ℕ, ∃ p > max K 40, Nat.Prime p ∧ p ≡ 29 [MOD 35]) ∧
      ∀ p : ℕ, 40 < p → Nat.Prime p → p ≡ 29 [MOD 35] →
        Even (p+3) ∧ ShiftTest (p+3) 1 2 b ∧
        oppositeSum (p+3) b = Real.log 3 * b 3 * Real.log p := by
  obtain ⟨b,h3,hrest,test⟩ := fixed_weight
  refine ⟨b,h3,fun K => Nat.forall_exists_prime_gt_and_modEq (max K 40)
    (q := 35) (a := 29) (by decide) (by decide),?_⟩
  intro p hp pr hmod
  obtain ⟨he,cp,np⟩ := prime_shifts hp pr hmod
  refine ⟨he,test _ (by omega),?_⟩
  unfold oppositeSum
  rw [Finset.sum_eq_single 3]
  · rw [ite_eq_left cp, show p+3-3=p by omega, show p+3+3=p+6 by omega,
      vonMangoldt_apply_prime (by decide : Nat.Prime 3), vonMangoldt_apply_prime pr,
      vonMangoldt_eq_zero_iff.mpr np, sub_zero]
    norm_num
  · intro m _ hn
    simp [hrest m hn]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

/-- The weaker logarithmic lower bound needs only the Hardy transfer. In
particular, it is independent of the arithmetic input of Y. Liu, Section 3. -/
theorem one_shift_lower {M : ℕ → ℝ} {G : ℕ → Prop} (transfer : ShiftTransfer M G) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, ∃ N ≥ K, Even N ∧
      (G N → c*Real.log N^2 ≤ (N:ℝ)*(M N)^2) := by
  obtain ⟨C,hC,F,estimate⟩ := transfer
  obtain ⟨b,hb,cofinal,data⟩ := unconditional_shift
  let v := Real.log 3 * b 3
  have hv : 0 < v := mul_pos (Real.log_pos (by norm_num)) hb
  refine ⟨v^2/(16*C),by positivity,fun K => ?_⟩
  obtain ⟨p,hp,pr,hmod⟩ := cofinal (max K F)
  obtain ⟨he,test,iden⟩ := data p (by omega) pr hmod
  refine ⟨p+3,by omega,he,fun hg => ?_⟩
  have hpp : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hlog := Real.log_pos hpp
  have hN : (1:ℝ) < (p+3:ℕ) := by push_cast; linarith
  have hlN := Real.log_pos hN
  have logs : Real.log (p+3:ℕ) ≤ 2*Real.log p := by
    have hh := Real.log_le_log (by linarith : (0:ℝ) < (p+3:ℕ))
      (show ((p+3:ℕ):ℝ) ≤ (p:ℝ)^2 by
        push_cast; have : (3:ℝ) < p := by exact_mod_cast (show 3 < p by omega)
        nlinarith)
    simpa [Real.log_pow] using hh
  have L := pow_le_pow_left₀ hlN.le logs 2
  have bound := estimate (p+3) (by omega) he hg 1 2 b test
  rw [iden] at bound
  change 1*(v*Real.log p)^2 ≤ C*2^2*((p+3:ℕ):ℝ)*(M (p+3))^2 at bound
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left L (sq_nonneg v)]

end GoldbachSpectral

