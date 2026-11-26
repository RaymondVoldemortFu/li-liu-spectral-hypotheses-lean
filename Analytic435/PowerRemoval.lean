module
public import SquareRemoval
public import ConditionalGoldbach.Proofs.PrimePowerReindex
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.PSeries

/-! Uniform removal of proper prime powers above a polylogarithmic threshold
from the Li–Liu quadratic form. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset ConditionalGoldbach Complex Filter
open scoped Topology ComplexConjugate
namespace GoldbachSpectral435.SquareResidues
open GoldbachSpectral435.PerronApproximation

def discarded (N : ℕ) : Finset ℕ :=
  (allIndices N).filter (fun n => (squareFloor N)^2 ≤ n ∧ ¬n.Prime)

def higher (N : ℕ) := discarded N \ largeSquares N

private def majorant (z : ℕ×ℕ) : ℝ :=
  (z.1:ℝ)^(-(9/8:ℝ))*((2:ℝ)^(-(3/8:ℝ)))^z.2

private lemma maj0 (z : ℕ×ℕ) : 0≤majorant z := by unfold majorant; positivity

private lemma summable_majorant : Summable majorant :=
  (Real.summable_nat_rpow.mpr (by norm_num : -(9/8:ℝ)< -1)).mul_of_nonneg
    (summable_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<2) (by norm_num : -(3/8:ℝ)<0)))
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun i => by positivity)

private lemma majorize {L : ℝ} (lp : 0<L) {p k : ℕ} (hp : 2≤p)
    (threshold : L^200≤((p^(k+3):ℕ):ℝ)) :
    ((p^(k+3):ℕ):ℝ)^(-(1/2:ℝ)) ≤ (L^25)⁻¹*majorant (p,k) := by
  have pp : 0<(p:ℝ) := by exact_mod_cast (by omega : 0<p)
  have np : 0<((p^(k+3):ℕ):ℝ) := by positivity
  have small := Real.rpow_le_rpow_of_nonpos (pow_pos lp 200) threshold (by norm_num : -(1/8:ℝ)≤0)
  have eq : (L^200)^(-(1/8:ℝ))=(L^25)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul lp.le]
    norm_num [Real.rpow_neg lp.le]
  rw [eq] at small
  have fac : ((p^(k+3):ℕ):ℝ)^(-(3/8:ℝ)) =
      (p:ℝ)^(-(9/8:ℝ))*((p:ℝ)^(-(3/8:ℝ)))^k := by
    rw [Nat.cast_pow,← Real.rpow_natCast,← Real.rpow_mul pp.le,← Real.rpow_natCast,
      ← Real.rpow_mul pp.le,← Real.rpow_add pp]
    push_cast; ring_nf
  rw [show -(1/2:ℝ) = -(1/8:ℝ) + -(3/8:ℝ) by norm_num,Real.rpow_add np,fac]
  apply mul_le_mul small _ (by positivity) (by positivity)
  unfold majorant
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by positivity)
    (Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<2) (by exact_mod_cast hp) (by norm_num)) _

private lemma index_bound {n N : ℕ} (hn : n∈allIndices N) : n≤(baseEnd N)^2 := by
  have cut : cutoff N (exponent N) = (((baseEnd N)^2:ℕ):ℝ) := by simp [cutoff,baseEnd]
  simpa only [allIndices,cut,Nat.floor_natCast,mem_range,Nat.lt_succ_iff] using hn

private lemma higher_repr {n N : ℕ} (hn : n∈higher N) (isp : IsPrimePow n) :
    ∃ p k : ℕ, p.Prime ∧ p≤(baseEnd N)^2 ∧ k≤(baseEnd N)^2 ∧ p^(k+3)=n := by
  obtain ⟨hd,ns⟩ := mem_sdiff.mp hn
  obtain ⟨hI,lb,com⟩ := mem_filter.mp hd
  have ub := index_bound hI
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp isp
  have bounds := prime_power_parameter_bounds hp hk
  have three : 3≤k := by
    by_contra! h
    interval_cases k
    · simp [hp] at com
    · apply ns
      apply mem_image.mpr
      refine ⟨p,mem_Ico.mpr ⟨?_,?_⟩,rfl⟩
      · exact le_of_not_gt (fun h => (not_lt_of_ge lb) (Nat.pow_lt_pow_left h (by decide)))
      · apply Nat.lt_succ_of_le
        exact le_of_not_gt (fun h => (not_lt_of_ge ub) (Nat.pow_lt_pow_left h (by decide)))
  exact ⟨p,k-3,hp,bounds.1.trans ub,by omega,by rw [Nat.sub_add_cancel three]⟩

private theorem higher_mass (N : ℕ) (big : Real.exp 10<(N:ℝ))
    (f : HardySpace (alpha N) beta) (hf : ‖f‖≤1) :
    (∑ n ∈ higher N, ‖testCoefficient N (exponent N) n f‖) ≤
      (612 * ∑' z, majorant z)/(Real.log N)^23 := by
  classical
  let c := fun n => testCoefficient N (exponent N) n f
  let L := Real.log N
  let X := (baseEnd N)^2
  let S := higher N
  let V := ((range (X+1)) ×ˢ (range (X+1))).filter
    (fun z : ℕ×ℕ => z.1.Prime ∧ z.1^(z.2+3) ∈ S)
  let idx := fun z : ℕ×ℕ => z.1^(z.2+3)
  have lp : 0<L := by
    have np := (Real.exp_pos 10).trans big
    dsimp [L]; linarith [(Real.lt_log_iff_exp_lt np).mpr big]
  have ⟨rp,xp,lr⟩ := parameters N big
  have im : V.image idx = S.filter IsPrimePow := by
    ext n
    constructor
    · rintro hn
      obtain ⟨⟨p,k⟩,h,rfl⟩ := mem_image.mp hn
      obtain ⟨hp,hS⟩ := (mem_filter.mp h).2
      exact mem_filter.mpr ⟨hS,(isPrimePow_nat_iff _).mpr ⟨p,k+3,hp,by omega,rfl⟩⟩
    · intro hn
      obtain ⟨hS,hp⟩ := mem_filter.mp hn
      obtain ⟨p,k,hpr,pX,kX,id⟩ := higher_repr hS hp
      refine mem_image.mpr ⟨(p,k),mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,hpr,?_⟩,id⟩
      · exact mem_range.mpr (Nat.lt_succ_of_le pX)
      · exact mem_range.mpr (Nat.lt_succ_of_le kX)
      · simpa only [id] using hS
  have inj : Set.InjOn idx V := by
    intro x hx y hy eq
    have a := (mem_filter.mp hx).2.1
    have b := (mem_filter.mp hy).2.1
    obtain ⟨p,k⟩ := a.pow_inj' b (by omega : x.2+3≠0) (by omega : y.2+3≠0) eq
    exact Prod.ext p (by omega)
  have onlyPow : ∑ n ∈ S, ‖c n‖ = ∑ n ∈ S.filter IsPrimePow, ‖c n‖ := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hp : IsPrimePow n
    · simp [hp]
    · have z : mangoldt n=0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp
      simp [hp,c,testCoefficient,z]
  change (∑ n ∈ S, ‖c n‖) ≤ _
  rw [onlyPow,← im,sum_image inj]
  have B0 : 0≤6*Real.log (baseEnd N) := by
    have := Real.log_nonneg (by exact_mod_cast rp : (1:ℝ)≤baseEnd N)
    positivity
  have cap (z : ℕ×ℕ) (hz : z∈V) : ‖c (idx z)‖ ≤ (612/L^23)*majorant z := by
    have ⟨hp,hS⟩ := (mem_filter.mp hz).2
    obtain ⟨hd,_⟩ := mem_sdiff.mp hS
    obtain ⟨hi,lb,_⟩ := mem_filter.mp hd
    have np : 0 < idx z := pow_pos hp.pos _
    have yr : L^100 ≤ (squareFloor N:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
    have rr : L^200 ≤ (idx z:ℝ) := calc
      _ = (L^100)^2 := by ring
      _ ≤ (squareFloor N:ℝ)^2 := pow_le_pow_left₀ (by positivity) yr 2
      _ ≤ _ := by exact_mod_cast lb
    have b := coefficient_decay N _ _ (baseEnd N) big xp np (index_bound hi) f hf
    have term := majorize lp hp.two_le rr
    calc
      _ ≤ (6*Real.log (baseEnd N))*((idx z:ℝ)^(-(1/2:ℝ))) := b
      _ ≤ (612*L^2)*((L^25)⁻¹*majorant z) :=
        mul_le_mul (by dsimp [L]; linarith only [lr]) term (by positivity) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ z ∈ V, (612/L^23)*majorant z := sum_le_sum cap
    _ = (612/L^23)*(∑ z ∈ V, majorant z) := (mul_sum ..).symm
    _ ≤ (612/L^23)*(∑' z, majorant z) := mul_le_mul_of_nonneg_left
      (summable_majorant.sum_le_tsum _ (fun i _ => maj0 i)) (by positivity)
    _ = _ := by dsimp [L]; ring

private lemma energy_of_absolute (N : ℕ) [NeZero N] (he : Even N) (four : 4≤N)
    (S : Finset ℕ) (c : ℕ→ℂ) :
    meanEnergy N (amplitude S c) ≤ (∑ n ∈ S, ‖c n‖)^2 ∧
      diagonalEnergy N S c ≤ (∑ n ∈ S, ‖c n‖)^2 := by
  let B := ∑ n ∈ S, ‖c n‖
  have point (χ : Character N) : ‖amplitude S c χ‖≤B := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n _
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
  constructor
  · unfold meanEnergy
    apply (mul_le_mul_of_nonneg_left
      (sum_le_sum (fun χ (_ : χ∈oddCharacters N) => pow_le_pow_left₀ (norm_nonneg _) (point χ) 2))
      (by positivity : 0≤2/(N.totient:ℝ))).trans_eq
    rw [sum_const,nsmul_eq_mul,← mul_assoc,odd_character_average_mass N he four,one_mul]
  · unfold diagonalEnergy
    apply le_trans _ (sum_sq_le_sq_sum_of_nonneg (s:=S) (f:=fun n => ‖c n‖) (fun _ _ => norm_nonneg _))
    apply sum_le_sum
    intro n _
    split_ifs <;> first | exact le_rfl | positivity

private lemma squares_discarded (N : ℕ) : largeSquares N ⊆ discarded N := by
  intro n hn
  apply mem_filter.mpr
  refine ⟨square_subset N hn,?_⟩
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hn
  exact ⟨Nat.pow_le_pow_left (mem_Ico.mp hu).1 2,Nat.Prime.not_prime_pow (by decide)⟩

private lemma combine (N : ℕ) [NeZero N] (c : ℕ→ℂ) :
    meanEnergy N (amplitude (discarded N) c) ≤
      2*(meanEnergy N (amplitude (higher N) c)+meanEnergy N (amplitude (largeSquares N) c)) ∧
    diagonalEnergy N (discarded N) c =
      diagonalEnergy N (higher N) c+diagonalEnergy N (largeSquares N) c := by
  constructor
  · have split (χ : Character N) : amplitude (higher N) c χ+amplitude (largeSquares N) c χ =
        amplitude (discarded N) c χ := sum_sdiff (squares_discarded N)
    have localBound (χ : Character N) : ‖amplitude (discarded N) c χ‖^2 ≤
        2*(‖amplitude (higher N) c χ‖^2 + ‖amplitude (largeSquares N) c χ‖^2) := by
      rw [← split]
      apply (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans
      nlinarith only [sq_nonneg (‖amplitude (higher N) c χ‖-‖amplitude (largeSquares N) c χ‖)]
    unfold meanEnergy
    apply (mul_le_mul_of_nonneg_left (sum_le_sum (fun χ (_ : χ∈oddCharacters N) => localBound χ))
      (by positivity : 0≤2/(N.totient:ℝ))).trans_eq
    rw [← mul_sum,sum_add_distrib]
    ring
  · exact (sum_sdiff (squares_discarded N)).symm

theorem prime_power_trim_error :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ (_ : NeZero N), Even N →
      Real.exp 10<(N:ℝ) → GRH N → ∀ (ha : alpha N<beta) (f : HardySpace (alpha N) beta),
      ‖f‖≤1 → ‖inner ℂ f (residualOperator ha N f) -
        ((finiteForm N ((allIndices N).filter (fun n => n.Prime ∨ n<(squareFloor N)^2))
          (fun n => testCoefficient N (exponent N) n f):ℂ) -
         inner ℂ f (modelOperator ha N f))‖ ≤ C/(Real.log N)^16 := by
  classical
  let A : ℝ := 612*∑' z, majorant z
  let K : ℝ := 4*612^2*103*104
  have ap : 0≤A := mul_nonneg (by norm_num) (tsum_nonneg maj0)
  have kp : 0<K := by norm_num [K]
  have id (N : ℕ) : allIndices N\discarded N =
      (allIndices N).filter (fun n => n.Prime ∨ n<(squareFloor N)^2) := by
    ext n
    simp only [discarded,mem_filter]
    by_cases hi : n∈allIndices N <;> by_cases p : n.Prime <;> simp [hi,p]
  simp_rw [← id]
  apply trim_error discarded (fun _ => filter_subset ..) (2*(A^2+K)) (by positivity)
  filter_upwards [floor_fits] with N fit
  intro inst he big _ f hf c
  let L := Real.log N
  have l1 : 1≤L := by
    have np := (Real.exp_pos 10).trans big
    dsimp [L]; linarith [(Real.lt_log_iff_exp_lt np).mpr big]
  have lp : 0<L := zero_lt_one.trans_le l1
  have m := higher_mass N big f hf
  have high := energy_of_absolute N he (large_parameters big).1 (higher N) c
  have mass : (∑ n ∈ higher N, ‖c n‖)^2 ≤ A^2/L^40 := calc
    _ ≤ (A/L^23)^2 := pow_le_pow_left₀ (by positivity) m 2
    _ = A^2/L^46 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_right₀ l1 (by decide : 40≤46))
  obtain ⟨s,d⟩ := large_square_energy N he big fit f hf
  have decay : K/L^92 ≤ K/L^40 := div_le_div_of_nonneg_left kp.le (by positivity)
    (pow_le_pow_right₀ l1 (by decide : 40≤92))
  have total := combine N c
  constructor
  · apply total.1.trans
    exact (mul_le_mul_of_nonneg_left (add_le_add (high.1.trans mass) (s.trans decay)) (by norm_num : (0:ℝ)≤2)).trans_eq (by dsimp [L]; ring)
  · rw [total.2]
    apply (add_le_add (high.2.trans mass) (d.trans decay)).trans
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [sq_nonneg A,kp]

#print axioms prime_power_trim_error
end GoldbachSpectral435.SquareResidues
