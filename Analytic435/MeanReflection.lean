module
public import Reflection
public import SquareRemoval
public import Mathlib.NumberTheory.Chebyshev

/-! Averaged control of the endpoints of the first Goldbach line. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset
open scoped Topology InnerProductSpace ComplexConjugate
namespace GoldbachSpectral435.MeanReflection

def primeWeight (n : ℕ) : ℝ := mangoldt n/Real.sqrt n

private theorem posWeight (n : ℕ) : 0≤primeWeight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

private def weightSum (X : ℕ) : ℝ := ∑ n ∈ Icc 0 X, primeWeight n

def chebyshevConstant : ℝ := Real.log 4+4

/-- A square-root weighted Chebyshev estimate with an absolute constant. -/
theorem weighted_chebyshev (X : ℕ) :
    (∑ n ∈ Icc 0 X, primeWeight n)≤4*chebyshevConstant*Real.sqrt X := by
  change weightSum X≤_
  induction X using Nat.strong_induction_on with
  | h X ih =>
    rcases Nat.eq_zero_or_pos X with rfl|xp
    · simp [weightSum,primeWeight]
    let Y := X/4
    have yx : Y<X := Nat.div_lt_self xp (by decide)
    have p := ih Y yx
    let C := chebyshevConstant
    have cp : 0≤C := by dsimp [C,chebyshevConstant]; positivity
    have xr : 0<(X:ℝ) := by exact_mod_cast xp
    have root := Real.sqrt_pos.mpr xr
    have point (n : ℕ) : primeWeight n≤
        (if n≤Y then primeWeight n else 0)+2*mangoldt n/Real.sqrt X := by
      have mp : 0≤mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      by_cases sh : n≤Y
      · simpa [sh] using (show 0≤2*mangoldt n/Real.sqrt X by positivity)
      · simp only [ite_eq_right_iff.mpr (fun h => (sh h).elim),zero_add]
        have q : X≤4*n := by dsimp [Y] at sh; omega
        have nr : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
        have rt : Real.sqrt X≤2*Real.sqrt n := by
          have h := Real.sqrt_le_sqrt (show (X:ℝ)≤4*n by exact_mod_cast q)
          rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)] at h
          norm_num at h
          exact h
        unfold primeWeight
        apply (div_le_div_iff₀ (Real.sqrt_pos.mpr nr) root).mpr
        exact (mul_le_mul_of_nonneg_left rt mp).trans_eq (by ring)
    have sub : (Icc 0 X).filter (·≤Y)=Icc 0 Y := by ext n; simp; omega
    have psi := Chebyshev.psi_le_const_mul_self xr.le
    rw [Chebyshev.psi_eq_sum_Icc,Nat.floor_natCast] at psi
    have rt : Real.sqrt Y≤Real.sqrt X/2 := by
      have le : 4*Y≤X := by dsimp [Y]; omega
      have q := Real.sqrt_le_sqrt (show (4:ℝ)*Y≤X by exact_mod_cast le)
      rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)] at q
      norm_num at q
      linarith
    calc
      weightSum X ≤ ∑ n ∈ Icc 0 X, ((if n≤Y then primeWeight n else 0)+2*mangoldt n/Real.sqrt X) :=
        sum_le_sum (fun n _ => point n)
      _ = weightSum Y+2*(∑ n ∈ Icc 0 X, mangoldt n)/Real.sqrt X := by
        rw [sum_add_distrib,← sum_filter,sub,← sum_div,← mul_sum]
        rfl
      _ ≤ 4*C*(Real.sqrt X/2)+2*(C*X)/Real.sqrt X := by
        apply add_le_add (p.trans (mul_le_mul_of_nonneg_left rt (by positivity))) _
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left psi (by norm_num)) root.le
      _ = _ := by
        have sq := Real.sq_sqrt xr.le
        change _=4*C*Real.sqrt X
        field_simp
        nlinarith only [congrArg (fun x : ℝ => C*x) sq]

/-- Positive majorant for two truncated inputs on n+j=N. -/
def pairMass (N Y Z : ℕ) : ℝ :=
  ∑ n ∈ Icc 0 Y, ∑ j ∈ Icc 0 Z, if n+j=N then primeWeight n*primeWeight j else 0

/-- Uniform summed estimate over any finite collection of distinct moduli.
One endpoint may be arbitrarily shorter than the other. -/
theorem sum_pairMass (I : Finset ℕ) (Y Z : ℕ) :
    ∑ N ∈ I, pairMass N Y Z ≤ (4*chebyshevConstant)^2*Real.sqrt Y*Real.sqrt Z := by
  classical
  unfold pairMass
  rw [sum_comm]
  calc
    _ ≤ ∑ n ∈ Icc 0 Y, ∑ j ∈ Icc 0 Z, primeWeight n*primeWeight j := by
      apply sum_le_sum
      intro n _
      rw [sum_comm]
      apply sum_le_sum
      intro j _
      rw [sum_ite_eq]
      split
      · rfl
      · exact mul_nonneg (posWeight _) (posWeight _)
    _ = (∑ n ∈ Icc 0 Y, primeWeight n)*(∑ j ∈ Icc 0 Z, primeWeight j) := by rw [sum_mul]; simp only [mul_sum]
    _ ≤ (4*chebyshevConstant*Real.sqrt Y)*(4*chebyshevConstant*Real.sqrt Z) :=
      mul_le_mul (weighted_chebyshev Y) (weighted_chebyshev Z)
        (sum_nonneg (fun n _ => posWeight n)) (by unfold chebyshevConstant; positivity)
    _ = _ := by ring

open MeasureTheory Complex
open GoldbachSpectral435.LocalPrimeForm GoldbachSpectral435.Reflection

private lemma coefficient_le {N : ℕ} (big : Real.exp 10<(N:ℝ)) (n : ℕ)
    (f : HardySpace (alpha N) beta) (fn : ‖f‖≤1) : ‖coefficient f n‖≤3*primeWeight n := by
  rcases Nat.eq_zero_or_pos n with rfl|np
  · simp [coefficient,primeWeight,mangoldt]
  have pos : 0<(n:ℝ) := by exact_mod_cast np
  have ip : ‖inner ℂ f (diagonalHardyVector n)‖≤3 := (norm_inner_le_norm _ _).trans
    (by simpa using mul_le_mul fn (SquareResidues.diagonal_vec N n big np) (norm_nonneg _) zero_le_one)
  have power : ‖(n:ℂ)^(-(1/2:ℂ))‖=(Real.sqrt n)⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos np]
    simp only [Complex.neg_re]
    norm_num
    rw [Real.rpow_neg pos.le,Real.sqrt_eq_rpow]
  simp only [coefficient,norm_mul,norm_neg,Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,power]
  rw [← div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left ip (posWeight _)).trans_eq (mul_comm _ _)

/-- For arbitrary unit vectors the first-block arithmetic entry is bounded
by the same positive majorant, with no logarithmic loss on average. -/
theorem entry_le_pairMass (N Y Z : ℕ) [NeZero N] (even : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (yp : 0<Y) (zp : 0<Z) (yn : Y≤N) (zn : Z≤N)
    (x y : HardySpace (alpha N) beta) (xn : ‖x‖≤1) (ynorm : ‖y‖≤1)
    (hx : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Y → x t=0)
    (hy : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log Z → y t=0) :
    ‖inner ℂ x ((arithmeticOperator ha N-diagonalOperator ha N) y)‖≤9*pairMass N Y Z := by
  classical
  rw [mixed_first_block N even big grh ha x y (widen yp yn x hx) (widen zp zn y hy),norm_neg]
  let rows (n : ℕ) : ℝ := ∑ j ∈ Icc 0 Z, if n+j=N then primeWeight n*primeWeight j else 0
  have rp (n : ℕ) : 0≤rows n := sum_nonneg (fun j _ => by split <;> first | exact mul_nonneg (posWeight _) (posWeight _) | rfl)
  change ‖∑ n ∈ range N, _‖≤9*∑ n ∈ Icc 0 Y, rows n
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ n ∈ range N, if n≤Y then 9*rows n else 0 := by
      apply sum_le_sum
      intro n hn
      have nn := (mem_range.mp hn).le
      by_cases ny : n≤Y
      · simp only [ite_eq_left ny]
        by_cases cp : n.Coprime N
        · simp only [ite_eq_left cp,norm_mul,RCLike.norm_conj]
          by_cases jz : N-n≤Z
          · have jmem : N-n∈Icc 0 Z := mem_Icc.mpr ⟨Nat.zero_le _,jz⟩
            have term := single_le_sum (s:=Icc 0 Z) (f:=fun j => if n+j=N then primeWeight n*primeWeight j else 0)
              (fun j _ => by split <;> first | exact mul_nonneg (posWeight _) (posWeight _) | rfl) jmem
            rw [ite_eq_left (show n+(N-n)=N by omega)] at term
            calc
              _ ≤ (3*primeWeight n)*(3*primeWeight (N-n)) := mul_le_mul (coefficient_le big _ x xn)
                (coefficient_le big _ y ynorm) (norm_nonneg _) (mul_nonneg (by norm_num) (posWeight n))
              _ = 9*(primeWeight n*primeWeight (N-n)) := by ring
              _ ≤ 9*rows n := mul_le_mul_of_nonneg_left term (by norm_num)
          · rw [sample_zero zp (by omega : Z≤N-n) (large_alpha_pos big).le ha y hy]
            simpa using mul_nonneg (by norm_num : (0:ℝ)≤9) (rp n)
        · simpa [cp] using (mul_nonneg (by norm_num : (0:ℝ)≤9) (rp n))
      · simp [ny,sample_zero yp (by omega : Y≤n) (large_alpha_pos big).le ha x hx]
    _ ≤ 9*∑ n ∈ Icc 0 Y, rows n := by
      rw [← sum_filter,mul_sum]
      exact sum_le_sum_of_subset_of_nonneg (fun n hn => mem_Icc.mpr ⟨Nat.zero_le _,(mem_filter.mp hn).2⟩)
        (fun n _ _ => mul_nonneg (by norm_num) (rp n))

#print axioms entry_le_pairMass
#print axioms weighted_chebyshev
#print axioms sum_pairMass
end GoldbachSpectral435.MeanReflection
