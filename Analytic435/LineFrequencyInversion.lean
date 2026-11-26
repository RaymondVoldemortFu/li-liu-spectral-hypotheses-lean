module
public import DyadicLineArithmetic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Fourier inversion of a prescribed integer line inside one congruence. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace GoldbachSpectral435.GoldbachSieve

def frequencyTerm (q M : ℕ) (k : ℤ) (v t : ℝ) : ℝ :=
  if (q:ℤ)∣k then v*Real.cos (t*((k:ℝ)/M)) else 0

def frequencySlice (q M : ℕ) (d : ℤ) (sign : Bool) (a b : ℕ→ℝ) (t : ℝ) : ℝ :=
  ∑ n∈range M,∑ m∈range M,frequencyTerm q M (lineCoordinate sign n m-d) (a n*b m) t

lemma continuous_frequencyTerm (q M : ℕ) (k : ℤ) (v : ℝ) : Continuous (frequencyTerm q M k v) := by
  unfold frequencyTerm
  split <;> fun_prop

lemma continuous_frequencySlice (q M : ℕ) (d : ℤ) (sign : Bool) (a b : ℕ→ℝ) :
    Continuous (frequencySlice q M d sign a b) :=
  continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_frequencyTerm ..

private lemma integrate_frequency (q M : ℕ) (qp : 0<q) (mp : 0<M) (k : ℤ) (v : ℝ) :
    let A := Real.pi*M/q
    (∫ t in -A..A,frequencyTerm q M k v t)=2*A*(if k=0 then v else 0) := by
  intro A
  by_cases hk : k=0
  · subst k
    simp only [frequencyTerm,dvd_zero,ite_true,Int.cast_zero,zero_div,mul_zero,Real.cos_zero,mul_one,
      intervalIntegral.integral_const,smul_eq_mul]
    ring
  by_cases dv : (q:ℤ)∣k
  · obtain ⟨j,hj⟩ := dv
    let u : ℝ := k/M
    have mr : (M:ℝ)≠0 := Nat.cast_ne_zero.mpr mp.ne'
    have qr : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr qp.ne'
    have un : u≠0 := div_ne_zero (Int.cast_ne_zero.mpr hk) mr
    have eq : A*u=(j:ℝ)*Real.pi := by
      change Real.pi*M/q*((k:ℝ)/M)=_
      rw [hj]
      push_cast
      field_simp
    have z : (∫ t in -A..A, Real.cos (t*u))=0 := by
      rw [intervalIntegral.integral_comp_mul_right Real.cos un,integral_cos,neg_mul,eq,
        Real.sin_neg,Real.sin_int_mul_pi]
      simp
    simp only [frequencyTerm,ite_eq_left (show (q:ℤ)∣k from ⟨j,hj⟩),ite_eq_right hk,mul_zero]
    rw [intervalIntegral.integral_const_mul]
    exact mul_eq_zero_of_right v z
  · simp [frequencyTerm,dv,hk]

/-- This is exact for each prescribed integer d, both signs, and arbitrary
real weights. The integration interval has length 2πM/q. -/
theorem frequency_recovers_line (q M : ℕ) (qp : 0<q) (mp : 0<M) (d : ℤ) (sign : Bool) (a b : ℕ→ℝ) :
    let A := Real.pi*M/q
    (∫ t in -A..A,frequencySlice q M d sign a b t)=2*A*exactLine M M d sign a b := by
  intro A
  have integ (n m : ℕ) := (continuous_frequencyTerm q M (lineCoordinate sign n m-d) (a n*b m)).intervalIntegrable
    (μ:=volume) (-A) A
  have row (n : ℕ) := (continuous_finsetSum (range M) (fun m _ =>
    continuous_frequencyTerm q M (lineCoordinate sign n m-d) (a n*b m))).intervalIntegrable
    (μ:=volume) (-A) A
  unfold frequencySlice exactLine
  rw [intervalIntegral.integral_finsetSum (fun n _ => row n),mul_sum]
  apply sum_congr rfl
  intro n _
  rw [intervalIntegral.integral_finsetSum (fun m _ => integ n m),mul_sum]
  apply sum_congr rfl
  intro m _
  simpa only [sub_eq_zero] using integrate_frequency q M qp mp (lineCoordinate sign n m-d) (a n*b m)

#print axioms frequency_recovers_line
end GoldbachSpectral435.GoldbachSieve
