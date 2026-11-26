module
public import SquareResidues
public import PrimeCorrelations

/-! A uniform second moment for squared indices in the odd-character
Gram form. All estimates use finite sums. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset ConditionalGoldbach Complex
open scoped ComplexConjugate
namespace GoldbachSpectral435.SquareResidues
open GoldbachSpectral435.PerronApproximation

def squares (Y R : ℕ) : Finset ℕ := (Ico Y (R+1)).image (fun u => u^2)

lemma sum_squares {M : Type*} [AddCommMonoid M] (Y R : ℕ) (f : ℕ → M) :
    ∑ n ∈ squares Y R, f n = ∑ u ∈ Ico Y (R+1), f (u^2) := by
  apply Finset.sum_image
  intro a _ b _ e
  nlinarith only [e,sq_nonneg (a-b:ℤ),show (0:ℕ)≤a by omega,show (0:ℕ)≤b by omega]

lemma harmonic_interval {Y R : ℕ} (hy : 0<Y) :
    ∑ n ∈ Ico Y (R+1), 1/(n:ℝ) ≤ 1+Real.log R := by
  apply le_trans _ (harmonic_le_one_add_log R)
  rw [harmonic_eq_sum_Icc,Rat.cast_sum]
  simp only [Rat.cast_inv,Rat.cast_natCast,one_div]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro n hn
  obtain ⟨a,b⟩ := mem_Ico.mp hn
  exact mem_Icc.mpr ⟨by omega,by omega⟩

private lemma weighted_fiber (N Y R : ℕ) (hY : Y^3<N) (hy : 0<Y)
    (r : ZMod N) (c : ℕ → ℂ) {B : ℝ} (b0 : 0≤B)
    (cap : ∀ u ∈ Ico Y (R+1), ‖c (u^2)‖ ≤ B/u) :
    (∑ v ∈ squares Y R, if (v:ZMod N)=r then ‖c v‖ else 0) ≤
        B*((2/(Y:ℝ))*(2+Real.log R)) := by
  rw [sum_squares]
  simp only [Nat.cast_pow]
  have clear : ∑ u ∈ Ico Y (R+1), (if (u:ZMod N)^2=r then ‖c (u^2)‖ else 0) ≤
      B*∑ u ∈ Ico Y (R+1), (if (u:ZMod N)^2=r then 1/(u:ℝ) else 0) := by
    rw [mul_sum]
    apply sum_le_sum
    intro u hu
    split_ifs
    · simpa only [div_eq_mul_inv,one_mul] using cap u hu
    · simp
  exact clear.trans ((mul_le_mul_of_nonneg_left (square_fiber_harmonic N Y Y R hY r hy hy) b0).trans_eq (by ring))

/-- Uniform mean square for any coefficients on large squares. The
constant does not depend on the residue structure of the modulus. -/
theorem square_mean (N Y R : ℕ) [NeZero N] (he : Even N) (four : 4≤N)
    (hY : Y^3<N) (hy : 0<Y) (hr : 1≤R) (c : ℕ → ℂ) {B : ℝ} (b0 : 0≤B)
    (cap : ∀ u ∈ Ico Y (R+1), ‖c (u^2)‖ ≤ B/u) :
    (2/(N.totient:ℝ))*∑ χ ∈ oddCharacters N, ‖∑ n ∈ squares Y R, c n*χ n‖^2 ≤
      4*B^2*(1+Real.log R)*(2+Real.log R)/Y := by
  classical
  let S := squares Y R
  let F := B*((2/(Y:ℝ))*(2+Real.log R))
  have log0 : 0≤Real.log R := Real.log_nonneg (by exact_mod_cast hr)
  have fp : 0≤F := by dsimp [F]; positivity
  let w (r : ZMod N) (v : ℕ) := if (v:ZMod N)=r then ‖c v‖ else 0
  have row (n : ℕ) : ∑ v ∈ S, ‖c v‖*‖residueSign N n v‖ ≤ F+F := by
    have term (v : ℕ) : ‖c v‖*‖residueSign N n v‖ ≤ w n v + w (-(n:ZMod N)) v := by
      unfold residueSign w
      have b : ((v:ZMod N)=-(n:ZMod N)) ↔ (n:ZMod N)=-(v:ZMod N) := by
        constructor <;> intro eqv <;> simpa using (congrArg Neg.neg eqv).symm
      simp only [b,show ((v:ZMod N)=n) ↔ (n:ZMod N)=v from eq_comm]
      split_ifs <;> simp
    apply (sum_le_sum (fun v _ => term v)).trans
    rw [sum_add_distrib]
    exact add_le_add (weighted_fiber N Y R hY hy _ c b0 cap) (weighted_fiber N Y R hY hy _ c b0 cap)
  have total : ∑ v ∈ S, ‖c v‖ ≤ B*(1+Real.log R) := by
    rw [show S=squares Y R from rfl,sum_squares]
    apply (sum_le_sum cap).trans
    simp_rw [div_eq_mul_inv]
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using harmonic_interval (R:=R) hy) b0
  have id := congrArg norm (odd_character_quadratic_complex N he four S c)
  have positive : 0≤ (2/(N.totient:ℝ))*∑ χ ∈ oddCharacters N, ‖∑ n ∈ S, c n*χ n‖^2 := by positivity
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg positive] at id
  change _ = ‖∑ n ∈ S, ∑ v ∈ S, c n*conj (c v)*residueSign N n v‖ at id
  rw [show squares Y R=S from rfl,id]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ S, ‖c n‖*(F+F) := by
      apply sum_le_sum
      intro n _
      apply (norm_sum_le _ _).trans
      simp only [norm_mul,RCLike.norm_conj,mul_assoc,← mul_sum]
      exact mul_le_mul_of_nonneg_left (row n) (norm_nonneg _)
    _ ≤ B*(1+Real.log R)*(F+F) := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right total (by positivity)
    _ = _ := by dsimp [F]; ring

#print axioms square_mean
end GoldbachSpectral435.SquareResidues
