module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic

/-! Local spacing of squares in one residue class and a uniform harmonic
bound for the square terms of the prime-power correlations. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset
namespace GoldbachSpectral435.SquareResidues

private lemma vandermonde {N : ℕ} (a b c : ℤ)
    (hab : (a:ZMod N)^2=(b:ZMod N)^2) (hac : (a:ZMod N)^2=(c:ZMod N)^2) :
    (N:ℤ) ∣ (b-a)*(c-a)*(c-b) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  calc
    _ = ((b:ZMod N)-a)*(c^2-a^2)-((c:ZMod N)-a)*(b^2-a^2) := by ring
    _ = 0 := by rw [← hab,← hac]; ring

/-- Three different square roots of a residue cannot lie in one interval
of length h when the modulus exceeds h cubed. -/
theorem short_square_fiber (N Y h : ℕ) (size : h^3<N) (r : ZMod N) :
    ((Finset.Ico Y (Y+h)).filter (fun n : ℕ => (n:ZMod N)^2=r)).card ≤ 2 := by
  classical
  by_contra! bad
  obtain ⟨i,j,k,hi,hj,hk,ij,ik,jk⟩ := Finset.two_lt_card_iff.mp bad
  obtain ⟨si,ei⟩ := Finset.mem_filter.mp hi
  obtain ⟨sj,ej⟩ := Finset.mem_filter.mp hj
  obtain ⟨sk,ek⟩ := Finset.mem_filter.mp hk
  have g := vandermonde (N:=N) i j k (by simpa using ei.trans ej.symm) (by simpa using ei.trans ek.symm)
  obtain ⟨il,iu⟩ := Finset.mem_Ico.mp si
  obtain ⟨jl,ju⟩ := Finset.mem_Ico.mp sj
  obtain ⟨kl,ku⟩ := Finset.mem_Ico.mp sk
  have d₁ : |(j:ℤ)-i| ≤ h := abs_le.mpr ⟨by omega,by omega⟩
  have d₂ : |(k:ℤ)-i| ≤ h := abs_le.mpr ⟨by omega,by omega⟩
  have d₃ : |(k:ℤ)-j| ≤ h := abs_le.mpr ⟨by omega,by omega⟩
  let t : ℤ := ((j:ℤ)-i)*(k-i)*(k-j)
  have pos : 0 < |t| := abs_pos.mpr (mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by omega))
  have divides : (N:ℤ) ∣ |t| := by
    rcases le_total 0 t with hpos | hneg
    · rwa [abs_of_nonneg hpos]
    · rwa [abs_of_nonpos hneg,dvd_neg]
  have lower : (N:ℤ) ≤ |t| := Int.le_of_dvd pos divides
  have upper : |t| ≤ (h:ℤ)^3 := by
    dsimp only [t]
    rw [abs_mul,abs_mul,pow_succ,pow_two]
    gcongr
  exact (not_le_of_gt (show (h:ℤ)^3 < N by exact_mod_cast size)) (lower.trans upper)

private lemma block (N Y h : ℕ) (size : h^3<N) (r : ZMod N) (hy : 0<Y) :
    ∑ n ∈ Finset.Ico Y (Y+h), (if (n:ZMod N)^2=r then 1/(n:ℝ) else 0) ≤ 2/Y := by
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _ ∈ (Finset.Ico Y (Y+h)).filter (fun n : ℕ => (n:ZMod N)^2=r), 1/(Y:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_left zero_le_one (by exact_mod_cast hy)
        (by exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1)
    _ ≤ _ := by
      rw [Finset.sum_const,nsmul_eq_mul]
      have bound : (((Finset.Ico Y (Y+h)).filter (fun n : ℕ => (n:ZMod N)^2=r)).card:ℝ) ≤ 2 := by
        exact_mod_cast short_square_fiber N Y h size r
      convert mul_le_mul_of_nonneg_right bound (by positivity : 0≤1/(Y:ℝ)) using 1
      ring

/-- A harmonic bound in one square class with arbitrary finite upper
endpoint. Both constants come from counting roots in disjoint intervals. -/
theorem square_fiber_harmonic (N Y h R : ℕ) (size : h^3<N) (r : ZMod N)
    (hy : 0<Y) (hh : 0<h) :
    ∑ n ∈ Finset.Ico Y (R+1), (if (n:ZMod N)^2=r then 1/(n:ℝ) else 0) ≤
      2/(Y:ℝ)+(2/(h:ℝ))*(1+Real.log R) := by
  let g (n : ℕ) : ℝ := if (n:ZMod N)^2=r then 1/(n:ℝ) else 0
  have hr : 0<(h:ℝ) := by exact_mod_cast hh
  have partial_sum (k : ℕ) :
      ∑ n ∈ Finset.Ico Y (Y+(k+1)*h), g n ≤ 2/(Y:ℝ)+(2/(h:ℝ))*(harmonic k:ℝ) := by
    induction k with
    | zero => simpa [g] using block N Y h size r hy
    | succ k ih =>
      let u := Y+(k+1)*h
      have eqv : Y+(k+1+1)*h=u+h := by dsimp [u]; ring
      rw [eqv,← Finset.sum_Ico_consecutive g (show Y≤u by dsimp [u]; omega) (Nat.le_add_right u h)]
      have b := block N u h size r (by dsimp [u]; omega)
      have ku : ((k+1:ℕ):ℝ)*(h:ℝ) ≤ u := by exact_mod_cast (show (k+1)*h ≤ u by dsimp [u]; omega)
      have cap : 2/(u:ℝ) ≤ (2/(h:ℝ))*(((k+1:ℕ):ℝ))⁻¹ := by
        have d := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤2) (by positivity) ku
        exact d.trans_eq (by simp only [div_eq_mul_inv,mul_inv_rev]; ring)
      rw [harmonic_succ,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast]
      exact (add_le_add ih (b.trans cap)).trans_eq (by ring)
  have endpt : R+1 ≤ Y+(R+1)*h := by
    have hh1 := Nat.mul_le_mul_left (R+1) (show 1≤h from hh)
    omega
  change ∑ n ∈ Finset.Ico Y (R+1), g n ≤ _
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right endpt)
    (fun n _ _ => by dsimp [g]; split <;> positivity)).trans
  exact (partial_sum R).trans (add_le_add_right
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log R) (by positivity : 0≤2/(h:ℝ))) _)

#print axioms square_fiber_harmonic
#print axioms short_square_fiber
end GoldbachSpectral435.SquareResidues
