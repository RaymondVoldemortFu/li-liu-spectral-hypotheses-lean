module
public import Mathlib.Data.Int.CardIntervalMod
public import SpectralTests.BandSieve

@[expose] public section
namespace GoldbachSpectral.BandSieve
open Finset

/-- Exact periodic counting controls two residue classes by an absolute constant,
uniform in the modulus and in both interval endpoints. -/
theorem residue_discrepancy {d : ℤ} (hd : 0 < d) (u v A B : ℤ) (hab : A ≤ B) :
    |((Finset.Ioc A B).filter (fun n => n ≡ u [ZMOD d])).card -
      (((Finset.Ioc A B).filter (fun n => n ≡ v [ZMOD d])).card : ℤ)| ≤ 2 := by
  have hq : (0:ℚ) < d := by exact_mod_cast hd
  have floorBound (r : ℤ) :
      |(((Finset.Ioc A B).filter (fun n => n ≡ r [ZMOD d])).card : ℚ) -
        ((B:ℚ)-A)/d| ≤ 1 := by
    have order : ((A:ℚ)-r)/d ≤ ((B:ℚ)-r)/d :=
      div_le_div_of_nonneg_right (sub_le_sub_right (by exact_mod_cast hab) _) hq.le
    have eqn := Int.Ioc_filter_modEq_card A B hd r
    rw [max_eq_left (sub_nonneg.mpr (Int.floor_mono order))] at eqn
    have fromZ := congrArg (fun t : ℤ => (t:ℚ)) eqn
    push_cast at fromZ
    rw [fromZ]
    obtain ⟨l₁,l₂⟩ := Int.floor_eq_iff.mp (rfl : ⌊((A:ℚ)-r)/d⌋ = _)
    obtain ⟨r₁,r₂⟩ := Int.floor_eq_iff.mp (rfl : ⌊((B:ℚ)-r)/d⌋ = _)
    have add : ((B:ℚ)-r)/d - ((A:ℚ)-r)/d = ((B:ℚ)-A)/d := by ring
    rw [← add]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have a := abs_le.mp (floorBound u)
  have b := abs_le.mp (floorBound v)
  have up : |(((Finset.Ioc A B).filter (fun n => n ≡ u [ZMOD d])).card : ℚ) -
      (((Finset.Ioc A B).filter (fun n => n ≡ v [ZMOD d])).card : ℚ)| ≤ 2 :=
    abs_le.mpr ⟨by linarith [a.1,b.2],by linarith [a.2,b.1]⟩
  exact_mod_cast up

/-- Finite summation by parts. The shift in the prefix index is needed when
both residue classes are truncated at a moving endpoint. -/
theorem abel_finite (a w : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, a i * w i =
      (∑ i ∈ range n, a i)*w n +
      ∑ i ∈ range n, (∑ k ∈ range (i+1), a k)*(w i-w (i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
      Finset.sum_range_succ (f := fun i => (∑ k ∈ range (i+1), a k)*(w i-w (i+1))),
      Finset.sum_range_succ]
    ring

theorem weighted_discrepancy (a w : ℕ → ℝ) (n : ℕ) {D : ℝ}
    (bound : ∀ k ≤ n, |∑ i ∈ range k, a i| ≤ D) :
    |∑ i ∈ range n, a i*w i| ≤ D*(|w n| + ∑ i ∈ range n, |w i-w (i+1)|) := by
  rw [abel_finite, mul_add, Finset.mul_sum]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (bound n le_rfl) (abs_nonneg _)
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (bound _ (by have := Finset.mem_range.mp hi; omega)) (abs_nonneg _)

end GoldbachSpectral.BandSieve
