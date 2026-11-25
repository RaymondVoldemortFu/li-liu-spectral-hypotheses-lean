module
public import SpectralTests.Shifts

@[expose] public section
namespace GoldbachSpectral
open Finset ArithmeticFunction

/-- Exact von Mangoldt term at either opposite shift, retaining coprimality. -/
noncomputable def shifted (N m : ℕ) (plus : Bool) : ℝ :=
  if m.Coprime N then vonMangoldt (if plus then N+m else N-m) else 0

/-- The unrestricted arithmetic main term of a unit residue class. Integer
subtraction is essential, because a central shift can exceed the residue a. -/
def unitResidue (q : ℕ) (a : ℤ) : ℝ := if a.natAbs.Coprime q then 1 else 0

theorem sum_rows (S : Finset ℕ) (b : ℝ → ℝ) {R : ℕ}
    (cut : ∀ m : ℕ, R ≤ m → b m = 0) (above : ∀ N ∈ S, R ≤ N) :
    ∑ N ∈ S, oppositeSum N b =
      ∑ m ∈ range R, (vonMangoldt m*b m) *
        ((∑ N ∈ S, shifted N m false) - ∑ N ∈ S, shifted N m true) := by
  classical
  have row (N : ℕ) (hN : R ≤ N) : oppositeSum N b =
      ∑ m ∈ range R, vonMangoldt m*b m*(shifted N m false - shifted N m true) := by
    unfold oppositeSum
    rw [← sum_subset (range_mono hN) (fun m _ hm => by
      rw [cut m (by simpa using hm)]; simp)]
    apply sum_congr rfl
    intro m _
    unfold shifted
    split_ifs <;> simp_all
  calc
    _ = ∑ N ∈ S, ∑ m ∈ range R, vonMangoldt m*b m*
      (shifted N m false - shifted N m true) :=
        sum_congr rfl (fun N hN => row N (above N hN))
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      rw [← sum_sub_distrib, mul_sum]

/-- Transfer from signed unit-class averages to a genuine modulus, with both
endpoint errors paid for each m. None of its inputs mentions an operator. -/
theorem residue_row_witness {S : Finset ℕ} (hne : S.Nonempty)
    {R q : ℕ} {a : ℤ} {b : ℝ → ℝ} {U E A : ℝ}
    (cut : ∀ m : ℕ, R ≤ m → b m = 0) (above : ∀ N ∈ S, R ≤ N)
    (wpos : ∀ m : ℕ, 0 ≤ b m)
    (minus : ∀ m ∈ range R, U*unitResidue q (a-m)-E ≤ ∑ N ∈ S, shifted N m false)
    (plus : ∀ m ∈ range R, (∑ N ∈ S, shifted N m true) ≤ U*unitResidue q (a+m)+E)
    (signal : (S.card:ℝ)*A ≤
      U*(∑ m ∈ range R, vonMangoldt m*b m*(unitResidue q (a-m)-unitResidue q (a+m))) -
        2*E*(∑ m ∈ range R, vonMangoldt m*b m)) :
    ∃ N ∈ S, A ≤ oppositeSum N b := by
  have lower : (S.card:ℝ)*A ≤ ∑ N ∈ S, oppositeSum N b := by
    rw [sum_rows S b cut above]
    apply signal.trans
    rw [mul_sum,mul_sum, ← sum_sub_distrib]
    apply sum_le_sum
    intro m hm
    have w := mul_nonneg (vonMangoldt_nonneg (n := m)) (wpos m)
    have d := sub_le_sub (minus m hm) (plus m hm)
    have pay := mul_le_mul_of_nonneg_left d w
    linarith only [pay,
      show U*(vonMangoldt m*b m*(unitResidue q (a-m)-unitResidue q (a+m))) -
        2*E*(vonMangoldt m*b m) =
        vonMangoldt m*b m*(U*unitResidue q (a-m)-E-(U*unitResidue q (a+m)+E)) by ring]
  by_contra! none
  have h := Finset.sum_lt_sum_of_nonempty hne none
  simpa using (not_lt_of_ge lower) (by simpa using h)

end GoldbachSpectral
