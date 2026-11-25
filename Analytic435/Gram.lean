module
public import Samples

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex
open scoped ComplexConjugate
namespace GoldbachSpectral435

def selectOdd (N : ℕ) [NeZero N] (n m : ℕ) : ℂ :=
  (2/(N.totient:ℂ))*∑ χ ∈ oddCharacters N, χ n*conj (χ m)

private theorem selector_symm (N : ℕ) [NeZero N] (he : Even N) (hn : 4≤N) (m n : ℕ) :
    selectOdd N m n = selectOdd N n m := by
  unfold selectOdd
  simp_rw [lemma_3_1_odd_orthogonality N he hn]
  rw [Nat.mul_comm m n]
  have e : ((m:ZMod N) = -(n:ZMod N)) ↔ (n:ZMod N) = -(m:ZMod N) := by
    rw [← add_eq_zero_iff_eq_neg,← add_eq_zero_iff_eq_neg,add_comm]
  have ep : ((m:ZMod N)=(n:ZMod N)) ↔ (n:ZMod N)=(m:ZMod N) := eq_comm
  simp only [e,ep]

/-- Finite bilinear form of the odd-character projector, with the two
sampling sequences ordered independently. -/
def projected (N M : ℕ) [NeZero N] (A B : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, A m*B n*selectOdd N n m

theorem gram_projected (N M : ℕ) [NeZero N] (he : Even N) (hn : 4≤N) (hm : 0<M)
    (f g : ℝ → ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g) :
    (2/(N.totient:ℂ))*∑ χ ∈ oddCharacters N,
      characterSample χ M (companion f)*characterSample (star χ) M (companion g) =
    projected N M (fun n => (sampleValue M n f:ℂ)) (fun n => (sampleValue M n g:ℂ)) := by
  unfold projected
  conv_rhs => rw [Finset.sum_comm]
  simp_rw [finite_character_sample _ M hm f hf,finite_character_sample _ M hm g hg]
  simp only [MulChar.star_apply,RCLike.star_def,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [selector_symm N he hn m n]
  unfold selectOdd
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem projected_symm (N M : ℕ) [NeZero N] (he : Even N) (hn : 4≤N) (A B : ℕ → ℂ) :
    projected N M A B = projected N M B A := by
  unfold projected
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [selector_symm N he hn n m]
  ring

theorem projected_add (N M : ℕ) [NeZero N] (he : Even N) (hn : 4≤N) (A B : ℕ → ℂ) :
    projected N M (A+B) (A+B) =
      projected N M A A + projected N M B B + 2*projected N M A B := by
  have identity : projected N M (A+B) (A+B) =
    projected N M A A + projected N M B B + (projected N M A B + projected N M B A) := by
    unfold projected
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    simp only [Pi.add_apply]
    ring
  rw [identity,projected_symm N M he hn B A]
  ring

/-- Isolate the two physical samples in the finite bilinear form.
The broad sequence may include prime powers. -/
theorem projected_shifts (N : ℕ) [NeZero N] (he : Even N) (hn : 4≤N) (A B : ℕ → ℂ)
    (sf : ∀ m, A m ≠ 0 → 0<m ∧ 4*m<N) (sg : ∀ n, B n ≠ 0 → 3*N<4*n ∧ 4*n<5*N) :
    projected N (2*N) A B = ∑ m ∈ Finset.range (2*N), A m *
      (if m.Coprime N then B (N+m)-B (N-m) else 0) := by
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : A m=0
  · simp [h]
  · have sp := sf m h
    simp only [mul_assoc,← Finset.mul_sum]
    rw [← broad_projection N m he hn sp.1 sp.2 B sg]
    rfl

#print axioms gram_projected
#print axioms projected_shifts
end GoldbachSpectral435

