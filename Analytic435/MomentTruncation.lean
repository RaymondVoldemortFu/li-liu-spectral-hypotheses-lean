module
public import ConditionalGoldbach.Proofs.CharacterShortPolynomial

/-! The contribution of every Dirichlet polynomial of length below the modulus
to the difference of odd-character moments at levels N and 2N. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex
open scoped ComplexConjugate
namespace GoldbachSpectral435.ConductorMoments

def polynomialMoment (N : ℕ) [NeZero N] (I : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N, ‖∑ m ∈ I, a m * χ m‖ ^ 2

/-- The modulus-doubling difference of the two finite second moments has
exactly one additive correlation. Coefficients and their phases are arbitrary. -/
theorem truncated_increment_exact (N : ℕ) [NeZero N] (even : Even N) (four : 4 ≤ N)
    (I : Finset ℕ) (a : ℕ → ℂ) (short : ∀ n ∈ I, a n ≠ 0 → 0 < n ∧ n < N) :
    ((polynomialMoment (2*N) I a - polynomialMoment N I a : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ m ∈ I,
        if Nat.Coprime (n*m) N ∧ n+m=N then a n * conj (a m) else 0 := by
  classical
  have twice : Even (2*N) := even_two.mul_right _
  have units (d : ℕ) : Nat.Coprime d (2*N) ↔ Nat.Coprime d N := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨And.right, fun h => ⟨h.coprime_dvd_right (even_iff_two_dvd.mp even),h⟩⟩
  rw [Complex.ofReal_sub,polynomialMoment,polynomialMoment,
    odd_character_quadratic_complex _ twice (by omega),
    odd_character_quadratic_complex _ even four,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases an : a n=0
  · simp [an]
  by_cases am : a m=0
  · simp [am]
  obtain ⟨np,nN⟩ := short n hn an
  obtain ⟨mp,mN⟩ := short m hm am
  obtain ⟨low,neg⟩ := residue_diagonals (by omega : 0<N) np nN mp mN
  obtain ⟨high,neg'⟩ := residue_diagonals (by omega : 0<2*N) np (by omega) mp (by omega)
  have ne : n+m ≠ 2*N := by omega
  simp only [units,low,neg,high,neg',ne,ite_false,sub_zero]
  split_ifs <;> simp_all

/-- All coefficients at integers strictly below N/2 give zero increment. -/
theorem short_increment_zero (N : ℕ) [NeZero N] (even : Even N) (four : 4 ≤ N)
    (I : Finset ℕ) (a : ℕ → ℂ) (short : ∀ n ∈ I, a n ≠ 0 → 0<n ∧ 2*n<N) :
    polynomialMoment (2*N) I a = polynomialMoment N I a := by
  have support : ∀ n ∈ I, a n ≠ 0 → 0<n ∧ n<N := by
    intro n hn nz
    obtain ⟨np,small⟩ := short n hn nz
    exact ⟨np,by omega⟩
  have key := truncated_increment_exact N even four I a support
  have vanish : (∑ n ∈ I, ∑ m ∈ I, if Nat.Coprime (n*m) N ∧ n+m=N then
      a n * conj (a m) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro m hm
    by_cases an : a n=0
    · simp [an]
    by_cases am : a m=0
    · simp [am]
    have h1 := (short n hn an).2
    have h2 := (short m hm am).2
    simp [show n+m≠N by omega]
  rw [vanish, Complex.ofReal_eq_zero] at key
  exact sub_eq_zero.mp key

#print axioms truncated_increment_exact
#print axioms short_increment_zero
end GoldbachSpectral435.ConductorMoments
