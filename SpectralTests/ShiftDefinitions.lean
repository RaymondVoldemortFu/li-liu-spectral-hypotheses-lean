module
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace GoldbachSpectral
open Set ArithmeticFunction
open scoped ContDiff

/-- The signed arithmetic observable from Y. Liu, Section 2. -/
noncomputable def oppositeSum (N : ℕ) (b : ℝ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range N, if m.Coprime N then
    vonMangoldt m * b m * (vonMangoldt (N-m)-vonMangoldt (N+m)) else 0

/-- Uniform normalization; separate suprema bounded by one cost at most a factor
of two relative to the normalization of Lemma 2.1. -/
structure ShiftTest (N : ℕ) (H P : ℝ) (b : ℝ → ℝ) : Prop where
  one_le : 1 ≤ H
  width_le : H ≤ P
  small : P < (N:ℝ)/20
  smooth : ContDiff ℝ ∞ b
  band : Function.support b ⊆ Icc P (2*P)
  short_support : ∃ t : ℝ, Function.support b ⊆ Icc t (t+H)
  normalized : ∀ u, |b u| ≤ 1 ∧ H*|deriv b u| ≤ 1

/-- The analytic transfer in Lemma 2.1, with one uniform squared constant. -/
def ShiftTransfer (M : ℕ → ℝ) (G : ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ N ≥ K, Even N → G N → ∀ H P b,
    ShiftTest N H P b → H*(oppositeSum N b)^2 ≤ C*P^2*N*(M N)^2

end GoldbachSpectral

