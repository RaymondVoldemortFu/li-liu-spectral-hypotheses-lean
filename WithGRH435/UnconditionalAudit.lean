import Main
import OriginalStatements
import SingleScaleCriterion

/-! Spectral consequences of the independently formalized Dirichlet GRH. -/
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral
namespace GoldbachSpectral435.Unconditional

/-- Every modulus meets the original local GRH premise. -/
theorem local_GRH (N : ℕ) : GRH N :=
  all_local_of_primitive LFunction_eq_zero_re_of_isPrimitive N

/-- The Li–Liu spectral hypothesis R is false. -/
theorem not_R : ¬HypothesisR := refute_R local_GRH

/-- The prescribed widths are admissible and fail the original S. -/
theorem prescribed (j : ℕ) :
    IsAdmissible (prescribedH j) ∧ ¬HypothesisS (prescribedH j) :=
  prescribed_failure local_GRH j

/-- The full existence problem is an unconditional uniform assertion
about prime pairs at every sufficiently large even integer. -/
theorem some_S_iff :
    (∃ h, HypothesisS h) ↔ ∀ ε : ℝ, 0<ε → EvenEventually
      (fun N => FiniteDiscrepancy.UniformBound N (ε*singularSeries N)) := by
  rw [FiniteDiscrepancy.some_S_iff]
  constructor
  · intro h ε ep
    obtain ⟨K,s⟩ := (h ε ep).and evenEventually_large
    refine ⟨K,fun N hn he => ?_⟩
    obtain ⟨b,big⟩ := s N hn he
    have four := (large_parameters big).1
    let inst : NeZero N := ⟨by omega⟩
    exact b (local_GRH N)
  · intro h ε ep
    obtain ⟨K,s⟩ := h ε ep
    exact ⟨K,fun N hn he _ _ => s N hn he⟩

/-- An explicit single dilation suffices at every large even modulus. -/
theorem some_S_iff_single_scale :
    (∃ h, HypothesisS h) ↔ ∀ ε : ℝ, 0<ε → EvenEventually
      (fun N => PhysicalTests.ScaleBound N (PhysicalTests.scale N) (ε*singularSeries N)) := by
  rw [PhysicalTests.exists_iff_single_scale]
  constructor
  · intro h ε ep
    obtain ⟨K,s⟩ := (h ε ep).and evenEventually_large
    refine ⟨K,fun N hn he => ?_⟩
    obtain ⟨b,big⟩ := s N hn he
    have four := (large_parameters big).1
    let inst : NeZero N := ⟨by omega⟩
    exact b (local_GRH N)
  · intro h ε ep
    obtain ⟨K,s⟩ := h ε ep
    exact ⟨K,fun N hn he _ _ => s N hn he⟩

#print axioms some_S_iff_single_scale
#print axioms local_GRH
#print axioms not_R
#print axioms prescribed
#print axioms some_S_iff
end GoldbachSpectral435.Unconditional
