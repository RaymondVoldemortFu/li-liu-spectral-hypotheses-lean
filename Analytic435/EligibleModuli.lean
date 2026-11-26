module
public import ActualLimits
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! Arithmetic consequences of the local GRH quantifier in the original
existence assertion. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex
namespace GoldbachSpectral435.EligibleModuli

/-- The primitive character of conductor one occurs at every modulus.
The completed functional equation deals with zeros to the left of the
open critical strip in mathlib's statement of RH. -/
theorem rh_of_local {N : ℕ} (g : GRH N) : RiemannHypothesis := by
  intro s z nontriv _
  have nz : s≠0 := by
    intro eq
    rw [eq,riemannZeta_zero] at z
    norm_num at z
  have right : s.re<1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h z)
  have left : 0<s.re := by
    by_contra! h
    have gamma : Gammaℝ s≠0 := by
      intro v
      obtain ⟨n,e⟩ := Gammaℝ_eq_zero_iff.mp v
      cases n with
      | zero => exact nz (by simpa using e)
      | succ n => exact nontriv ⟨n,by simpa [Nat.cast_succ,neg_mul] using e⟩
    rw [riemannZeta_def_of_ne_zero nz] at z
    have c := (div_eq_zero_iff.mp z).resolve_right gamma
    have o : 1≤(1-s).re := by simpa using h
    have os : 1-s≠0 := by intro eq; have := congrArg Complex.re eq; simp at this; linarith
    apply riemannZeta_ne_zero_of_one_le_re o
    rw [riemannZeta_def_of_ne_zero os,completedRiemannZeta_one_sub,c,zero_div]
  apply g 1 inferInstance (one_dvd N) (1 : DirichletCharacter ℂ 1)
    DirichletCharacter.isPrimitive_one_level_one s left right
  simpa only [DirichletCharacter.LFunction_modOne_eq] using z

/-- Failure of the existential spectral assertion forces eligible moduli
arbitrarily far out among the even integers. -/
theorem unbounded_of_failure (fail : ¬∃ h, HypothesisS h) (K : ℕ) :
    ∃ N : ℕ, K≤N ∧ Even N ∧ GRH N := by
  by_contra! no
  apply fail
  refine ⟨fun n => Real.log n,isAdmissible_log,K,?_⟩
  intro n hn he g
  exact (no n hn he g).elim

/-- An unconditional disproof of the full existential statement implies
the ordinary Riemann hypothesis. -/
theorem rh_of_failure (fail : ¬∃ h, HypothesisS h) : RiemannHypothesis := by
  obtain ⟨N,_,_,g⟩ := unbounded_of_failure fail 4
  exact rh_of_local g

#print axioms rh_of_local
#print axioms rh_of_failure
end GoldbachSpectral435.EligibleModuli
