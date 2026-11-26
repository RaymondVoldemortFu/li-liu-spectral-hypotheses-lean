import UnconditionalAudit
import Lean.Util.CollectAxioms

/-! Statement checks for Theorem 1.1 of the R manuscript and Li–Liu's original R. -/
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter
open scoped Topology
namespace GoldbachSpectral435.RPaperAudit

/-- Li–Liu, pp. 3–4 and Appendix A.1. The local GRH and eventual quantifiers
are written out, as are both endpoints of the Hardy strip. -/
def originalR : Prop :=
  ∃ K : ℕ, ∀ N ≥ K, Even N →
    (∀ d : ℕ, ∀ (_ : NeZero d), d ∣ N → ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2) →
    ∀ (inst : NeZero N) (ha : 1 / Real.log N < (1 / 8 : ℝ)) (q : Quaternion ℝ),
      spectralQuaternion N (@residualOperator (1 / Real.log N) ha N inst) q = 0 →
        q.re = 1 / 2

theorem statement_agrees : ConditionalGoldbach.HypothesisR = originalR := rfl

theorem main_normalization : HypothesisRAt 1 = originalR := rfl

theorem scale_squared (N : ℕ) (large : Real.exp 10 < (N : ℝ)) :
    spectralScale N ^ 2 = singularSeries N * Real.log N ^ 3 / N := by
  rw [spectralScale_sq N ((Real.exp_pos _).trans large) (singularSeries_pos N).le
    (large_parameters large).2.1.le]
  ring

/-- The two choices used to define the operator and the infinite product
realize the kernel and the convergent partial products at eligible moduli. -/
theorem realization (N : ℕ) [NeZero N] (he : Even N) (large : Real.exp 10 < (N : ℝ))
    (ha : alpha N < beta) :
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) ∧
    ∀ q : Quaternion ℝ, Tendsto (fun k : ℕ => (List.range k).foldl (fun acc j =>
      acc * (1 - (4 * eigenvalues (residualOperator ha N) j ^ 2 / spectralScale N ^ 2 : ℝ) •
        (q * (1 - q)))) 1)
      atTop (𝓝 (spectralQuaternion N (residualOperator ha N) q)) := by
  have g := Unconditional.local_GRH N
  exact ⟨(proposition_5_3 N he large g ha).2.1,
    spectralPartialQuaternion_tendsto N _ (residualOperator_has_spectral_data N he large g ha)⟩

/-- All three conclusions of the manuscript, with the original operator and
quaternionic product and with one sequence working for all exponents. -/
theorem paper_theorem :
    (∀ d K : ℕ, ∃ N ≥ K, Even N ∧ ∃ inst : NeZero N, ∃ ha : 1 / Real.log N < (1 / 8 : ℝ),
      Real.log N ^ d < (N : ℝ) * ‖@residualOperator (1 / Real.log N) ha N inst‖ ^ 2) ∧
    ¬originalR ∧
    ∃ (N : ℕ → ℕ) (x : ℕ → ℝ), StrictMono N ∧
      (∀ i, Even (N i) ∧ x i < 1 ∧ ∃ inst : NeZero (N i),
        ∃ ha : 1 / Real.log (N i) < (1 / 8 : ℝ),
          spectralQuaternion (N i) (@residualOperator (1 / Real.log (N i)) ha (N i) inst)
            (x i : Quaternion ℝ) = 0) ∧
      ∀ d : ℕ, Tendsto (fun i => Real.log (N i) ^ d * (1 - x i)) atTop (𝓝 0) := by
  obtain ⟨N, x, increasing, zeros, limits, _⟩ := common_zero_sequence Unconditional.local_GRH
  exact ⟨norm_lower_on_original Unconditional.local_GRH, Unconditional.not_R,
    N, x, increasing, zeros, limits⟩

#print axioms statement_agrees
#print axioms main_normalization
#print axioms scale_squared
#print axioms realization
#print axioms paper_theorem
open Lean Elab Command in
run_cmd
  for decl in [``statement_agrees, ``main_normalization, ``scale_squared, ``realization, ``paper_theorem] do
    let axioms ← liftCoreM (Lean.collectAxioms decl)
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
end GoldbachSpectral435.RPaperAudit
