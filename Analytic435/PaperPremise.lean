module
public import ArithmeticWidths

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral
namespace GoldbachSpectral435

/-- Each positive conductor divides arbitrarily large even moduli. -/
theorem paper_GRH_iff : EvenEventually GRH ↔ ∀ N, GRH N := by
  constructor
  · rintro ⟨K, tail⟩ N d inst _
    have dp : 0 < d := Nat.pos_of_ne_zero inst.out
    let m := d * (K + 1)
    have large : K ≤ m + m := by
      dsimp [m]
      nlinarith only [Nat.mul_le_mul_right (K+1) dp]
    exact tail (m+m) large ⟨m, rfl⟩ d inst ⟨(K+1)+(K+1), (Nat.mul_add ..).symm⟩
  · intro all
    exact ⟨0, fun n _ _ => all n⟩

/-- The negative conclusions with the exact eventual local premise of
Li and Liu's Theorem 1.1 and Theorem 1.2. -/
theorem paper_spectral_consequences (g : EvenEventually GRH) :
    ¬HypothesisR ∧
    (∀ (h : ℕ → ℝ) (j : ℕ),
      EvenEventually (fun N => logWidth j N ≤ zeroFreeWidth N h) → ¬HypothesisS h) ∧
    IsAdmissible arithmeticH ∧ ¬HypothesisS arithmeticH := by
  have all := paper_GRH_iff.mp g
  exact ⟨refute_R all, refute_S all, arithmeticH_admissible all, arithmetic_width_refuted all⟩

#print axioms paper_GRH_iff
#print axioms paper_spectral_consequences
end GoldbachSpectral435

