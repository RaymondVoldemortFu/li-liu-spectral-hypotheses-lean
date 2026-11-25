module
public import PrimeLower

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral
namespace GoldbachSpectral435

private theorem tested {N : ℕ} [NeZero N] {ha : alpha N<beta} {H P C : ℝ} {b : ℝ → ℝ}
    (bound : H*(oppositeSum N b)^2≤C*P^2*N*‖residualOperator ha N‖^2)
    (cp : 0≤C) (z : ℝ) (nm : ‖residualOperator ha N‖≤z) :
    H*(oppositeSum N b)^2≤ C*P^2*N*z^2 :=
  bound.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) nm 2) (by positivity))

/-- R bounds every normalized shift, simultaneously with one absolute constant. -/
theorem R_forces_shifts (R : HypothesisR) :
    ∃ C : ℝ, 0<C ∧ EvenEventually (fun N => GRH N → ∀ H P b,
      ShiftTest N H P b → H*(oppositeSum N b)^2 ≤ C*P^2*singularSeries N*(Real.log N)^3) := by
  obtain ⟨C,cp,T⟩ := actual_transfer
  obtain ⟨K,step⟩ := R.and evenEventually_large
  refine ⟨C,cp,K,?_⟩
  intro N hn he g H P b w
  obtain ⟨r,lar⟩ := step N hn he
  obtain ⟨four,lg,ha⟩ := large_parameters lar
  let : NeZero N := ⟨by omega⟩
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have sp := singularSeries_pos N
  have nm := (theorem_6_1 N he lar g ha).1.mp (r g inferInstance ha)
  have h := tested (T N he lar g ha H P b w) cp.le _ nm
  rw [spectralScale_sq N np sp.le lg.le] at h
  exact h.trans_eq (by field_simp)

/-- S imposes an explicit upper bound for the same arithmetic shifts for each
prescribed admissible function, including the full factor from the half-plane. -/
theorem S_forces_shifts {h : ℕ → ℝ} (S : HypothesisS h) :
    ∃ C : ℝ, 0<C ∧ EvenEventually (fun N => GRH N → ∀ H P b,
      ShiftTest N H P b → H*(oppositeSum N b)^2*(2*h N*Real.sqrt (1-zeroFreeWidth N h))^2 ≤
        C*P^2*N*(singularSeries N)^2) := by
  obtain ⟨C,cp,T⟩ := actual_transfer
  obtain ⟨⟨positive,_,width⟩,half⟩ := S
  obtain ⟨K,step⟩ := half.and (width.and evenEventually_large)
  refine ⟨C,cp,K,?_⟩
  intro N hn he g H P b w
  obtain ⟨s,cap,lar⟩ := step N hn he
  obtain ⟨four,lg,ha⟩ := large_parameters lar
  let : NeZero N := ⟨by omega⟩
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have sp := singularSeries_pos N
  have hp := positive N he four
  have wp : 0<zeroFreeWidth N h := by unfold zeroFreeWidth; positivity
  have nm := ((theorem_6_1 N he lar g ha).2.1 _ wp (by linarith)).mp (s g inferInstance ha)
  rw [spectralScale_div_sqrt_width_eq N h np sp lg hp (by linarith)] at nm
  have rp : 0<Real.sqrt (1-zeroFreeWidth N h) := Real.sqrt_pos.mpr (by linarith)
  let d := 2*h N*Real.sqrt (1-zeroFreeWidth N h)
  have dp : 0<d := by dsimp [d]; positivity
  have u := tested (T N he lar g ha H P b w) cp.le (singularSeries N/d) nm
  apply (mul_le_mul_of_nonneg_right u (sq_nonneg d)).trans_eq
  field_simp [dp.ne']

#print axioms R_forces_shifts
#print axioms S_forces_shifts
end GoldbachSpectral435

