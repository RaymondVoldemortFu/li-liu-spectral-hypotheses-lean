module
public import PerronDiagonal
public import PerronOperators
public import OriginalBounds
public import ConditionalGoldbach.Proofs.VariableComponentOperators

/-! The arithmetic side of the full existence assertion as a finite sum of
prime-power Gram operators, with an error uniform in all unit test vectors. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex MeasureTheory Filter Set InnerProductSpace
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PerronApproximation

def exponent (N : ℕ) : ℕ := max 1 ⌈100*Real.log (Real.log N)⌉₊

def primeResidual (N : ℕ) [NeZero N] (ha : alpha N<beta) :=
  primeGram N (exponent N) - primeDiagonal N (exponent N) - modelOperator ha N

theorem residual_error : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
    Real.exp 10<(N:ℝ) → GRH N → ∀ ha : alpha N<beta,
      ‖residualOperator ha N-primeResidual N ha‖ ≤ C/(Real.log N)^16 := by
  obtain ⟨K,kp,gram⟩ := operator_error
  let B := 16*Real.pi*(Real.log 4+4)
  have bp : 0<B := by dsimp [B]; positivity
  refine ⟨K+B,by positivity,?_⟩
  intro N inst he big g ha
  have m1 : 1≤exponent N := le_max_left ..
  have hm : 100*Real.log (Real.log N) ≤ exponent N := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr (le_max_right ..))
  obtain ⟨n4,lp,_⟩ := large_parameters big
  have one : 1≤Real.log N := by
    have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
    linarith [(Real.lt_log_iff_exp_lt np).mpr big]
  have a := gram N inst he big g ha (exponent N) m1 hm
  have b : ‖diagonalOperator ha N-primeDiagonal N (exponent N)‖ ≤ B/(Real.log N)^16 :=
    (diagonal_error N big ha _ m1 hm).trans (div_le_div_of_nonneg_left bp.le (by positivity)
      (pow_le_pow_right₀ one (by decide : 16≤18)))
  rw [residualOperator_components_at _ N (large_alpha_pos big) n4 g ha,primeResidual,
    show arithmeticOperator ha N-diagonalOperator ha N-modelOperator ha N-
      (primeGram N (exponent N)-primeDiagonal N (exponent N)-modelOperator ha N) =
      (arithmeticOperator ha N-primeGram N (exponent N))-(diagonalOperator ha N-primeDiagonal N (exponent N)) by abel,
    add_div]
  exact (norm_sub_le _ _).trans (add_le_add a b)

def primeNorm (N : ℕ) : ℝ := by
  classical
  exact if h : N ≠ 0 ∧ alpha N<beta ∧ GRH N then
    ‖@primeResidual N ⟨h.1⟩ h.2.1‖ else 0

private theorem norm_difference : ∃ C : ℝ, 0<C ∧ EvenEventually (fun N =>
    |eligibleNorm N-primeNorm N| ≤ C/(Real.log N)^16) := by
  obtain ⟨C,hC,err⟩ := residual_error
  obtain ⟨K,large⟩ := evenEventually_large
  refine ⟨C,hC,K,fun N hn he => ?_⟩
  have big := large N hn he
  obtain ⟨n4,lp,ha⟩ := large_parameters big
  let inst : NeZero N := ⟨by omega⟩
  change |eligibleNorm N-primeNorm N| ≤ _
  by_cases g : GRH N
  · rw [eligibleNorm_spec N ha g]
    have pv : primeNorm N=‖primeResidual N ha‖ := by simp [primeNorm,NeZero.ne N,ha,g]
    rw [pv]
    exact (abs_norm_sub_norm_le _ _).trans (err N inst he big g ha)
  · simp [eligibleNorm,primeNorm,g,div_nonneg hC.le (pow_nonneg lp.le _)]

/-- Existence of any admissible prescription has exactly the original
quantifiers, with finite arithmetic operators and the explicit beta model. -/
theorem existence_iff_prime_residual :
    (∃ h, HypothesisS h) ↔ ∀ ε : ℝ, 0<ε →
      EvenEventually (fun N => primeNorm N ≤ ε*singularSeries N) := by
  rw [some_actual_S_iff]
  obtain ⟨C,_,cl⟩ := norm_difference
  have close (ε : ℝ) (ep : 0<ε) : EvenEventually (fun N =>
      |eligibleNorm N-primeNorm N| ≤ (ε/2)*singularSeries N) := by
    have logs := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    have rate : Tendsto (fun n : ℕ => C/(Real.log n)^16) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 16≠0)).comp logs)
    obtain ⟨J,small⟩ := eventually_atTop.mp (rate.eventually_lt_const (show 0<ε/2 by positivity))
    obtain ⟨K,bnd⟩ := cl
    refine ⟨max K J,fun N hn he => ?_⟩
    have ss : 1≤singularSeries N := by rw [original_series]; exact GoldbachSpectral.singular_lower N
    exact ((bnd N (by omega) he).trans (small N (by omega)).le).trans
      (le_mul_of_one_le_right (by positivity) ss)
  constructor <;> intro small ε ep
  · obtain ⟨K,h⟩ := (small (ε/2) (by positivity)).and (close ε ep)
    refine ⟨K,fun N hn he => ?_⟩
    obtain ⟨a,b⟩ := h N hn he
    linarith only [a,(abs_le.mp b).1]
  · obtain ⟨K,h⟩ := (small (ε/2) (by positivity)).and (close ε ep)
    refine ⟨K,fun N hn he => ?_⟩
    obtain ⟨a,b⟩ := h N hn he
    linarith only [a,(abs_le.mp b).2]

#print axioms existence_iff_prime_residual
end GoldbachSpectral435.PerronApproximation
