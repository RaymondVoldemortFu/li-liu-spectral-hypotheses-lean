module
public import OriginalStatements
public import ConditionalGoldbach.Proofs.QuantitativeBounds

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral Filter
namespace GoldbachSpectral435

/-- The kernel's verified uniform Hilbert--Schmidt estimate supplies a
positive exclusion width. The explicit admissible choice h = log asks
for a width which exceeds every fixed multiple of this guaranteed width. -/
theorem guaranteed_width_and_log_gap :
    ∃ c : ℝ, 0<c ∧
      EvenEventually (fun N => ∀ (inst : NeZero N) (ha : alpha N<beta), GRH N →
        @SpectralZeroFree N inst (alpha N) ha (c*singularSeries N/(N*Real.log N))) ∧
      ∀ A : ℝ, EvenEventually (fun N =>
        A*(c*singularSeries N/(N*Real.log N))≤zeroFreeWidth N (fun n => Real.log n)) := by
  obtain ⟨_,c,_,cp,K,bound⟩ := theorem_6_2
  refine ⟨c,cp,⟨K,fun N hn ev inst ha g => (bound N hn ev inst ha g).2.2.2⟩,?_⟩
  intro A
  obtain ⟨F,cap⟩ := eventually_atTop.mp eventually_small_series
  have logs := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨J,large⟩ := eventually_atTop.mp (logs.eventually_ge_atTop (max 1 (A*c)))
  refine ⟨max (max F J) 2,fun N hn _ => ?_⟩
  let l := Real.log (N:ℝ)
  let s := singularSeries N
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have sp : 0<s := singularSeries_pos N
  have lc : max 1 (A*c)≤l := large N (by omega)
  have one : 1≤l := (le_max_left _ _).trans lc
  have lp : 0<l := zero_lt_one.trans_le one
  have sc : s≤l^2 := by simpa only [s,l,original_series] using (cap N (by omega)).2
  have ac : A*c≤l^2 :=
    ((le_max_right _ _).trans lc).trans (by nlinarith only [one,sq_nonneg (l-1)])
  have s4 : s^2≤(l^2)^2 := pow_le_pow_left₀ sp.le sc 2
  have six : (A*c)*s^2≤l^6 := calc
    _ ≤ l^2*s^2 := mul_le_mul_of_nonneg_right ac (sq_nonneg _)
    _ ≤ l^2*(l^2)^2 := mul_le_mul_of_nonneg_left s4 (sq_nonneg _)
    _ = l^6 := by ring
  change A*(c*s/((N:ℝ)*l))≤l^2*l^3/((N:ℝ)*s)
  rw [mul_div_assoc', div_le_div_iff₀ (mul_pos np lp) (mul_pos np sp)]
  calc
    _ = (N:ℝ)*((A*c)*s^2) := by ring
    _ ≤ (N:ℝ)*l^6 := mul_le_mul_of_nonneg_left six np.le
    _ = _ := by ring

/-- Exact obstruction to *all* admissible choices. The operator in each
witness is the original one and each witness satisfies its own local GRH. -/
theorem no_admissible_S_iff :
    (¬∃ h, HypothesisS h) ↔
      ∃ ε : ℝ, 0<ε ∧ ∀ K : ℕ, ∃ N≥K, Even N ∧ GRH N ∧
        ∃ inst : NeZero N, ∃ ha : alpha N<beta,
          ε*singularSeries N < ‖@residualOperator (alpha N) ha N inst‖ := by
  rw [some_actual_S_iff]
  constructor
  · intro absent
    by_contra! none
    apply absent
    intro ε ep
    obtain ⟨K,small⟩ := none ε ep
    obtain ⟨F,big⟩ := evenEventually_large
    refine ⟨max F K,fun N hn ev => ?_⟩
    obtain ⟨four,_,ha⟩ := large_parameters (big N (by omega) ev)
    have inst : NeZero N := ⟨by omega⟩
    by_cases g : GRH N
    · rw [@eligibleNorm_spec N inst ha g]
      exact small N (by omega) ev g inst ha
    · simp [eligibleNorm,g,mul_nonneg ep.le (singularSeries_pos N).le]
  · rintro ⟨ε,ep,row⟩ limit
    obtain ⟨K,tiny⟩ := limit ε ep
    obtain ⟨N,nk,ev,g,inst,ha,lower⟩ := row K
    have upper : eligibleNorm N≤ε*singularSeries N := tiny N nk ev
    rw [@eligibleNorm_spec N inst ha g] at upper
    exact (not_lt_of_ge upper) lower

#print axioms guaranteed_width_and_log_gap
#print axioms no_admissible_S_iff
end GoldbachSpectral435

