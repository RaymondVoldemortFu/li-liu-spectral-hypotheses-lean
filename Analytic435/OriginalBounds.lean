module
public import SpectralTestsAtScale
public import SpectralTests.Obstruction

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach GoldbachSpectral Filter
open scoped Topology
namespace GoldbachSpectral435

/-- The primitive-character statement in the independent Dirichlet GRH
verification, specialized to precisely the source's conductor condition. -/
theorem all_local_of_primitive (input : ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive →
    ∀ z : ℂ, 0<z.re → z.re<1 → χ.LFunction z=0 → z.re=1/2) :
    ∀ N, GRH N := fun _ _ _ _ χ prim => input _ χ prim

theorem original_series (N : ℕ) : singularSeries N=singular N := by
  open MathlibNt.SieveTheory.SingularSeries in
  have coeff (p : ℕ) : 1+liuBaseDeviation p=twinFactor p := by
    unfold liuBaseDeviation twinFactor
    split_ifs <;> ring
  unfold ConditionalGoldbach.singularSeries singular MathlibNt.SieveTheory.SingularSeries.liuSingularSeries
    MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct
  simp_rw [coeff]
  unfold MathlibNt.SieveTheory.SingularSeries.liuCorrection MathlibNt.SieveTheory.SingularSeries.liuCorrectionFactor
  ring

theorem actual_R_failure_of_growth (global : ∀ N, GRH N) (growth : LiuInput eligibleNorm GRH) :
    ¬HypothesisR := by
  intro R
  obtain ⟨L,cap⟩ := eventually_atTop.mp eventually_small_series
  obtain ⟨K,claim⟩ := R.and evenEventually_large
  obtain ⟨N,hn,he,up⟩ := growth 5 (max K L)
  obtain ⟨r,lar⟩ := claim N (by omega) he
  obtain ⟨lg,small⟩ := cap N (by omega)
  obtain ⟨four,logp,ha⟩ := large_parameters lar
  let : NeZero N := ⟨by omega⟩
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have g := global N
  have ub := (theorem_6_1 N he lar g ha).1.mp (r g inferInstance ha)
  have sq := pow_le_pow_left₀ (norm_nonneg _) ub 2
  rw [spectralScale_sq N np (singularSeries_pos N).le logp.le] at sq
  have high := up g
  rw [eligibleNorm_spec N ha g] at high
  have b := mul_le_mul_of_nonneg_left sq np.le
  have eqn : (N:ℝ)*(singularSeries N/N*Real.log N^3)=singularSeries N*Real.log N^3 := by field_simp
  rw [eqn,original_series] at b
  have lim := mul_le_mul_of_nonneg_right small (pow_nonneg logp.le 3)
  nlinarith only [high,b,lim]

/-- Pointwise squared norm inequality, in the normalization of the spectral product. -/
theorem squared_bound_of_exclusion {N : ℕ} [NeZero N] (j : ℕ) (he : Even N)
    (lar : Real.exp 10<(N:ℝ)) (g : GRH N) (ha : alpha N<beta) (lg : 2≤Real.log N)
    (sub : SpectralZeroFree N (alpha N) ha (logWidth j N)) :
    Sbound (deltaSq N (singular N)) (eligibleNorm N) (logWidth j N) := by
  have np : 0<(N:ℝ) := by exact_mod_cast (NeZero.pos N)
  have logp : 0<Real.log N := by linarith
  have lp : 1≤Real.log N^j := one_le_pow₀ (by linarith)
  have wp : 0<logWidth j N := by unfold logWidth; positivity
  have narrow : logWidth j N<1/2 := by unfold logWidth; rw [div_lt_iff₀ (by positivity)]; linarith
  have norm := ((theorem_6_1 N he lar g ha).2.1 _ wp narrow).mp sub
  have one : 0<1-logWidth j N := by linarith
  have denom : 0<2*Real.sqrt (logWidth j N*(1-logWidth j N)) := by positivity
  have m := (le_div_iff₀ denom).mp norm
  have root : 0≤logWidth j N*(1-logWidth j N) := mul_nonneg wp.le (by linarith)
  have sq := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) denom.le) m 2
  simp only [mul_pow,Real.sq_sqrt root] at sq
  rw [spectralScale_sq N np (singularSeries_pos N).le logp.le,original_series] at sq
  unfold Sbound deltaSq
  rw [eligibleNorm_spec N ha g]
  apply le_trans _ (sq.trans_eq ?_)
  · ring_nf
    rfl
  · field_simp

/-- An eventual exclusion width of at least 1/(4 log^j N) would forbid
the cofinal growth of the original operator. The prescribed h is explicit. -/
theorem actual_S_failure_of_growth (global : ∀ N, GRH N) (growth : LiuInput eligibleNorm GRH)
    (h : ℕ → ℝ) (j : ℕ) (strip : EvenEventually (fun N => logWidth j N≤zeroFreeWidth N h)) :
    ¬HypothesisS h := by
  intro S
  obtain ⟨L,cap⟩ := eventually_atTop.mp eventually_small_series
  obtain ⟨K,claim⟩ := S.2.and (strip.and evenEventually_large)
  obtain ⟨N,hn,he,up⟩ := growth (j+6) (max (max K L) 2)
  obtain ⟨s,wide,lar⟩ := claim N (by omega) he
  obtain ⟨lg,small⟩ := cap N (by omega)
  obtain ⟨four,logp,ha⟩ := large_parameters lar
  let : NeZero N := ⟨by omega⟩
  have g := global N
  have sub : SpectralZeroFree N (alpha N) ha (logWidth j N) := by
    intro x hx
    exact s g inferInstance ha x (by linarith)
  have lower := up g
  have bad := logWidth_fails (a := j) (by omega : 0<N) lg small lower
  exact bad (squared_bound_of_exclusion j he lar g ha lg sub)

#print axioms actual_R_failure_of_growth
#print axioms actual_S_failure_of_growth
end GoldbachSpectral435

