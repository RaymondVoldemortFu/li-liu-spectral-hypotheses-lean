module
public import OriginalBounds
public import ConditionalGoldbach.Proofs.PoleModel

/-! Correlations of odd Dirichlet logarithmic derivatives at consecutive powers
of a fixed even base, evaluated at the same point of the moving Hardy strip. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Set Complex
open scoped Topology ComplexConjugate
namespace GoldbachSpectral435.ConductorMoments

/-- The diagonal of the odd-character kernel, before the arithmetic subtractions. -/
def moment (N : ℕ) [NeZero N] (x t : ℝ) : ℂ :=
  characterKernel N (line x t) (conj (line x t))

theorem moment_eq_mean_square (N : ℕ) [NeZero N] (x t : ℝ) :
    moment N x t = 2 / (N.totient : ℂ) *
      ∑ χ ∈ oddCharacters N, ((‖logDerivative χ (line x t)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [moment, characterKernel, conj_conj, Complex.mul_conj, Complex.sq_norm]

theorem singular_power (b k : ℕ) :
    singularSeries (b^(k+1)) = singularSeries b := by
  simp only [original_series, GoldbachSpectral.singular, Nat.primeFactors_pow_succ]

private theorem density_power (b k : ℕ) (w : ℂ) :
    densityEulerProduct (b^(k+1)) w = densityEulerProduct b w := by
  unfold densityEulerProduct
  apply tprod_congr
  intro p
  by_cases hp : p.Prime
  · have h : p ∣ b^(k+1) ↔ p ∣ b := ⟨hp.dvd_of_dvd_pow, fun h => h.trans (dvd_pow_self b (Nat.succ_ne_zero k))⟩
    simp only [hp, h]
  · simp [hp]

theorem diagonal_power (b k : ℕ) (w : ℂ) :
    diagonalSeries (b^(k+1)) w = diagonalSeries b w := by
  simp only [diagonalSeries, Nat.coprime_pow_right_iff (Nat.succ_pos k)]

private lemma model_power (b k : ℕ) (hb : 1 < b) (x t : ℝ) :
    continuedModel (b^(k+1)) (line x t) (conj (line x t)) =
    (Real.exp (-2*x*(Real.log (b^(k+1):ℕ)-Real.log b)) : ℂ) *
      continuedModel b (line x t) (conj (line x t)) := by
  have hsum : line x t + conj (line x t) = 2*(x:ℂ) := by simp [line]; ring
  have bpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0<b)
  have npos : 0 < (((b^(k+1):ℕ):ℝ)) := by positivity
  have powR (n : ℕ) (hn : 0 < (n:ℝ)) :
      ((Real.pi:ℂ) / n)^(2*(x:ℂ)) = (Real.exp ((Real.log Real.pi - Real.log n)*(2*x)) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_ofNat (n := 2),
      ← Complex.ofReal_mul, ← Complex.ofReal_cpow (div_pos Real.pi_pos hn).le,
      Real.rpow_def_of_pos (div_pos Real.pi_pos hn), Real.log_div Real.pi_ne_zero hn.ne']
  unfold continuedModel
  rw [singular_power, density_power, hsum, powR _ npos, powR _ bpos]
  rw [show (Real.log Real.pi-Real.log (b^(k+1):ℕ))*(2*x) =
    -2*x*(Real.log (b^(k+1):ℕ)-Real.log b)+(Real.log Real.pi-Real.log b)*(2*x) by ring,
    Real.exp_add]
  push_cast
  ring

/-- A common height and a common real shift can be used at both moduli. -/
private theorem scaled_residual_bound (N : ℕ) [NeZero N] (he : Even N)
    (big : Real.exp 10 < (N:ℝ)) (g : GRH N) {x δ : ℝ} (hx : 0<x)
    (hsmall : x ≤ beta/2) (hd : 0<δ) (gap : δ*x ≤ x-alpha N) (t : ℝ) :
    ‖(x:ℂ)*residual N (line x t) (conj (line x t))‖ ≤
      ((4+t^2)/(8*δ)) * eligibleNorm N := by
  obtain ⟨_,_,ha⟩ := large_parameters big
  have hp := large_alpha_pos big
  have pos : 0 < x-alpha N := (mul_pos hd hx).trans_le gap
  have xb : x < beta := by unfold beta at *; linarith
  have hs : line x t ∈ strip (alpha N) beta := by simpa [strip,line] using And.intro (sub_pos.mp pos) xb
  have dist : pointDistance (alpha N) beta (line x t) = x-alpha N := by
    simp only [pointDistance,line,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,
      zero_mul,sub_zero,add_zero]
    rw [min_eq_left (by linarith)]
  have bound := residual_norm_le_of_kernel_pairing ha hp.le N (residualOperator ha N) _ _ hs hs
    (proposition_5_4_kernel_pairing N he big g ha _ _ hs hs)
  rw [dist,← sq, Real.sqrt_sq pos.le,← eligibleNorm_spec N ha g] at bound
  have squares : ‖1+line x t‖^2 = (1+x)^2+t^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,line,pow_two]
  have num : (1+x)^2+t^2 ≤ 4+t^2 := by
    have x1 : x ≤ 1 := by unfold beta at hsmall; linarith
    nlinarith only [mul_nonneg (sub_nonneg.mpr x1) (show 0 ≤ 3+x by linarith)]
  rw [mul_assoc,← sq,squares] at bound
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hx.le]
  have key := (le_div_iff₀ (mul_pos (by norm_num) pos)).mp bound
  have low := mul_le_mul_of_nonneg_left gap (norm_nonneg (residual N (line x t) (conj (line x t))))
  have top := mul_le_mul_of_nonneg_left num (eligibleNorm_nonneg N)
  rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity)]
  nlinarith only [key,low,top]

private theorem norm_vanishes (s : ∃ h, HypothesisS h) {n : ℕ → ℕ}
    (grow : Tendsto n atTop atTop) (even : ∀ k, Even (n k))
    (D : ℝ) (positive : 0 < D) (fixedSeries : ∀ k, singularSeries (n k)=D) :
    Tendsto (fun k => eligibleNorm (n k)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  obtain ⟨K,small⟩ := some_actual_S_iff.mp s (ε/(2*D)) (by positivity)
  filter_upwards [grow.eventually_ge_atTop K] with k hk
  have h := small (n k) hk (even k)
  change eligibleNorm (n k) ≤ ε/(2*D)*singularSeries (n k) at h
  rw [fixedSeries, show ε/(2*D)*D=ε/2 by field_simp] at h
  simpa [Real.dist_eq, abs_of_nonneg (eligibleNorm_nonneg _)] using h.trans_lt (half_lt_self ep)

theorem common_shift_error (s : ∃ h, HypothesisS h) {n : ℕ → ℕ}
    [∀ k, NeZero (n k)] (grow : Tendsto n atTop atTop) (even : ∀ k, Even (n k))
    (g : ∀ k, GRH (n k)) {D : ℝ} (dp : 0 < D) (fixedSeries : ∀ k, singularSeries (n k)=D)
    {x : ℕ → ℝ} (xp : ∀ k, 0<x k) (lim : Tendsto x atTop (𝓝 0))
    {δ : ℝ} (δp : 0<δ) (gap : ∀ k, δ*x k ≤ x k-alpha (n k)) (t : ℝ) :
    Tendsto (fun k => (x k:ℂ)*residual (n k) (line (x k) t) (conj (line (x k) t)))
      atTop (𝓝 0) := by
  have hB : Tendsto (fun k => ((4+t^2)/(8*δ))*eligibleNorm (n k)) atTop (𝓝 0) := by
    simpa using (norm_vanishes s grow even D dp fixedSeries).const_mul ((4+t^2)/(8*δ))
  apply squeeze_zero_norm' _ hB
  obtain ⟨K, large⟩ := evenEventually_large
  filter_upwards [grow.eventually_ge_atTop K, lim.eventually_le_const
    (show (0:ℝ)<beta/2 by norm_num [beta])] with k hk hs
  exact scaled_residual_bound (n k) (even k) (large _ hk (even k)) (g k)
    (xp k) hs δp (gap k) t

private abbrev level (b k : ℕ) := b^(k+1)

private theorem level_grows {b : ℕ} (hb : 1 < b) :
    Tendsto (level b) atTop atTop := by
  exact (pow_right_strictMono₀ hb).tendsto_atTop.comp (tendsto_add_atTop_nat 1)

private theorem level_log {b : ℕ} (k : ℕ) (hb : 1<b) :
    Real.log (level b (k+1)) = Real.log (level b k) + Real.log b := by
  change Real.log ((b^((k+1)+1):ℕ):ℝ) = _
  rw [pow_succ,Nat.cast_mul,Real.log_mul (by positivity) (by exact_mod_cast (by omega : b ≠ 0))]

/-- The change in the continuous model between adjacent levels. The common
shift is measured with the lower level's logarithm. -/
theorem model_increment (b : ℕ) (hb : 1<b) (even : Even b) (c t : ℝ) (hc : 0<c) :
    let x := fun k => c / Real.log (b^(k+1):ℕ)
    Tendsto (fun k => (x k:ℂ) *
      (continuedModel (b^(k+2)) (line (x k) t) (conj (line (x k) t)) -
       continuedModel (b^(k+1)) (line (x k) t) (conj (line (x k) t)))) atTop
      (𝓝 ((Real.log b * Real.exp (-2*c) / 2 : ℝ) : ℂ)) := by
  intro x
  have lb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have lp (k : ℕ) : 0 < Real.log (level b k) :=
    Real.log_pos (by exact_mod_cast one_lt_pow₀ hb (Nat.succ_ne_zero k))
  have xp (k : ℕ) : 0 < x k := div_pos hc (lp k)
  have logs := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ) |>.comp (level_grows hb))
  have lim : Tendsto x atTop (𝓝 0) := tendsto_const_nhds.div_atTop logs
  have right : Tendsto x atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨lim,Eventually.of_forall xp⟩
  have pole := (continuedModel_double_pole b even (by omega) t).comp right
  have hd : HasDerivAt (fun u : ℝ => Real.exp ((2*Real.log b)*u)) (2*Real.log b) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul (2*Real.log b)).exp)
  have slopes := hd.tendsto_slope_zero_right.comp right
  have hsl : Tendsto (fun k => (1-Real.exp (2*Real.log b*x k))/x k) atTop
      (𝓝 (-(2*Real.log b))) := by
    convert slopes.neg using 1
    funext k
    simp [div_eq_inv_mul, sub_eq_add_neg, add_comm]
    ring
  have total := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hsl).mul_const
      (Real.exp (-2*c) : ℂ)).mul pole
  convert total using 1
  · funext k
    have prod : x k * Real.log (level b k) = c := div_mul_cancel₀ c (lp k).ne'
    have lower : -2*x k*(Real.log (level b k)-Real.log b) = -2*c + 2*Real.log b*x k := by
      linear_combination -2*prod
    have upper : -2*x k*(Real.log (level b (k+1))-Real.log b) = -2*c := by
      rw [level_log k hb,add_sub_cancel_right]
      linear_combination -2*prod
    rw [model_power b (k+1) hb,model_power b k hb,upper,lower,Real.exp_add]
    dsimp only [Function.comp_def]
    push_cast
    field_simp [show (x k:ℂ) ≠ 0 by exact_mod_cast (xp k).ne']
  · push_cast
    ring

/-- A necessary asymptotic for the original existential hypothesis. Both
moments use the same spectral argument, so the entire arithmetic diagonal
cancels. Each summand is an actual Dirichlet logarithmic derivative. -/
theorem moment_increment_of_exists_S (s : ∃ h, HypothesisS h)
    (b : ℕ) [NeZero b] (hb : 1<b) (even : Even b) (grh : ∀ k, GRH (b^(k+1)))
    (c t : ℝ) (hc : 1<c) :
    let x := fun k => c / Real.log (b^(k+1):ℕ)
    Tendsto (fun k => (x k:ℂ)*(moment (b^(k+2)) (x k) t - moment (b^(k+1)) (x k) t))
      atTop (𝓝 ((Real.log b * Real.exp (-2*c) / 2 : ℝ) : ℂ)) := by
  intro x
  have lp (k : ℕ) : 0 < Real.log (level b k) :=
    Real.log_pos (by exact_mod_cast one_lt_pow₀ hb (Nat.succ_ne_zero k))
  have cp : 0<c := by linarith
  have xp (k : ℕ) : 0 < x k := div_pos cp (lp k)
  have inc := level_grows hb
  have logs := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ) |>.comp inc)
  have lim : Tendsto x atTop (𝓝 0) := tendsto_const_nhds.div_atTop logs
  let δ := (c-1)/c
  have dp : 0 < δ := div_pos (by linarith) cp
  have gap (k : ℕ) : δ*x k = x k-alpha (level b k) := by
    change ((c-1)/c)*(c/Real.log (level b k)) = c/Real.log (level b k)-1/Real.log (level b k)
    field_simp
  have gap' (k : ℕ) : δ*x k ≤ x k - alpha (level b (k+1)) := by
    rw [gap]
    apply sub_le_sub_left
    unfold alpha
    apply one_div_le_one_div_of_le (lp k)
    rw [level_log k hb]
    linarith [Real.log_pos (show (1:ℝ)<b by exact_mod_cast hb)]
  have ev (k : ℕ) : Even (level b k) := even.pow_of_ne_zero (Nat.succ_ne_zero k)
  have lo := common_shift_error s inc ev grh (singularSeries_pos b)
    (singular_power b) xp lim dp (fun k => (gap k).le) t
  have hi := common_shift_error s (n := fun k => level b (k+1)) (inc.comp (tendsto_add_atTop_nat 1))
    (fun k => ev (k+1)) (fun k => grh (k+1)) (singularSeries_pos b)
    (fun k => singular_power b (k+1)) xp lim dp gap' t
  have model := model_increment b hb even c t cp
  have tot := (hi.sub lo).add model
  simp only [sub_self,zero_add] at tot
  apply tot.congr'
  apply Eventually.of_forall
  intro k
  change (x k:ℂ)*residual (level b (k+1)) _ _ - (x k:ℂ)*residual (level b k) _ _ + _ = _
  unfold ConditionalGoldbach.residual moment
  rw [diagonal_power b (k+1),diagonal_power b k]
  ring

#print axioms moment_increment_of_exists_S

end GoldbachSpectral435.ConductorMoments
