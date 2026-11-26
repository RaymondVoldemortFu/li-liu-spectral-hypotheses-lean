module
public import ConditionalGoldbach.Proofs.SpectralModelOperator
public import ConditionalGoldbach.Proofs.SpectralModelGrowth

/-! Decay of the model after retaining its full conductor scaling. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace GoldbachSpectral435.ModelDecay

private lemma local_domination (N p : ℕ) (w : ℂ) :
    ‖1+densityEulerTerm N p w‖ ≤ ‖1+densityEulerTerm 1 p (w.re:ℂ)‖ := by
  by_cases hp : p.Prime ∧ 2<p
  · have pos : (0:ℝ)<p := by exact_mod_cast hp.1.pos
    have den : 0<(p:ℝ)-2 := sub_pos.mpr (by exact_mod_cast hp.2)
    have no : ¬p∣1 := hp.1.not_dvd_one
    have realval : densityEulerTerm 1 p (w.re:ℂ) = ((((p:ℝ)^(-w.re))/((p:ℝ)-2):ℝ):ℂ) := by
      simp only [densityEulerTerm,hp.1,hp.2,no,not_false_eq_true,and_self,ite_true]
      push_cast
      rw [← Complex.ofReal_neg,← Complex.ofReal_natCast,← Complex.ofReal_cpow pos.le]
    have nn : 0≤(p:ℝ)^(-w.re)/((p:ℝ)-2) := by positivity
    rw [realval,← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    by_cases dv : p∣N
    · simp [densityEulerTerm,dv,nn]
    · apply (norm_add_le _ _).trans
      simp only [Complex.ofReal_one,norm_one,densityEulerTerm,hp.1,hp.2,dv,not_false_eq_true,and_self,ite_true,
        norm_div,Complex.norm_natCast_cpow_of_pos hp.1.pos,neg_re]
      have eq : ‖(p:ℂ)-2‖=(p:ℝ)-2 := by
        rw [show (p:ℂ)-2=(((p:ℝ)-2:ℝ):ℂ) by push_cast; rfl,Complex.norm_real,Real.norm_eq_abs,abs_of_pos den]
      rw [eq]
  · have no (M : ℕ) : ¬(p.Prime ∧ 2<p ∧ ¬p∣M) := fun h => hp ⟨h.1,h.2.1⟩
    simp only [densityEulerTerm,ite_eq_right (no N),ite_eq_right (no 1),le_refl]

/-- Uniform domination by the positive Euler product at real part, with no
loss of the factor coming from the conductor. -/
theorem euler_domination (N : ℕ) {w : ℂ} (hw : 0<w.re) :
    ‖densityEulerProduct N w‖ ≤ ‖densityEulerProduct 1 (w.re:ℂ)‖ := by
  have prod (M : ℕ) (v : ℂ) (hv : 0<v.re) :
      HasProd (fun p => 1+densityEulerTerm M p v) (densityEulerProduct M v) := by
    rw [densityEulerProduct_eq_tprod]
    exact (multipliable_one_add_of_summable (densityEulerTerm_summable_norm M hv)).hasProd
  apply le_of_tendsto_of_tendsto' (prod N w hw).norm (prod 1 w.re hw).norm
  intro S
  simp only [norm_prod]
  apply Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
  exact fun p _ => local_domination N p w

private lemma density_bound (N : ℕ) {w : ℂ} (wp : 0<w.re) (wu : w.re≤1) :
    ‖densityEulerProduct N w‖ ≤ (6/singularSeries 1)/w.re := by
  have sp := singularSeries_pos 1
  have b := singularSeries_densityEuler_scaled_bound 1 (by decide) (w:=(w.re:ℂ)) wp
  simp only [Nat.cast_one,Complex.one_cpow,one_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos sp,Complex.ofReal_re] at b
  apply (euler_domination N wp).trans
  have d := b.trans (mul_le_mul_of_nonneg_left (riemannZeta_right_pole_bound _ wp wu) (by norm_num))
  apply (le_div_iff₀ wp).mpr
  apply (le_div_iff₀ sp).mpr
  have q := (le_div_iff₀ wp).mp (d.trans_eq (by ring : 2*(3/w.re)=6/w.re))
  linarith only [show ‖densityEulerProduct 1 (w.re:ℂ)‖ * w.re * singularSeries 1 =
    singularSeries 1 * ‖densityEulerProduct 1 (w.re:ℂ)‖ * w.re by ring,q]

/-- The kernel bound retains the full conductor power uniformly on both
closed boundary lines. -/
theorem kernel_decay :
    ∃ C : ℝ, 0<C ∧ ∀ {a : ℝ}, 0<a → ∀ N : ℕ, 0<N → ∀ s z : ℂ,
      s.re ∈ Icc a beta → z.re ∈ Icc a beta →
      ‖continuedModel N s (conj z)‖ ≤
        (C*singularSeries N*(N:ℝ)^(-2*a)*(a⁻¹)^2)*
        (1+|s.im|)^(1/4:ℝ)*(1+|z.im|)^(1/4:ℝ) := by
  obtain ⟨G,gp,gamma⟩ := gammaQuotient_uniform_nonnegative beta (by norm_num [beta]) (by norm_num [beta])
  have sp := singularSeries_pos 1
  refine ⟨48*Real.pi*G^2/singularSeries 1,by positivity,?_⟩
  intro a ap N np s z hs hz
  let w := s+conj z
  let v := 1-s-conj z
  have wr : w.re=s.re+z.re := by simp [w]
  have vr : v.re=1-w.re := by simp [v,wr]; ring
  have vi : v.im = -(s.im-z.im) := by simp [v]; ring
  have lo : 2*a≤w.re := by linarith [hs.1,hz.1,wr]
  have hi : w.re≤1/4 := by dsimp [beta] at hs hz; linarith [hs.2,hz.2,wr]
  have wp : 0<w.re := by linarith
  have wa : a≤w.re := by linarith
  have nu : (1:ℝ)≤N := by exact_mod_cast np
  have scale : ‖(N:ℂ)^(-w)‖ ≤ (N:ℝ)^(-2*a) := by
    rw [Complex.norm_natCast_cpow_of_pos np,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le nu (by linarith)
  have dd : ‖densityEulerProduct N w‖ ≤ (6/singularSeries 1)/a :=
    (density_bound N wp (by linarith)).trans (div_le_div_of_nonneg_left (by positivity) ap wa)
  have pi : Real.pi^w.re ≤ Real.pi := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three] : 1≤Real.pi)
      (by linarith : w.re≤1)
  have zeta : ‖riemannZeta v‖ ≤ (8/a)*((1+|s.im|)^(1/4:ℝ)*(1+|z.im|)^(1/4:ℝ)) := by
    apply (riemannZeta_left_pole_bound (by linarith : 3/4≤v.re) (by linarith : v.re<1)).trans
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · apply div_le_div_of_nonneg_left (by norm_num) ap (by linarith)
    · rw [← Real.mul_rpow (by positivity) (by positivity),vi,abs_neg]
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      nlinarith [abs_sub s.im z.im,mul_nonneg (abs_nonneg s.im) (abs_nonneg z.im)]
  have gs := gamma s ⟨ap.le.trans hs.1,hs.2⟩
  have gz := gamma (conj z) ⟨by simpa using ap.le.trans hz.1,by simpa using hz.2⟩
  have sn := singularSeries_pos N
  rw [continuedModel_norm_split N np,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos sn]
  change Real.pi^w.re*(‖(N:ℂ)^(-w)‖*singularSeries N*‖densityEulerProduct N w‖)*
    ‖riemannZeta v‖*‖gammaQuotient s‖*‖gammaQuotient (conj z)‖ ≤ _
  calc
    _ ≤ Real.pi*((N:ℝ)^(-2*a)*singularSeries N*((6/singularSeries 1)/a))*
          ((8/a)*((1+|s.im|)^(1/4:ℝ)*(1+|z.im|)^(1/4:ℝ)))*G*G := by gcongr
    _ = _ := by simp only [div_eq_mul_inv]; ring

/-- Uniform Hilbert--Schmidt estimate for the original model on a
variable strip, normalized by the original singular series. -/
theorem operator_decay :
    ∃ C : ℝ, 0<C ∧ ∀ {a : ℝ}, 0<a → ∀ (ha : a<beta) (N : ℕ) [NeZero N],
      hsNorm (modelOperator ha N) ≤ C*singularSeries N*(N:ℝ)^(-2*a)*(a⁻¹)^2 := by
  obtain ⟨B,bp,kernel⟩ := kernel_decay
  let J : ℝ := ∫ t : ℝ, (1+|t|)^(-(3/2:ℝ))
  refine ⟨8*B*(|J|+1),by positivity,?_⟩
  intro a ap ha N inst
  let Q := B*singularSeries N*(N:ℝ)^(-2*a)*(a⁻¹)^2
  have sp := singularSeries_pos N
  have qp : 0≤Q := by dsimp [Q]; positivity
  have cap := kernel ap N (NeZero.pos N)
  obtain ⟨hk,hc⟩ := weightedAnalyticKernel_inputs_at ap ha (continuedModel N)
    (continuedModel_differentiableOn N (NeZero.pos N)) Q qp cap
  have herm : HermitianKernel (weightedAnalyticKernel (continuedModel N)) := by
    apply weightedAnalyticKernel_hermitian
    intro s z
    rw [continuedModel_conj,Complex.conj_conj,continuedModel_symmetric]
  obtain ⟨_,_,_,_,_,_,eq,_⟩ := kernelOperator_spec_of_hardyColumns ha N _ herm hk hc
  have energy := boundaryKernelSquareIntegral_power_bound ha _ hk (16*Q^2) (by positivity)
    (weightedAnalyticKernel_power_bound ap.le (continuedModel N) Q qp cap)
  change hsNorm (modelOperator ha N)^2=_ at eq
  rw [← eq] at energy
  apply (sq_le_sq₀ (hsNorm_nonneg _) (by positivity)).mp
  have inc : J^2≤(|J|+1)^2 := by nlinarith [sq_abs J,abs_nonneg J]
  calc
    _ ≤ 4*(16*Q^2)*J^2 := energy
    _ ≤ 4*(16*Q^2)*(|J|+1)^2 := by gcongr
    _ = _ := by dsimp [Q]; ring

#print axioms operator_decay
end GoldbachSpectral435.ModelDecay
