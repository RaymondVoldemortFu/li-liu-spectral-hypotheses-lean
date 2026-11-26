module
public import PerronApproximation
public import ConditionalGoldbach.Proofs.CharacterGramOperator
public import ConditionalGoldbach.Proofs.CharacterTraceBounds

/-! Approximation of the actual Hardy vectors on the moving strip by
functions whose numerators are finite Mangoldt polynomials. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex MeasureTheory Filter Set
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PerronApproximation

def cutoff (N m : ℕ) : ℝ := ((N:ℝ)^m)^2

def polynomialFunction {N : ℕ} (χ : Character N) (m : ℕ) (s : ℂ) : ℂ :=
  -smoothedDirichletPolynomial χ (cutoff N m) (1/2+s)/(1+s)

private theorem poly_entire {N : ℕ} (χ : Character N) (X : ℝ) :
    Differentiable ℂ (fun s : ℂ => smoothedDirichletPolynomial χ X (1/2+s)) := by
  unfold smoothedDirichletPolynomial
  apply Differentiable.fun_sum
  intro n _
  by_cases hz : n=0
  · subst n
    simp [mangoldt]
  · have dc : Differentiable ℂ (fun s : ℂ => (n:ℂ)^(-(1/2+s))) :=
      ((differentiable_id.const_add (1/2:ℂ)).neg).const_cpow (Or.inl (by exact_mod_cast hz))
    exact (dc.const_mul _).mul_const _

private def height (t : ℝ) : ℝ :=
  2*((1+t^2)⁻¹ + Real.log (|t|+2)^2/(1+t^2))

private lemma height_int : Integrable height :=
  (integrable_inv_one_add_sq.add logarithmic_height_square_integrable).const_mul 2

private lemma height_pos (t : ℝ) : 0≤height t := by unfold height; positivity

private theorem hardy_majorant : ∃ V : ℝ, 0<V ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    Real.exp 10<(N:ℝ) → GRH N → ∀ χ ∈ oddCharacters N, ∀ (m : ℕ) (k : ℝ), 0<k →
    (∀ x ∈ Icc (alpha N) beta, ∀ t : ℝ,
      ‖-logDerivative χ (line x t)-smoothedDirichletPolynomial χ (cutoff N m) (1/2+line x t)‖ ≤
      k*(1+Real.log (|t|+2))) →
    ∃ e : HardySpace (alpha N) beta,
      (∀ s ∈ strip (alpha N) beta, fourierLaplace e s =
        characterHardyFunction χ s - polynomialFunction χ m s) ∧ ‖e‖≤k*V := by
  let V := 1+2*∫ t, height t
  have hv : 0<V := by
    have i : 0 ≤ ∫ t, height t := integral_nonneg (fun t => height_pos t)
    dsimp [V]; linarith
  refine ⟨Real.sqrt V,Real.sqrt_pos.mpr hv,?_⟩
  intro N inst big g χ hc m k kp uniform
  have ha := (large_parameters big).2.2
  have ap := large_alpha_pos big
  let E := fun s => characterHardyFunction χ s - polynomialFunction χ m s
  have diff (s : ℂ) (hs : s.re ∈ Icc (alpha N) beta) : DifferentiableAt ℂ E s := by
    have nz : 1+s≠0 := by
      intro h
      have re := congrArg Complex.re h
      simp only [add_re,one_re,zero_re] at re
      linarith [hs.1]
    exact (characterHardyFunction_differentiableAt g χ hc (ap.trans_le hs.1)).sub
      (((poly_entire χ (cutoff N m) s).neg).div (by fun_prop) nz)
  have integ : Integrable (fun t => k^2*height t) := height_int.const_mul _
  have bound (x : ℝ) (hx : x ∈ Icc (alpha N) beta) (t : ℝ) : ‖E (line x t)‖^2 ≤ k^2*height t := by
    let H := Real.log (|t|+2)
    have hh : 0≤H := Real.log_nonneg (by linarith [abs_nonneg t])
    have x0 : 0<x := ap.trans_le hx.1
    have eqv : E (line x t) =
        -(-logDerivative χ (line x t)-smoothedDirichletPolynomial χ (cutoff N m) (1/2+line x t))/(1+line x t) := by
      dsimp only [E,characterHardyFunction,polynomialFunction]
      ring
    rw [eqv,norm_div,norm_neg,div_pow,norm_one_add_line_sq]
    have c : ‖-logDerivative χ (line x t)-smoothedDirichletPolynomial χ (cutoff N m) (1/2+line x t)‖ ≤ k*(1+H) :=
      uniform x hx t
    have den : 1+t^2 ≤ (1+x)^2+t^2 := by nlinarith [sq_nonneg x]
    apply (div_le_div₀ (by positivity : 0≤(k*(1+H))^2) (pow_le_pow_left₀ (norm_nonneg _) c 2) (by positivity : 0<1+t^2) den).trans
    have num : (1+H)^2 ≤ 2*(1+H^2) := by nlinarith [sq_nonneg (1-H)]
    unfold height
    calc
      _ ≤ (k^2*(2*(1+H^2)))/(1+t^2) := by rw [mul_pow]; gcongr
      _ = _ := by dsimp [H]; ring
  obtain ⟨e,rep,left,right⟩ := hardy_column_of_closedStrip_majorant ha
    (fun s hs => (diff s ⟨hs.1.le,hs.2.le⟩).differentiableWithinAt)
    (fun s hs => (diff s hs).continuousAt.continuousWithinAt) integ bound
  refine ⟨e,rep,?_⟩
  have energy (x : ℝ) (hx : x ∈ Icc (alpha N) beta) :
      (∫ t, ‖E (line x t)‖^2) ≤ k^2*(∫ t, height t) := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) integ (Eventually.of_forall (bound x hx))
  have bd : ‖e‖^2 ≤ k^2*V := by
    rw [boundaryTraces_norm_sq ha e,l2_norm_sq_integral,l2_norm_sq_integral]
    have el : (∫ t, ‖(boundaryTraces ha e).1 t‖^2) = ∫ t, ‖E (line (alpha N) t)‖^2 :=
      integral_congr_ae (left.fun_comp (fun z : ℂ => ‖z‖^2))
    have er : (∫ t, ‖(boundaryTraces ha e).2 t‖^2) = ∫ t, ‖E (line beta t)‖^2 :=
      integral_congr_ae (right.fun_comp (fun z : ℂ => ‖z‖^2))
    rw [el,er]
    dsimp only [V]
    nlinarith only [energy _ ⟨le_rfl,ha.le⟩,energy _ ⟨ha.le,le_rfl⟩,sq_nonneg k]
  have b := (sq_le_sq₀ (norm_nonneg e) (show 0≤k*Real.sqrt V by positivity)).mp
    (bd.trans_eq (by rw [mul_pow,Real.sq_sqrt hv.le]))
  exact b

/-- The strip Hardy norm of each individual character error decays with an
absolute constant independent of the level, the character and the exponent. -/
theorem hardy_error : ∃ D : ℝ, 0<D ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    Real.exp 10 < (N:ℝ) → GRH N → ∀ χ ∈ oddCharacters N, ∀ m : ℕ,
    1≤m → 100*Real.log (Real.log N) ≤ m →
    ∃ e : HardySpace (alpha N) beta,
      (∀ s ∈ strip (alpha N) beta, fourierLaplace e s =
        characterHardyFunction χ s - polynomialFunction χ m s) ∧
      ‖e‖ ≤ D/(Real.log N)^18 := by
  obtain ⟨C,hC,U⟩ := logarithmic_accuracy
  obtain ⟨V,vp,H⟩ := hardy_majorant
  refine ⟨C*V,by positivity,?_⟩
  intro N inst big g χ hc m hm hcut
  have hn : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have L1 : 1≤Real.log N := by linarith [(Real.lt_log_iff_exp_lt hn).mpr big]
  let k := C/(Real.log N)^18
  have kp : 0<k := div_pos hC (pow_pos (by linarith) _)
  obtain ⟨e,rep,cap⟩ := H N inst big g χ hc m k kp (fun x hx t =>
    (U N inst L1 g χ hc x t m hm hcut (by simpa [alpha,one_div] using hx.1)
      (hx.2.trans (by norm_num [beta]))).trans_eq (by dsimp [k]; ring))
  exact ⟨e,rep,cap.trans_eq (by dsimp [k]; ring)⟩

/-- For fixed modulus the actual Hardy column is the norm limit of the
smoothed polynomials. The convergence is geometric in the cutoff exponent. -/
theorem hardy_geometric : ∃ D : ℝ, 0<D ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    Real.exp 10<(N:ℝ) → GRH N → ∀ χ ∈ oddCharacters N, ∀ m : ℕ, 1≤m →
    ∃ e : HardySpace (alpha N) beta,
      (∀ s ∈ strip (alpha N) beta, fourierLaplace e s =
        characterHardyFunction χ s - polynomialFunction χ m s) ∧
      ‖e‖≤D*(Real.log N)^2*(4/5:ℝ)^m := by
  obtain ⟨C,cp,U⟩ := conductor_power_error
  obtain ⟨V,vp,H⟩ := hardy_majorant
  refine ⟨(2*C+8)*V,by positivity,?_⟩
  intro N inst big g χ hc m hm
  let L := Real.log (N:ℝ)
  let r := (4/5:ℝ)^m
  have hn : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have one : 1≤L := by dsimp [L]; linarith [(Real.lt_log_iff_exp_lt hn).mpr big]
  have lp : 0<L := by linarith
  have rp : 0<r := by dsimp [r]; positivity
  let k := (2*C+8)*L^2*r
  have kp : 0<k := by dsimp [k]; positivity
  obtain ⟨e,rep,bound⟩ := H N inst big g χ hc m k kp (by
    intro x hx t
    let M := Real.log (|t|+2)
    have mp : 0≤M := Real.log_nonneg (by linarith [abs_nonneg t])
    have h := U N inst one g χ hc x t m hm (by simpa [alpha,one_div] using hx.1)
      (hx.2.trans (by norm_num [beta]))
    have logn : Real.log ((N:ℝ)*(|t|+2))=L+M := Real.log_mul hn.ne' (by positivity)
    rw [logn] at h
    apply h.trans
    have sq : L≤L^2 := by nlinarith only [mul_nonneg lp.le (sub_nonneg.mpr one)]
    have lh := mul_le_mul_of_nonneg_right sq mp
    have cn := mul_le_mul_of_nonneg_left lh cp.le
    have major : 2*C*L*(L+M)+4+4*L ≤ ((2*C+8)*L^2)*(1+M) := by
      nlinarith only [one,sq,cn,mul_nonneg (sq_nonneg L) mp]
    exact (mul_le_mul_of_nonneg_left major rp.le).trans_eq (by dsimp only [k,M]; ring))
  exact ⟨e,rep,bound.trans_eq (by dsimp only [k,r,L]; ring)⟩

#print axioms hardy_error
#print axioms hardy_geometric
end GoldbachSpectral435.PerronApproximation
