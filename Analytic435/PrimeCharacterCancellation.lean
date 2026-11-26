module
public import CriticalCharacterBound
public import PhysicalAP

/-! Square-root cancellation, up to logarithms, in genuine smooth
prime sums for every nonprincipal character at every conductor up to M. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex Set MeasureTheory Finset
namespace GoldbachSpectral435.CriticalCharacter

def primeTwist {q : ℕ} (χ : Character q) (M : ℕ) (f : ℝ→ℝ) : ℂ :=
  ∑ n∈range M,(weightedMangoldt M n f:ℂ)*χ n

private lemma finite_twist {q : ℕ} (χ : Character q) (M : ℕ) (mp : 0<M)
    (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    primeTwist χ M f=(Real.sqrt M:ℂ)*characterSample χ M (companion f) := by
  rw [finite_character_sample χ M mp f hf,mul_sum]
  apply sum_congr rfl
  intro n _
  have root : (Real.sqrt M:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr mp)).ne'
  unfold sampleValue weightedMangoldt
  push_cast
  field_simp

theorem prime_twist_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ (q M : ℕ) [NeZero q], 4≤q → q≤M → GRH q →
      ∀ χ : Character q, χ≠1 →
      ‖primeTwist χ M f‖≤C*Real.sqrt M*(Real.log M)^2*(6+Real.log q) := by
  obtain ⟨B,bp,dec⟩ := mellin_axis f hf
  let W := fun t : ℝ => (1+|t|)⁻¹^2
  have wi : Integrable W := by
    have h := integrable_one_add_norm (E:=ℝ) (μ:=volume) (r:=2) (by simp)
    convert h using 1
    ext t
    simp [W,Real.norm_eq_abs,Real.rpow_neg (by positivity : 0≤1+|t|)]
  let c := ‖(2*(Real.pi:ℂ))⁻¹‖
  let K := Real.exp 1*B*80
  let U := ∫ t,W t
  have up : 0≤U := integral_nonneg (fun t => sq_nonneg _)
  have cp : 0≤c := norm_nonneg _
  have kp : 0<K := by dsimp [K]; positivity
  refine ⟨1+c*K*U,by positivity,?_⟩
  intro q M inst q4 qm grh χ nc
  have mp : 0<M := by omega
  have mr : 0<(M:ℝ) := Nat.cast_pos.mpr mp
  have qr : (4:ℝ)≤q := by exact_mod_cast q4
  let L := Real.log (M:ℝ)
  let J := 6+Real.log (q:ℝ)
  let σ := 1/L
  have l1 : 1≤L := (Real.le_log_iff_exp_le mr).mpr (Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3≤M by omega)))
  have lp : 0<L := zero_lt_one.trans_le l1
  have jp : 0<J := by dsimp [J]; linarith [Real.log_nonneg (by linarith : (1:ℝ)≤q)]
  have sp : 0<σ := one_div_pos.mpr lp
  have s1 : σ≤1 := (div_le_one lp).mpr l1
  let F := fun s : ℂ => (M:ℂ)^s*mellin (fun u => (companion f u:ℂ)) s*logDerivative χ s
  obtain ⟨integ,inv⟩ := nonprincipal_sampling q4 grh χ nc M qm (companion f)
    ((FiniteModel.companion_contDiff hf).of_le (by norm_num)) (FiniteModel.companion_support_subset hf) σ sp s1
  change verticalMellin σ F= -characterSample χ M (companion f) at inv
  have bound (t : ℝ) : ‖F (line σ t)‖≤(K*L^2*J)*W t := by
    have d := dec (line σ t) (by simpa [line] using (show σ∈Icc (0:ℝ) 1 from ⟨sp.le,s1⟩))
    have ld := log_derivative q q4 grh χ nc σ t sp s1
    have r : (line σ t).re=σ := by simp [line]
    have i : (line σ t).im=t := by simp [line]
    rw [i] at d
    have e : (M:ℝ)^σ=Real.exp 1 := by
      rw [Real.rpow_def_of_pos mr]
      change Real.exp (L*(1/L))=_
      rw [mul_one_div_cancel lp.ne']
    rw [show F (line σ t)=_ from rfl,norm_mul,norm_mul,← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos mr,r,e]
    have z : 0<1+|t| := by positivity
    calc
      _ ≤ (Real.exp 1*(B*(1+|t|)⁻¹^4))*(80/σ^2*J*(1+|t|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left d (Real.exp_pos _).le) ld (norm_nonneg _) (by positivity)
      _ = (K*L^2*J)*((1+|t|)⁻¹^2*(1+|t|)⁻¹) := by dsimp only [K,σ]; field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_of_le_one_right (sq_nonneg _) (inv_le_one_of_one_le₀ (by linarith [abs_nonneg t]))
  have b := integral_mono integ.norm (wi.const_mul (K*L^2*J)) bound
  rw [integral_const_mul] at b
  have norm : ‖characterSample χ M (companion f)‖≤c*((K*L^2*J)*U) := by
    rw [← neg_neg (characterSample χ M (companion f)),← inv,norm_neg,verticalMellin,norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans b) cp
  rw [finite_twist χ M mp f hf,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left norm (Real.sqrt_nonneg _)).trans
  change Real.sqrt M*(c*(K*L^2*J*U))≤(1+c*K*U)*Real.sqrt M*L^2*J
  nlinarith only [mul_nonneg (mul_nonneg (Real.sqrt_nonneg (M:ℝ)) (sq_nonneg L)) jp.le]

#print axioms prime_twist_bound
end GoldbachSpectral435.CriticalCharacter
