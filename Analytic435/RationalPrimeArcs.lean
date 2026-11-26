module
public import ModulatedPrimeTwist
public import PrimitiveAdditiveMean
public import PrimeLineSifting
public import Mathlib.Analysis.Normed.Ring.Finite

/-! An explicit major-arc approximation for the genuine Mangoldt
exponential sum near every reduced rational. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open ConditionalGoldbach Finset Filter Complex
namespace GoldbachSpectral435.CriticalCharacter
open GoldbachSieve

private def unitsOnly {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ) (a : ZMod q) : ℂ :=
  if IsUnit a then ψ a else 0

private lemma excluded_arc (q M : ℕ) [NeZero q] (ψ : AddChar (ZMod q) ℂ)
    (w : ℝ→ℝ) (F : ℝ) (hb : ∀ u, |w u|≤F) :
    ‖residueSum q M w ψ-residueSum q M w (unitsOnly ψ)‖≤F*((Nat.log 2 M:ℝ)*Real.log q) := by
  classical
  have fp := (abs_nonneg _).trans (hb 0)
  rw [residueSum,residueSum,← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n∈range M,F*excludedMass q n := by
      apply sum_le_sum
      intro n _
      by_cases cp : n.Coprime q
      · have iu := (ZMod.isUnit_iff_coprime n q).mpr cp
        simp only [unitsOnly,ite_eq_left iu,sub_self,norm_zero,excludedMass,ite_eq_left cp,mul_zero,le_refl]
      · have nu := mt (ZMod.isUnit_iff_coprime n q).mp cp
        simp only [unitsOnly,ite_eq_right nu,mul_zero,sub_zero,norm_mul,AddChar.norm_apply,mul_one,
          Complex.norm_real,Real.norm_eq_abs,weightedMangoldt,excludedMass,ite_eq_right cp,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact (mul_le_mul_of_nonneg_left (hb _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq (mul_comm ..)
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (excluded_mass_bound q M (NeZero.pos q)) fp

private lemma unitMean_unitsOnly (q : ℕ) [NeZero q] (ψ : AddChar (ZMod q) ℂ) :
    unitMean q (unitsOnly ψ)=unitMean q ψ := by
  unfold unitMean
  congr 1
  exact sum_congr rfl fun a ha => ite_eq_left (mem_unitClasses.mp ha)

def arcSum {q : ℕ} (M : ℕ) (f : ℝ→ℝ) (ψ : AddChar (ZMod q) ℂ) (t : ℝ) :=
  ∑ n∈range M,(weightedMangoldt M n f:ℂ)*ψ n*Complex.exp ((t*(n/(M:ℝ)):ℝ)*I)

def principalArc (q M : ℕ) (f : ℝ→ℝ) (t : ℝ) := (principalMass q M (cosTest t f):ℂ)+
  I*(principalMass q M (sinTest t f):ℂ)

private lemma expand_arc {q M : ℕ} (f : ℝ→ℝ) (ψ : AddChar (ZMod q) ℂ) (t : ℝ) :
    arcSum M f ψ t=residueSum q M (cosTest t f) ψ+I*residueSum q M (sinTest t f) ψ := by
  unfold arcSum residueSum
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  have e (u : ℝ) : Complex.exp ((u:ℂ)*I)=(Real.cos u:ℂ)+(Real.sin u:ℂ)*I := by
    rw [Complex.exp_mul_I,Complex.ofReal_cos,Complex.ofReal_sin]
  rw [e]
  simp only [weightedMangoldt,cosTest,sinTest,Complex.ofReal_mul]
  ring

/-- The principal term for any additive character is its mean on the units. -/
theorem additive_arc_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C F : ℝ, 0<C ∧ 0≤F ∧ ∀ᶠ M : ℕ in atTop, ∀ (q : ℕ) [NeZero q], 4≤q → q≤M → GRH q →
      ∀ (ψ : AddChar (ZMod q) ℂ), ∀ t : ℝ,
      ‖arcSum M f ψ t-unitMean q ψ*principalArc q M f t‖≤
        Real.sqrt q*(C*(1+|t|)^4*Real.sqrt M*(6+Real.log q))+F*(Nat.log 2 M:ℝ)*Real.log q := by
  obtain ⟨C,cp,all⟩ := modulated_residue_bound f hf
  obtain ⟨F,fb⟩ := hf.norm_bounded
  have cap (u : ℝ) : |f u|≤F := by simpa only [Complex.norm_real,Real.norm_eq_abs] using fb u
  have fp := (abs_nonneg _).trans (cap 0)
  refine ⟨2*C,2*F,by positivity,by positivity,?_⟩
  filter_upwards [all] with M est
  intro q inst q4 qm grh ψ t
  let a := unitMean q ψ
  let P := fun b => (principalMass q M (trigTest b t f):ℂ)
  let S := fun b => residueSum q M (trigTest b t f) ψ
  let W := Real.sqrt q*(C*(1+|t|)^4*Real.sqrt M*(6+Real.log q))
  let V := F*((Nat.log 2 M:ℝ)*Real.log q)
  have bound (b : Bool) : ‖S b-a*P b‖≤V+W := by
    let w := trigTest b t f
    have wb (u : ℝ) : |w u|≤F := by
      cases b <;> simp only [w,trigTest,Bool.false_eq_true,ite_false,ite_true,cosTest,sinTest,abs_mul]
      · exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans (cap _)
      · exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans (cap _)
    have exc := excluded_arc q M ψ w F wb
    have uni (x : ZMod q) : ‖unitsOnly ψ x‖≤1 := by
      unfold unitsOnly
      split <;> simp
    have zero (x : ZMod q) (nu : ¬IsUnit x) : unitsOnly ψ x=0 := ite_eq_right nu
    have core := est q q4 qm grh b t (unitsOnly ψ) zero uni
    change ‖residueSum q M w (unitsOnly ψ)-(principalMass q M w:ℂ)*unitMean q (unitsOnly ψ)‖≤W at core
    rw [unitMean_unitsOnly q ψ,mul_comm (principalMass q M w:ℂ)] at core
    have tri := dist_triangle (S b) (residueSum q M w (unitsOnly ψ)) (a*P b)
    simp only [dist_eq_norm] at tri
    exact tri.trans (add_le_add exc core)
  have eq : arcSum M f ψ t-a*principalArc q M f t=(S false-a*P false)+I*(S true-a*P true) := by
    rw [expand_arc,principalArc]
    change _=(residueSum q M (cosTest t f) ψ-a*(principalMass q M (cosTest t f):ℂ))+
      I*(residueSum q M (sinTest t f) ψ-a*(principalMass q M (sinTest t f):ℂ))
    ring
  rw [eq]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_I,one_mul]
  exact (add_le_add (bound false) (bound true)).trans_eq (by dsimp only [V,W]; ring)

/-- For ψ(n)=exp(2πian/q) with (a,q)=1 the main coefficient is μ(q)/φ(q).
The two phases are kept together in the original complex exponential sum. -/
theorem rational_arc_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C F : ℝ, 0<C ∧ 0≤F ∧ ∀ᶠ M : ℕ in atTop, ∀ (q : ℕ) [NeZero q], 4≤q → q≤M → GRH q →
      ∀ (ψ : AddChar (ZMod q) ℂ), Function.Injective ψ → ∀ t : ℝ,
      ‖arcSum M f ψ t-(ArithmeticFunction.moebius q:ℂ)/q.totient*principalArc q M f t‖≤
        Real.sqrt q*(C*(1+|t|)^4*Real.sqrt M*(6+Real.log q))+F*(Nat.log 2 M:ℝ)*Real.log q := by
  obtain ⟨C,F,cp,fp,est⟩ := additive_arc_bound f hf
  refine ⟨C,F,cp,fp,?_⟩
  filter_upwards [est] with M bound
  intro q inst q4 qm grh ψ inj t
  have m : unitMean q ψ=(ArithmeticFunction.moebius q:ℂ)/q.totient := by
    rw [unitMean,primitive_additive_mean q ψ inj]
  simpa only [m] using bound q q4 qm grh ψ t

#print axioms rational_arc_bound
end GoldbachSpectral435.CriticalCharacter
