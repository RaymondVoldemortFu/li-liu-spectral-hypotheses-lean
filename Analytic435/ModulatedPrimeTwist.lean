module
public import WaveMellinDecay
public import SharpPrimeTwist

/-! A uniform square-root character estimate for smooth additive
modulations, and its consequence for bounded functions of a residue. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open ConditionalGoldbach Finset Filter Complex
namespace GoldbachSpectral435.CriticalCharacter
open GoldbachSieve

def trigWeight {f : ℝ→ℝ} (hf : FiniteModelWeight f) (b : Bool) (t : ℝ) :
    FiniteModelWeight (trigTest b t f) := by
  cases b
  · exact cosWeight hf t
  · exact sinWeight hf t

/-- The same constant works at every real additive frequency. -/
theorem modulated_prime_twist (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ M : ℕ in atTop, ∀ (q : ℕ) [NeZero q], 4≤q → q≤M → GRH q →
      ∀ (b : Bool) (t : ℝ) (χ : Character q), χ≠1 →
      ‖primeTwist χ M (trigTest b t f)‖≤C*(1+|t|)^4*Real.sqrt M*(6+Real.log q) := by
  obtain ⟨A,ap,cap⟩ := modulated_mellin_axis f hf
  obtain ⟨C,cp,est⟩ := sharp_twist_from_mellin
  have growth := (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const hf.lower_pos
  refine ⟨C*A,mul_pos cp ap,?_⟩
  filter_upwards [growth.eventually_gt_atTop 1] with M large
  intro q inst q4 qm grh b t χ nc
  have lower : (trigWeight hf b t).lower=hf.lower := by cases b <;> rfl
  have e := est _ (trigWeight hf b t) (A*(1+|t|)^4) (by positivity) (cap b t) q M q4 qm grh
    (by rwa [lower]) χ nc
  exact e.trans_eq (by ring)

def residueSum (q M : ℕ) (f : ℝ→ℝ) (v : ZMod q→ℂ) :=
  ∑ n∈range M,(weightedMangoldt M n f:ℂ)*v n

def unitMean (q : ℕ) [NeZero q] (v : ZMod q→ℂ) := (∑ a∈unitClasses q,v a)/(q.totient:ℂ)

private lemma residue_by_class (q M : ℕ) [NeZero q] (f : ℝ→ℝ) (v : ZMod q→ℂ)
    (supported : ∀ a, ¬IsUnit a → v a=0) :
    residueSum q M f v=∑ a∈unitClasses q,(classMass q M a f:ℂ)*v a := by
  classical
  unfold residueSum classMass
  push_cast
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  have one (a : ZMod q) : ((if (n:ZMod q)=a then weightedMangoldt M n f else 0:ℝ):ℂ)*v a=
      if (n:ZMod q)=a then (weightedMangoldt M n f:ℂ)*v a else 0 := by
    by_cases eq : (n:ZMod q)=a
    · subst a; simp
    · simp [eq]
  simp_rw [one,sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [supported _ (mt mem_unitClasses.mpr h),mul_zero]

private lemma residue_error {q M : ℕ} [NeZero q] (w : ℝ→ℝ) (v : ZMod q→ℂ)
    (supported : ∀ a, ¬IsUnit a → v a=0) (bounded : ∀ a, ‖v a‖≤1) (B : ℝ) (bp : 0≤B)
    (variance : (∑ a∈unitClasses q,(classError M w a)^2)≤B^2) :
    ‖residueSum q M w v-(principalMass q M w:ℂ)*unitMean q v‖≤Real.sqrt q*B := by
  classical
  let E := unitClasses q
  have eq : residueSum q M w v-(principalMass q M w:ℂ)*unitMean q v=
      ∑ a∈E,(classError M w a:ℂ)*v a := by
    rw [residue_by_class _ _ _ _ supported,unitMean,mul_div_assoc',mul_sum,sum_div,← sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    simp only [classError,ofReal_sub,ofReal_div,ofReal_natCast,sub_mul]
    ring
  have card : (E.card:ℝ)≤q := by exact_mod_cast E.card_le_univ.trans_eq (ZMod.card q)
  rw [eq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a∈E,|classError M w a| := by
      apply sum_le_sum
      intro a _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (bounded a)
    _ ≤ Real.sqrt q*B := by
      have cs := Real.sum_mul_le_sqrt_mul_sqrt E (fun _ => (1:ℝ)) (fun a => |classError M w a|)
      simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,sq_abs] at cs
      exact cs.trans (mul_le_mul (Real.sqrt_le_sqrt card)
        ((Real.sqrt_le_sqrt variance).trans_eq (Real.sqrt_sq bp)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Bounded residue phases, including additive characters, may be chosen
after the summation length, the modulus and the physical frequency. -/
theorem modulated_residue_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ M : ℕ in atTop, ∀ (q : ℕ) [NeZero q], 4≤q → q≤M → GRH q →
      ∀ (b : Bool) (t : ℝ) (v : ZMod q→ℂ), (∀ a, ¬IsUnit a → v a=0) → (∀ a, ‖v a‖≤1) →
      let w := trigTest b t f
      ‖residueSum q M w v-(principalMass q M w:ℂ)*unitMean q v‖≤
        Real.sqrt q*(C*(1+|t|)^4*Real.sqrt M*(6+Real.log q)) := by
  obtain ⟨C,cp,all⟩ := modulated_prime_twist f hf
  refine ⟨C,cp,?_⟩
  filter_upwards [all] with M est
  intro q inst q4 qm grh b t v support bound w
  have lg : 0≤Real.log (q:ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr (by omega))
  exact residue_error w v support bound _ (by positivity)
    (variance_of_twists M w _ (est q q4 qm grh b t))

#print axioms modulated_prime_twist
#print axioms modulated_residue_bound
end GoldbachSpectral435.CriticalCharacter
