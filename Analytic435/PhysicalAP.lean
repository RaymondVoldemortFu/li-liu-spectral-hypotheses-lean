module
public import Progressions
public import Samples

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Set
namespace GoldbachSpectral435

def weightedMangoldt (M n : ℕ) (f : ℝ → ℝ) : ℝ := mangoldt n*f (n/(M:ℝ))
def classMass (q M : ℕ) (t : ZMod q) (f : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range M, if (n:ZMod q)=t then weightedMangoldt M n f else 0
def principalMass (q M : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range M, if n.Coprime q then weightedMangoldt M n f else 0

/-- Smoothed prime-number estimates on every invertible class. Both the
main term and the measured discrepancy are real finite arithmetic sums. -/
theorem physical_AP (f : ℝ → ℝ) (F : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, ∀ [NeZero q], 4≤q → GRH q →
      ∀ M : ℕ, 0<M → ∀ t : ZMod q, IsUnit t →
        |classMass q M t f-principalMass q M f/q.totient| ≤
          Real.sqrt M*(C*(M:ℝ)^(1/4:ℝ)*q^2) := by
  obtain ⟨C,hC,H⟩ := smooth_character_bound (companion f)
    ((FiniteModel.companion_contDiff F).of_le (by norm_num)) (FiniteModel.companion_support_subset F)
  refine ⟨C,hC,?_⟩
  intro q inst hq g M hm t unit
  let w := fun n => (weightedMangoldt M n f:ℂ)
  let E := Real.sqrt M*(C*(M:ℝ)^(1/4:ℝ)*q^2)
  have pos : 0<(M:ℝ) := by exact_mod_cast hm
  have root : Real.sqrt (M:ℝ)≠0 := (Real.sqrt_pos.mpr pos).ne'
  have coeff (n : ℕ) : w n = (Real.sqrt M:ℂ)*(sampleValue M n f:ℂ) := by
    dsimp [w,weightedMangoldt,sampleValue]
    push_cast
    have z : (Real.sqrt M:ℂ)≠0 := by exact_mod_cast root
    field_simp [z]
  have est (χ : Character q) (nc : χ≠1) :
      ‖∑ i ∈ Finset.range M,w i*χ (id i)‖ ≤ E := by
    have h := H q hq g χ nc M hm
    change ‖characterSample χ M (companion f)‖≤_ at h
    have eqn : ∑ i ∈ Finset.range M,w i*χ (id i) =
        (Real.sqrt M:ℂ)*characterSample χ M (companion f) := by
      rw [finite_character_sample χ M hm f F,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [coeff,id_eq,mul_assoc]
    rw [eqn,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
  have h := class_deviation_on t unit id (Finset.range M) w E (by dsimp [E]; positivity) est
  have main : ∑ i ∈ Finset.range M,w i*(1:Character q) (id i) = (principalMass q M f:ℂ) := by
    unfold principalMass
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    by_cases cp : i.Coprime q
    · rw [ite_eq_left cp]
      simp only [id_eq,MulChar.one_apply ((ZMod.isUnit_iff_coprime i q).mpr cp),mul_one,w]
    · rw [ite_eq_right cp]
      simp only [id_eq,MulChar.map_nonunit _ (fun h => cp ((ZMod.isUnit_iff_coprime i q).mp h)),mul_zero,Complex.ofReal_zero]
  have side : (∑ i ∈ Finset.range M, if ((id i):ZMod q)=t then w i else 0) = (classMass q M t f:ℂ) := by
    unfold classMass
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [id,w]
    split <;> simp_all only [Complex.ofReal_zero]
  simp only [id_eq] at h main side
  rw [main,side] at h
  have ident : (classMass q M t f:ℂ)-(principalMass q M f:ℂ)/(q.totient:ℂ) =
      ((classMass q M t f-principalMass q M f/q.totient:ℝ):ℂ) := by push_cast; rfl
  rwa [ident,Complex.norm_real,Real.norm_eq_abs] at h

#print axioms physical_AP
end GoldbachSpectral435

