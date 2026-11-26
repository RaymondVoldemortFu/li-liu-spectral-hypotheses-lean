module
public import PrimeCharacterCancellation

/-! Parseval on the full group of Dirichlet characters, with the
principal character removed. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex Finset
open scoped ComplexConjugate Classical
namespace GoldbachSpectral435.CriticalCharacter

def unitClasses (q : ℕ) [NeZero q] : Finset (ZMod q) := by classical exact univ.filter IsUnit

@[simp] lemma mem_unitClasses {q : ℕ} [NeZero q] {t : ZMod q} : t∈unitClasses q ↔ IsUnit t := by
  classical simp [unitClasses]

def classError {q : ℕ} (M : ℕ) (f : ℝ→ℝ) (t : ZMod q) :=
  classMass q M t f-principalMass q M f/q.totient

private lemma eval_sum {q : ℕ} [NeZero q] (χ : Character q) :
    (∑ t∈unitClasses q,χ t)=if χ=1 then (q.totient:ℂ) else 0 := by
  classical
  have ext : (∑ t∈unitClasses q,χ t)=∑ t,χ t := sum_subset (subset_univ _) (fun t _ h => χ.map_nonunit (mt mem_unitClasses.mpr h))
  rw [ext]
  split_ifs with one
  · subst χ
    rw [MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one one

private lemma twist_classes {q : ℕ} [NeZero q] (χ : Character q) (M : ℕ) (f : ℝ→ℝ) :
    (∑ t∈unitClasses q,(classMass q M t f:ℂ)*χ t)=primeTwist χ M f := by
  classical
  unfold classMass primeTwist
  push_cast
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  have term (t : ZMod q) : ((if (n:ZMod q)=t then weightedMangoldt M n f else 0:ℝ):ℂ)*χ t=
      if (n:ZMod q)=t then (weightedMangoldt M n f:ℂ)*χ n else 0 := by
    by_cases h : (n:ZMod q)=t
    · subst t; simp
    · simp [h]
  simp_rw [term,sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [χ.map_nonunit (mt mem_unitClasses.mpr h),mul_zero]

private lemma principal_twist {q : ℕ} [NeZero q] (M : ℕ) (f : ℝ→ℝ) :
    primeTwist (1:Character q) M f=principalMass q M f := by
  unfold primeTwist principalMass
  push_cast
  apply sum_congr rfl
  intro n _
  by_cases cp : n.Coprime q
  · rw [ite_eq_left cp,MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr cp),mul_one]
  · rw [ite_eq_right cp,MulChar.map_nonunit _ (mt (ZMod.isUnit_iff_coprime n q).mp cp),mul_zero]
    rfl

private lemma error_twist {q : ℕ} [NeZero q] (χ : Character q) (M : ℕ) (f : ℝ→ℝ) :
    (∑ t∈unitClasses q,(classError M f t:ℂ)*χ t)=if χ=1 then 0 else primeTwist χ M f := by
  classical
  unfold classError
  push_cast
  simp_rw [sub_mul]
  rw [sum_sub_distrib,← mul_sum,twist_classes,eval_sum]
  by_cases e : χ=1
  · subst χ
    simp [principal_twist,NeZero.ne (q.totient:ℂ)]
  · simp [e]

/-- Finite Parseval on any set of unit residue classes. -/
private theorem unit_parseval {q : ℕ} [NeZero q] (b : ZMod q→ℝ) :
    (∑ χ : Character q, ‖∑ t∈unitClasses q,(b t:ℂ)*χ t‖^2)=
      (q.totient:ℝ)*∑ t∈unitClasses q,(b t)^2 := by
  classical
  let E := unitClasses q
  have one (χ : Character q) : ((‖∑ t∈E,(b t:ℂ)*χ t‖^2:ℝ):ℂ)=
      ∑ t∈E,∑ u∈E,(b t:ℂ)*b u*(χ t*conj (χ u)) := by
    rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,mul_comm]
    simp only [map_sum,map_mul,conj_ofReal,sum_mul,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro u _
    ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  change (∑ χ : Character q,((‖∑ t∈E,(b t:ℂ)*χ t‖^2:ℝ):ℂ))=_
  simp_rw [one]
  push_cast
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro t ht
  rw [sum_comm]
  have zero (u : ZMod q) (hu : u∈E) : (∑ χ : Character q,(b t:ℂ)*b u*(χ t*conj (χ u)))=
      if t=u then (q.totient:ℂ)*(b t:ℂ)^2 else 0 := by
    rw [← mul_sum,full_character_orthogonality t u (mem_unitClasses.mp hu)]
    split_ifs with eq
    · subst u; ring
    · ring
  rw [sum_congr rfl zero,sum_ite_eq]
  simp [ht]

theorem class_variance_identity {q : ℕ} [NeZero q] (M : ℕ) (f : ℝ→ℝ) :
    (q.totient:ℝ)*(∑ t∈unitClasses q,(classError M f t)^2)=
      ∑ χ∈univ.erase (1:Character q),‖primeTwist χ M f‖^2 := by
  classical
  rw [← unit_parseval]
  simp_rw [error_twist]
  rw [← sum_erase_add _ _ (mem_univ (1:Character q))]
  simp only [ite_true,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,add_zero]
  apply sum_congr rfl
  intro χ h
  rw [ite_eq_right (mem_erase.mp h).1]

/-- The class-variance bound loses no factor in the number of residue
classes. It holds for each individual modulus. -/
theorem class_variance_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ (q M : ℕ) [NeZero q], 4≤q → q≤M → GRH q →
      (∑ t∈unitClasses q,(classError M f t)^2)≤
        (C*Real.sqrt M*(Real.log M)^2*(6+Real.log q))^2 := by
  classical
  obtain ⟨C,cp,all⟩ := prime_twist_bound f hf
  refine ⟨C,cp,?_⟩
  intro q M inst q4 qm grh
  let B := C*Real.sqrt M*(Real.log M)^2*(6+Real.log q)
  let T := univ.erase (1:Character q)
  have φ : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have card : T.card≤q.totient := by
    have b := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    rw [Nat.card_eq_fintype_card] at b
    exact (card_le_card (erase_subset ..)).trans (by simpa using b.le)
  apply le_of_mul_le_mul_left _ φ
  rw [class_variance_identity]
  have per (χ : Character q) (h : χ∈T) := pow_le_pow_left₀ (norm_nonneg _) (all q M q4 qm grh χ (mem_erase.mp h).1) 2
  apply (sum_le_sum per).trans
  rw [sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr card) (sq_nonneg B)

#print axioms class_variance_identity
#print axioms class_variance_bound
end GoldbachSpectral435.CriticalCharacter
