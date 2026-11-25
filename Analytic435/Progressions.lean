module
public import Characters
public import ConditionalGoldbach.Proofs.Characters

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex Set
open scoped ComplexConjugate
namespace GoldbachSpectral435

/-- Finite character inversion. The main term is the same principal sum for
all unit classes. The error is uniform and carries no additional totient. -/
theorem class_deviation_on {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (n : ℕ → ℕ) (S : Finset ℕ) (w : ℕ → ℂ) (E : ℝ) (ep : 0 ≤ E)
    (bound : ∀ χ : Character q, χ ≠ 1 → ‖∑ i ∈ S, w i * χ (n i)‖ ≤ E) :
    ‖(∑ i ∈ S, if ((n i):ZMod q)=a then w i else 0) -
      (∑ i ∈ S, w i * (1:Character q) (n i))/(q.totient:ℂ)‖ ≤ E := by
  classical
  let φ := (q.totient:ℂ)
  have ph : φ ≠ 0 := by dsimp [φ]; exact_mod_cast (NeZero.ne q.totient)
  let T := fun χ : Character q => conj (χ a)*(∑ i ∈ S, w i * χ (n i))
  let R := ∑ i ∈ S, if ((n i):ZMod q)=a then w i else 0
  have inv : ∑ χ : Character q, T χ = φ*R := by
    simp only [T,R,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have eqn := full_character_orthogonality ((n i):ZMod q) a ha
    calc
      _ = w i*(∑ χ : Character q, χ (n i)*conj (χ a)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by rw [eqn]; split_ifs <;> ring
  have unit : (1:Character q) a = 1 := by
    rw [← ha.unit_spec]
    exact MulChar.one_apply_coe _
  have one : T 1 = ∑ i ∈ S, w i*(1:Character q) (n i) := by simp [T,unit]
  let Sχ := Finset.univ.erase (1:Character q)
  have remove : ∑ χ ∈ Sχ, T χ = φ*R-T 1 := by
    rw [← inv,eq_sub_iff_add_eq]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ _)
  have card : Sχ.card ≤ q.totient := by
    have h := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    rw [Nat.card_eq_fintype_card] at h
    exact (Finset.card_le_card (Finset.erase_subset ..)).trans (by simpa using h.le)
  have major : ‖∑ χ ∈ Sχ, T χ‖ ≤ (q.totient:ℝ)*E := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _ ∈ Sχ, E := by
        apply Finset.sum_le_sum
        intro χ hχ
        have hne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
        dsimp only [T]
        rw [norm_mul,Complex.norm_conj]
        exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one a)).trans (bound χ hne)
      _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul]; gcongr
  change ‖R-_/φ‖ ≤ E
  rw [← one,show R-T 1/φ=(φ*R-T 1)/φ by field_simp,← remove,norm_div]
  have fnorm : ‖φ‖ = (q.totient:ℝ) := by simp [φ]
  rw [fnorm]
  exact (div_le_iff₀ (by exact_mod_cast (NeZero.pos q.totient))).mpr (by simpa [mul_comm] using major)

/-- Smooth class average under local GRH at the progression modulus q and
an arbitrary independent cutoff scale M. -/
theorem smooth_class_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) {a b : ℝ}
    (sf : Function.support f ⊆ Icc a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q], 4 ≤ q → GRH q →
      ∀ t : ZMod q, IsUnit t → ∀ M : ℕ, 0 < M →
      let w := fun i : ℕ => ((mangoldt (i+1):ℂ)/(i+1:ℕ)^(1/2:ℂ)) * (f ((i+1:ℕ)/(M:ℝ)):ℂ)
      ‖(∑' i : ℕ, if ((i+1:ℕ):ZMod q)=t then w i else 0) -
        (∑' i : ℕ, w i*(1:Character q) (i+1))/(q.totient:ℂ)‖ ≤ C*(M:ℝ)^(1/4:ℝ)*q^2 := by
  obtain ⟨C,hC,B⟩ := smooth_character_bound f hf sf
  refine ⟨C,hC,?_⟩
  intro q inst hq grh t unit M hM w
  obtain ⟨K,hK⟩ := exists_nat_gt (b*(M:ℝ))
  let S := Finset.range K
  have cut (i : ℕ) (hi : i ∉ S) : w i = 0 := by
    have low : K ≤ i := by simpa [S] using hi
    have mp : 0 < (M:ℝ) := by exact_mod_cast hM
    have ip : (K:ℝ) ≤ i := by exact_mod_cast low
    have gt : b < (i+1:ℕ)/(M:ℝ) := (lt_div_iff₀ mp).mpr (by push_cast; linarith)
    have z : f ((i+1:ℕ)/(M:ℝ)) = 0 := by by_contra nz; exact (not_lt_of_ge (sf nz).2) gt
    dsimp only [w]
    rw [z,Complex.ofReal_zero,mul_zero]
  have finite (χ : Character q) : ∑' i : ℕ, w i*χ (i+1) = ∑ i ∈ S,w i*χ (i+1) :=
    tsum_eq_sum (fun i hi => by rw [cut i hi,zero_mul])
  rw [finite,tsum_eq_sum (s := S) (fun i hi => by rw [cut i hi]; simp)]
  have scalar (χ : Character q) (hχ : χ≠1) : ‖∑ i∈S,w i*χ (i+1)‖ ≤ C*(M:ℝ)^(1/4:ℝ)*q^2 := by
    rw [← finite]
    have ident (i : ℕ) : w i * χ (i+1) =
        ((mangoldt (i+1):ℂ)*χ (i+1)/(i+1:ℕ)^(1/2:ℂ)) * (f ((i+1:ℕ)/(M:ℝ)):ℂ) := by dsimp [w]; ring
    simp_rw [ident]
    exact B q hq grh χ hχ M hM
  simpa only [Nat.cast_add,Nat.cast_one] using class_deviation_on t unit (fun i => i+1) S w
    (C*(M:ℝ)^(1/4:ℝ)*q^2) (by positivity) (fun χ nc => by simpa only [Nat.cast_add,Nat.cast_one] using scalar χ nc)

#print axioms smooth_class_bound
end GoldbachSpectral435

