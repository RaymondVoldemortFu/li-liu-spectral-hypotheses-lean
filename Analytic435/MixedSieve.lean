module
public import PeriodicModel
public import PhysicalAP

/-! The mixed correlation of one genuine von Mangoldt factor and one
periodic sieve factor on the surviving residue classes. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset Filter
namespace GoldbachSpectral435.GoldbachSieve
open MathlibNt.SieveTheory.MertensTheorem (primeProduct)

/-- The progression modulus is small enough for a power saving in the
physical character estimate at every sampling length M ≥ N. -/
theorem primorial_cutoff_power (N : ℕ) (np : 0<N) :
    (primorial (localCutoff N):ℝ)^32≤(N:ℝ) := by
  let z := localCutoff N
  have nr : 0<(N:ℝ) := by exact_mod_cast np
  have l : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast np : (1:ℝ)≤N)
  have low : (z:ℝ)≤Real.log N/64 := Nat.floor_le (by positivity)
  by_cases zero : z=0
  · change (primorial z:ℝ)^32≤N
    simp only [zero,primorial_zero,Nat.cast_one,one_pow]
    exact_mod_cast np
  have pp : 0<(primorial z:ℝ) := Nat.cast_pos.mpr (primorial_pos z)
  have h := Real.log_le_log pp (show (primorial z:ℝ)≤(4:ℝ)^z by exact_mod_cast (primorial_lt_four_pow z zero).le)
  rw [Real.log_pow] at h
  have four : Real.log 4≤2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  change (primorial z:ℝ)^32≤N
  apply (Real.log_le_log_iff (pow_pos pp _) nr).mp
  rw [Real.log_pow]
  norm_num
  nlinarith only [low,h,mul_le_mul_of_nonneg_left four (Nat.cast_nonneg (α:=ℝ) z)]

lemma primorial_totient (z : ℕ) :
    ((primorial z).totient:ℝ)=(primorial z:ℝ)*primeProduct z := by
  have h := congrArg (fun r : ℚ => (r:ℝ)) (Nat.totient_eq_mul_prod_factors (primorial z))
  push_cast at h
  rw [primeFactors_primorial] at h
  simp only [primeProduct,one_div]
  exact h

def mixedMass (H z M : ℕ) (f : ℝ→ℝ) : ℝ := by
  classical exact ∑ n∈range M, if (n:ZMod (primorial z))∈allowed H (primorial z)
    then weightedMangoldt M n f else 0

private lemma by_classes (H z M : ℕ) (f : ℝ→ℝ) :
    mixedMass H z M f=∑ t∈allowed H (primorial z), classMass (primorial z) M t f := by
  classical
  unfold mixedMass classMass
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  simp [sum_ite_eq]

/-- The mixed correlation has the same local main factor as the two
periodic weights. The only common scalar is the principal prime sum. -/
theorem mixed_bound (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ H z M : ℕ, 0<H → Even H → 3≤z → 0<M → GRH (primorial z) →
      |mixedMass H z M f/primeProduct z-truncatedSeries H z*principalMass (primorial z) M f|≤
        C*((M:ℝ)^(3/4:ℝ))*(primorial z:ℝ)^4 := by
  classical
  obtain ⟨C,cp,ap⟩ := physical_AP f hf
  refine ⟨C,cp,?_⟩
  intro H z M hp ev zz mp grh
  let Q := primorial z
  let W := primeProduct z
  let U := principalMass Q M f
  let T := truncatedSeries H z
  let E := allowed H Q
  let D := Real.sqrt M*(C*(M:ℝ)^(1/4:ℝ)*Q^2)
  have qp : 0<(Q:ℝ) := Nat.cast_pos.mpr (primorial_pos z)
  have q4 : 4≤Q := (by decide : 4≤primorial 3).trans (primorial_mono zz)
  have qp' : 0<Q.totient := Nat.totient_pos.mpr (primorial_pos z)
  have wt : (Q.totient:ℝ)=(Q:ℝ)*W := primorial_totient z
  have wp : 0<W := pos_of_mul_pos_right (wt ▸ (Nat.cast_pos.mpr qp' : 0<(Q.totient:ℝ))) qp.le
  have wt1 : 1≤(Q:ℝ)*W := wt ▸ (show (1:ℝ)≤Q.totient by exact_mod_cast qp')
  have inv : 1/W≤Q := (div_le_iff₀ wp).mpr wt1
  have card : (E.card:ℝ)=(Q:ℝ)*(W^2*T) :=
    (allowed_count H z).trans (congrArg ((Q:ℝ)*·) (density_identity H z hp ev (by omega)))
  have cardle : (E.card:ℝ)≤Q := by exact_mod_cast E.card_le_univ.trans_eq (ZMod.card Q)
  have dp : 0≤D := by dsimp [D]; positivity
  have error : |mixedMass H z M f-E.card*(U/Q.totient)|≤(Q:ℝ)*D := by
    rw [by_classes,← nsmul_eq_mul,← sum_const,← sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _t∈E,D := by
        apply sum_le_sum
        intro t ht
        exact ap Q q4 grh M mp t (((Commute.all _ _).isUnit_mul_iff.mp ((mem_allowed ..).mp ht)).1)
      _ ≤ _ := by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right cardle dp
  have main : (E.card:ℝ)*(U/Q.totient)=W*(T*U) := by rw [card,wt]; field_simp
  rw [main] at error
  change |mixedMass H z M f/W-T*U|≤_
  have eq : mixedMass H z M f/W-T*U=(mixedMass H z M f-W*(T*U))*(1/W) := by field_simp
  rw [eq,abs_mul,abs_of_pos (one_div_pos.mpr wp)]
  apply (mul_le_mul error inv (one_div_pos.mpr wp).le (mul_nonneg qp.le dp)).trans_eq
  have mr : 0<(M:ℝ) := by exact_mod_cast mp
  have power : Real.sqrt (M:ℝ)*(M:ℝ)^(1/4:ℝ)=(M:ℝ)^(3/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add mr]
    norm_num
  dsimp only [D,Q]
  rw [← power]
  ring

theorem mixed_horizon_power (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ N M H : ℕ, 0<N → N≤M → 3≤localCutoff N →
      0<H → Even H → GRH (primorial (localCutoff N)) →
      |mixedMass H (localCutoff N) M f/((M:ℝ)*primeProduct (localCutoff N))-
        truncatedSeries H (localCutoff N)*(principalMass (primorial (localCutoff N)) M f/M)|≤
        C/(M:ℝ)^(1/8:ℝ) := by
  obtain ⟨C,cp,work⟩ := mixed_bound f hf
  refine ⟨C,cp,?_⟩
  intro N M H np nm zz hp ev grh
  let z := localCutoff N
  let Q : ℝ := primorial z
  have qp : 0<Q := Nat.cast_pos.mpr (primorial_pos z)
  have mp := np.trans_le nm
  have mr : 0<(M:ℝ) := by exact_mod_cast mp
  have q32 : Q^32≤(M:ℝ) := (primorial_cutoff_power N np).trans (Nat.cast_le.mpr nm)
  have fourth : Q^4≤(M:ℝ)^(1/8:ℝ) := by
    have cmp := Real.rpow_le_rpow (pow_nonneg qp.le 32) q32 (by norm_num : 0≤(1/8:ℝ))
    rw [← Real.rpow_natCast_mul qp.le] at cmp
    norm_num at cmp ⊢
    exact cmp
  have p := work H z M hp ev zz mp grh
  rw [show mixedMass H z M f/((M:ℝ)*primeProduct z)-
      truncatedSeries H z*(principalMass (primorial z) M f/M)=
      (mixedMass H z M f/primeProduct z-truncatedSeries H z*principalMass (primorial z) M f)/M by ring,
    abs_div,abs_of_pos mr]
  apply (div_le_div_of_nonneg_right p mr.le).trans
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left fourth (by positivity : 0≤C*(M:ℝ)^(3/4:ℝ))) mr.le).trans_eq
  rw [div_eq_div_iff (by positivity) (by positivity)]
  calc
    _ = C*(((M:ℝ)^(3/4:ℝ)*(M:ℝ)^(1/8:ℝ))*(M:ℝ)^(1/8:ℝ)) := by ring
    _ = C*M := by rw [← Real.rpow_add mr,← Real.rpow_add mr]; norm_num

#print axioms mixed_horizon_power
end GoldbachSpectral435.GoldbachSieve
