module
public import ConditionalGoldbach.Proofs.Characters

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex
open scoped ComplexConjugate
namespace GoldbachSpectral435

private theorem cast_strip {N m n : ℕ} (hm : 0 < m) (small : 4*m < N)
    (lo : 3*N < 4*n) (hi : 4*n < 5*N) :
    ((n:ZMod N) = m ↔ n = N+m) ∧ ((n:ZMod N) = -(m:ZMod N) ↔ n = N-m) := by
  have hn : 0 < N := by omega
  have hmN : m < N := by omega
  constructor
  · rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hmN]
    by_cases h : n < N
    · rw [Nat.mod_eq_of_lt h]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : N ≤ n),Nat.mod_eq_of_lt (by omega : n-N < N)]
      omega
  · rw [← add_eq_zero_iff_eq_neg,← Nat.cast_add,ZMod.natCast_eq_zero_iff]
    constructor
    · rintro ⟨j,hj⟩
      have lower : 0 < j := by by_contra! hh; interval_cases j; simp at hj; omega
      have upper : j < 2 := by
        by_contra! h
        have inc := Nat.mul_le_mul_left N h
        omega
      have : j=1 := by omega
      simp [this] at hj
      omega
    · intro h
      rw [h,Nat.sub_add_cancel hmN.le]

/-- On the narrow and broad physical supports the two congruence selectors
give exactly N+m and N-m. Both retain the genuine coprimality condition. -/
theorem opposite_projector (N m n : ℕ) [NeZero N] (even : Even N) (big : 4 ≤ N)
    (hm : 0 < m) (small : 4*m<N) (lo : 3*N<4*n) (hi : 4*n<5*N) :
    (2/(N.totient:ℂ))*∑ χ ∈ oddCharacters N, χ n * conj (χ m) =
      if m.Coprime N then (if n=N+m then (1:ℂ) else 0) - (if n=N-m then 1 else 0) else 0 := by
  rw [lemma_3_1_odd_orthogonality N even big]
  simp only [(cast_strip hm small lo hi).1,
    (cast_strip hm small lo hi).2,Nat.coprime_mul_iff_left]
  by_cases hc : m.Coprime N
  · rw [ite_eq_left hc]
    by_cases hp : n=N+m
    · subst n
      simp [hc]
    · by_cases hn : n=N-m
      · subst n
        have hdiff : (N-m).Coprime N := (Nat.coprime_self_sub_left (by omega)).mpr hc
        simp [hdiff,hc]
      · simp [hp,hn]
  · simp [hc]

/-- Summing the projector against a broad test retains exactly the two
shifted samples. The weight can be arbitrary away from the support. -/
theorem broad_projection (N m : ℕ) [NeZero N] (even : Even N) (big : 4 ≤ N)
    (hm : 0<m) (small : 4*m<N) (v : ℕ → ℂ)
    (supp : ∀ n, v n ≠ 0 → 3*N<4*n ∧ 4*n<5*N) :
    (∑ n ∈ Finset.range (2*N), v n * ((2/(N.totient:ℂ))*∑ χ ∈ oddCharacters N, χ n*conj (χ m))) =
      if m.Coprime N then v (N+m)-v (N-m) else 0 := by
  have point (n : ℕ) : v n * ((2/(N.totient:ℂ))*∑ χ ∈ oddCharacters N, χ n*conj (χ m)) =
      if m.Coprime N then (if n=N+m then v n else 0) - (if n=N-m then v n else 0) else 0 := by
    by_cases h : v n = 0
    · simp [h]
    · have s := supp n h
      rw [opposite_projector N m n even big hm small s.1 s.2]
      split_ifs <;> ring
  simp_rw [point]
  split_ifs with hc
  · rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq',show N+m<2*N by omega,show N-m<2*N by omega]
  · simp

#print axioms broad_projection
end GoldbachSpectral435

