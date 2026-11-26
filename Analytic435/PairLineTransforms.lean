module
public import DyadicLineArithmetic
public import PrimePairDispersion

/-! Exact dyadic refinement of a two-prime congruence into individual
sum and difference lines. The refinement keeps the sieve modulus fixed
in the prime weights and changes only the modulus of the line. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset
namespace GoldbachSpectral435.GoldbachSieve

def siftedWeight (Q M : ℕ) (f : ℝ→ℝ) (n : ℕ) : ℝ :=
  if n.Coprime Q then weightedMangoldt M n f else 0

private lemma coordinate_mod {q : ℕ} {H n m : ℕ} (sign : Bool) :
    (m:ZMod q)=partner sign H n ↔ (q:ℤ)∣lineCoordinate sign n m-H := by
  cases sign
  · simp only [partner,lineCoordinate,Bool.false_eq_true,ite_false,eq_sub_iff_add_eq]
    rw [← Nat.cast_add,ZMod.natCast_eq_natCast_iff,Nat.modEq_iff_dvd]
    push_cast
    ring_nf
  · simp only [partner,lineCoordinate,ite_true,eq_sub_iff_add_eq]
    rw [← Nat.cast_add,ZMod.natCast_eq_natCast_iff,Nat.modEq_iff_dvd]
    push_cast
    rw [← dvd_neg]
    ring_nf

theorem class_pairs_lines (q H M L : ℕ) [NeZero q] (sign : Bool) (f g : ℝ→ℝ) :
    classPairs q H M L sign f g=lineSum q M L H sign (siftedWeight q M f) (siftedWeight q L g) := by
  classical
  unfold classPairs classMass lineSum
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  have term (t : ZMod q) : (if (n:ZMod q)=t then weightedMangoldt M n f else 0)*
      (∑ m∈range L,if (m:ZMod q)=partner sign H t then weightedMangoldt L m g else 0)=
      if (n:ZMod q)=t then ∑ m∈range L,if (m:ZMod q)=partner sign H n then
        weightedMangoldt M n f*weightedMangoldt L m g else 0 else 0 := by
    by_cases h : (n:ZMod q)=t
    · subst t; simp only [ite_true,mul_sum,mul_ite,mul_zero]
    · simp [h]
  simp_rw [term]
  rw [sum_ite_eq]
  by_cases hn : (n:ZMod q)∈allowed H q
  · rw [ite_eq_left hn]
    apply sum_congr rfl
    intro m _
    by_cases eq : (m:ZMod q)=partner sign H n
    · have u := units_of_allowed hn sign
      have cn := (ZMod.isUnit_iff_coprime ..).mp u.1
      have cm := (ZMod.isUnit_iff_coprime ..).mp (eq ▸ u.2)
      simp only [ite_eq_left eq,ite_eq_left ((coordinate_mod sign).mp eq),siftedWeight,ite_eq_left cn,ite_eq_left cm]
    · simp [eq,mt (coordinate_mod sign).mpr eq]
  · rw [ite_eq_right hn]
    symm
    apply sum_eq_zero
    intro m _
    by_cases eq : (m:ZMod q)=partner sign H n
    · have forbid (a : n.Coprime q) (b : m.Coprime q) : False := by
        apply hn
        rw [mem_allowed]
        apply ((ZMod.isUnit_iff_coprime ..).mpr a).mul
        have h := (ZMod.isUnit_iff_coprime ..).mpr b
        rw [eq] at h
        cases sign
        · exact h
        · simpa only [partner,ite_true,neg_sub] using h.neg
      by_cases cn : n.Coprime q
      · simp only [ite_eq_left ((coordinate_mod sign).mp eq),siftedWeight,ite_eq_right (forbid cn),mul_zero]
      · simp only [ite_eq_left ((coordinate_mod sign).mp eq),siftedWeight,ite_eq_right cn,zero_mul]
    · simp [mt (coordinate_mod sign).mpr eq]

#print axioms class_pairs_lines
end GoldbachSpectral435.GoldbachSieve
