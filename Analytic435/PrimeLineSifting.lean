module
public import PairLineTransforms
public import Mathlib.Data.Nat.Log

/-! The loss from imposing unit conditions on the two coordinates of one
specified sum or difference line. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset
namespace GoldbachSpectral435.GoldbachSieve

def excludedMass (q n : ℕ) : ℝ := if n.Coprime q then 0 else mangoldt n

/-- Every excluded prime power of size below M divides a single power of q.
Summing the von Mangoldt divisor identity gives a logarithmic bound. -/
theorem excluded_mass_bound (q M : ℕ) (qp : 0<q) :
    (∑ n∈range M,excludedMass q n)≤(Nat.log 2 M:ℝ)*Real.log q := by
  classical
  let k := Nat.log 2 M
  let S := (range M).filter (fun n => ¬n.Coprime q ∧ IsPrimePow n)
  have eq : (∑ n∈range M,excludedMass q n)=∑ n∈S,mangoldt n := by
    rw [show S=(range M).filter _ from rfl,sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases h : n.Coprime q
    · simp [excludedMass,h]
    · by_cases w : IsPrimePow n
      · simp [excludedMass,h,w]
      · have z : mangoldt n=0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr w
        simp [excludedMass,h,w,z]
  have sub : S⊆(q^k).divisors := by
    intro n hn
    obtain ⟨nr,nc,pw⟩ := mem_filter.mp hn
    obtain ⟨p,j,prime,jp,rfl⟩ := (isPrimePow_nat_iff _).mp pw
    have d : p∣q := by
      by_contra nd
      exact nc ((prime.coprime_iff_not_dvd.mpr nd).pow_left j)
    have le : j≤k := Nat.le_log_of_pow_le (by decide) ((Nat.pow_le_pow_left prime.two_le j).trans (mem_range.mp nr).le)
    exact Nat.mem_divisors.mpr ⟨pow_dvd_pow_of_dvd_of_le d le,pow_ne_zero _ qp.ne'⟩
  rw [eq]
  calc
    _ ≤ ∑ n∈(q^k).divisors,mangoldt n := sum_le_sum_of_subset_of_nonneg sub
      fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log (q^k:ℕ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

private lemma one_partner {α : Type*} [DecidableEq α] (s : Finset α) (P : α→Prop) [DecidablePred P]
    (unique : ∀ a b, P a → P b → a=b) (x : ℝ) (xp : 0≤x) :
    (∑ a∈s,if P a then x else 0)≤x := by
  classical
  by_cases e : ∃ a∈s,P a
  · obtain ⟨a,ha,pa⟩ := e
    rw [sum_eq_single_of_mem a ha]
    · simp [pa]
    · intro b _ ne
      exact ite_eq_right (fun pb => ne (unique b a pb pa))
  · rw [sum_eq_zero]
    · exact xp
    · intro a ha; exact ite_eq_right (fun pa => e ⟨a,ha,pa⟩)

private lemma line_marginals (M : ℕ) (d : ℤ) (sign : Bool) (w : ℕ→ℝ) (wp : ∀ n, 0≤w n) :
    (∑ n∈range M,∑ m∈range M,if lineCoordinate sign n m=d then w n+w m else 0)≤
      2*∑ n∈range M,w n := by
  have separate (n m : ℕ) : (if lineCoordinate sign n m=d then w n+w m else 0)=
      (if lineCoordinate sign n m=d then w n else 0)+(if lineCoordinate sign n m=d then w m else 0) := by
    split <;> simp
  simp_rw [separate,sum_add_distrib]
  rw [sum_comm (s:=range M) (t:=range M) (f:=fun n m => if lineCoordinate sign n m=d then w m else 0),two_mul]
  apply add_le_add <;> apply sum_le_sum <;> intro n _ <;> apply one_partner _ _ _ _ (wp n) <;>
    intro a b ha hb <;> cases sign <;> simp_all [lineCoordinate] <;> omega

/-- Uniform for both signs and all integer line coordinates, including the
diagonal. The loss is unnormalized and involves no hypotheses on zeros. -/
theorem exact_line_sifting (q M : ℕ) (qp : 0<q) (mp : 0<M) (d : ℤ) (sign : Bool)
    (f g : ℝ→ℝ) (F G : ℝ) (fp : 0≤F) (gp : 0≤G)
    (hb : ∀ n<M, |f (n/(M:ℝ))|≤F) (hc : ∀ n<M, |g (n/(M:ℝ))|≤G) :
    |exactLine M M d sign (fun n => weightedMangoldt M n f) (fun n => weightedMangoldt M n g)-
      exactLine M M d sign (siftedWeight q M f) (siftedWeight q M g)|≤
      2*F*G*Real.log M*(Nat.log 2 M:ℝ)*Real.log q := by
  let B := F*G*Real.log M
  let w := excludedMass q
  have lp : 0≤Real.log (M:ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr mp)
  have bp : 0≤B := by dsimp [B]; positivity
  have wp (n : ℕ) : 0≤w n := by dsimp [w,excludedMass]; split <;> positivity
  have point (n m : ℕ) (hn : n<M) (hm : m<M) :
      |weightedMangoldt M n f*weightedMangoldt M m g-siftedWeight q M f n*siftedWeight q M g m|≤
        B*(w n+w m) := by
    have v (i : ℕ) (hi : i<M) : mangoldt i≤Real.log M := mangoldt_le_log_of_le mp hi.le
    have np : 0≤mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have mp' : 0≤mangoldt m := ArithmeticFunction.vonMangoldt_nonneg
    have bound : |weightedMangoldt M n f*weightedMangoldt M m g|≤F*G*(mangoldt n*mangoldt m) := by
      simp only [weightedMangoldt,abs_mul,abs_of_nonneg np,abs_of_nonneg mp']
      calc
        _ = (|f (n/(M:ℝ))| *|g (m/(M:ℝ))|)*(mangoldt n*mangoldt m) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul (hb n hn) (hc m hm) (abs_nonneg _) fp) (mul_nonneg np mp')
    by_cases a : n.Coprime q
    · by_cases b : m.Coprime q
      · simp only [siftedWeight,w,excludedMass,ite_eq_left a,ite_eq_left b,sub_self,abs_zero,
          add_zero,mul_zero,le_refl]
      · simp only [siftedWeight,w,excludedMass,ite_eq_left a,ite_eq_right b,mul_zero,sub_zero,zero_add]
        have u := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (v n hn) mp') (mul_nonneg fp gp)
        exact bound.trans (by dsimp only [B]; linarith only [u])
    · simp only [siftedWeight,ite_eq_right a,zero_mul,sub_zero]
      have lower := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (wp m) (a:=w n)) bp
      rw [show w n=mangoldt n from ite_eq_right a] at lower ⊢
      have u := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (v m hm) np) (mul_nonneg fp gp)
      apply bound.trans (le_trans _ lower)
      dsimp only [B]
      linarith only [u]
  let t := fun n m : ℕ => if lineCoordinate sign n m=d then
      weightedMangoldt M n f*weightedMangoldt M m g-siftedWeight q M f n*siftedWeight q M g m else 0
  have e : exactLine M M d sign (fun n => weightedMangoldt M n f) (fun n => weightedMangoldt M n g)-
      exactLine M M d sign (siftedWeight q M f) (siftedWeight q M g)=∑ n∈range M,∑ m∈range M,t n m := by
    unfold exactLine
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    dsimp only [t]
    split <;> simp
  rw [e]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ n∈range M,∑ m∈range M,|t n m| := sum_le_sum fun _ _ => abs_sum_le_sum_abs ..
    _ ≤ B*(∑ n∈range M,∑ m∈range M,if lineCoordinate sign n m=d then w n+w m else 0) := by
      simp_rw [mul_sum]
      apply sum_le_sum
      intro n hn
      apply sum_le_sum
      intro m hm
      dsimp only [t]
      split
      · exact point n m (mem_range.mp hn) (mem_range.mp hm)
      · simp
    _ ≤ B*(2*((Nat.log 2 M:ℝ)*Real.log q)) := mul_le_mul_of_nonneg_left
      ((line_marginals M d sign w wp).trans (by linarith only [excluded_mass_bound q M qp])) bp
    _ = _ := by dsimp [B]; ring

#print axioms exact_line_sifting
end GoldbachSpectral435.GoldbachSieve
