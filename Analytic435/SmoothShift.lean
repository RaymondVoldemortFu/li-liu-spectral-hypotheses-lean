module
public import PrimeMass
public import Opposite
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open ConditionalGoldbach Finset Set
namespace GoldbachSpectral435

theorem broad_lipschitz : ∃ D : ℝ, 0<D ∧ ∀ x y : ℝ, |broad x-broad y|≤D*|x-y| := by
  have sm : ContDiff ℝ ∞ (broad : ℝ → ℝ) := broad.contDiff
  obtain ⟨C,B⟩ := (sm.continuous_deriv (by simp)).bounded_above_of_compact_support broad.hasCompactSupport.deriv
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x y
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => sm.differentiable (by simp) z) (fun z _ => B z) (Set.mem_univ y) (Set.mem_univ x)
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

/-- Translating a sum of sampled weights leaves its finite truncation exact
when the discarded endpoint terms vanish. -/
theorem translate_supported (M j : ℕ) (f : ℕ → ℝ)
    (lo : ∀ n<j, f n=0) (hi : ∀ n≥M, f n=0) :
    ∑ u∈range M, f (u+j) = ∑ n∈range M,f n := by
  have front : ∑ n∈range j,f n=0 := sum_eq_zero (fun n hn => lo n (mem_range.mp hn))
  have tail : ∑ u∈range j,f (M+u)=0 := sum_eq_zero (fun n _ => hi (M+n) (by omega))
  have left := Finset.sum_range_add f j M
  have right := Finset.sum_range_add f M j
  rw [front,zero_add,Nat.add_comm j M] at left
  rw [tail,add_zero] at right
  rw [← right,left]
  apply sum_congr rfl
  intro u _
  rw [Nat.add_comm]

theorem weight_zero_low (M n : ℕ) (hm : 0<M) (h : 4*n≤M) : broad (n/(M:ℝ))=0 := by
  by_contra nz
  have p := (broad_support nz).1
  have hr : 4*(n:ℝ)≤M := by exact_mod_cast h
  have r := (lt_div_iff₀ (show 0<(M:ℝ) by exact_mod_cast hm)).mp p
  linarith

theorem weight_zero_high (M n : ℕ) (hm : 0<M) (h : M≤n) : broad (n/(M:ℝ))=0 := by
  by_contra nz
  have p := (broad_support nz).2
  have hr : (M:ℝ)≤n := by exact_mod_cast h
  have r := (div_lt_iff₀ (show 0<(M:ℝ) by exact_mod_cast hm)).mp p
  linarith

theorem class_translate {q : ℕ} [NeZero q] (M i j m : ℕ) (hm : 0<M) (small : 4*j≤M) (a : ZMod q) :
    (∑ u∈range M, if ((u+i:ℕ):ZMod q)=a ∧ (u+j).Coprime m then weightedMangoldt M (u+j) broad else 0) =
      restrictedMass q M m (a+j-i) broad := by
  let f := fun n : ℕ => if (n:ZMod q)=a+j-i ∧ n.Coprime m then weightedMangoldt M n broad else 0
  have low (n : ℕ) (hn : n<j) : f n=0 := by simp [f,weightedMangoldt,weight_zero_low M n hm (by omega)]
  have high (n : ℕ) (hn : M≤n) : f n=0 := by simp [f,weightedMangoldt,weight_zero_high M n hm hn]
  rw [← show ∑ n∈range M,f n=restrictedMass q M m (a+j-i) broad from rfl,← translate_supported M j f low high]
  apply sum_congr rfl
  intro u _
  have h : ((u+i:ℕ):ZMod q)=a ↔ ((u+j:ℕ):ZMod q)=a+j-i := by push_cast; constructor <;> intro v <;> linear_combination v
  simp only [f,h]

/-- Uniform translation cost in the two weights. The Mangoldt factors and
class indicator are kept inside the sum. -/
theorem shift_weight_error {q : ℕ} (M i j m : ℕ) (hm : 0<M) (jcap : j≤M) (a : ZMod q)
    (D : ℝ) (dp : 0≤D) (lip : ∀ x y : ℝ, |broad x-broad y|≤D*|x-y|) :
    |∑ u∈range M, if ((u+i:ℕ):ZMod q)=a ∧ (u+j).Coprime m then
      mangoldt (u+j)*(broad ((u+i:ℕ)/(M:ℝ))-broad ((u+j:ℕ)/(M:ℝ))) else 0| ≤
      D*(i+j)*Real.log (2*M) := by
  have mp : 0<(M:ℝ) := by exact_mod_cast hm
  have lg : 0≤Real.log (2*(M:ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1≤2*M by omega))
  let A : ℝ := D*((i:ℝ)+j)/(M:ℝ)
  have ap : 0≤A := by dsimp [A]; positivity
  let L := Real.log (2*(M:ℝ))
  have each (u : ℕ) (hu : u∈range M) :
      |if ((u+i:ℕ):ZMod q)=a ∧ (u+j).Coprime m then mangoldt (u+j)*(broad ((u+i:ℕ)/(M:ℝ))-broad ((u+j:ℕ)/(M:ℝ))) else 0|≤L*A := by
    split
    · rw [abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have bd : mangoldt (u+j)≤L := by
        by_cases z : u+j=0
        · simpa [z,mangoldt] using lg
        · exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log
            (by exact_mod_cast Nat.pos_of_ne_zero z) (by exact_mod_cast (show u+j≤2*M by have := mem_range.mp hu; omega)))
      apply mul_le_mul bd _ (abs_nonneg _) lg
      have cmp : |((u+i:ℕ):ℝ)/M-((u+j:ℕ):ℝ)/M| ≤ ((i:ℝ)+j)/M := by
        rw [← sub_div,abs_div,abs_of_pos mp]
        push_cast
        apply div_le_div_of_nonneg_right _ mp.le
        rw [show (u:ℝ)+i-(u+j)=i-j by ring]
        exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) i],by linarith [Nat.cast_nonneg (α := ℝ) j]⟩
      exact (lip _ _).trans ((mul_le_mul_of_nonneg_left cmp dp).trans_eq (by dsimp [A]; ring))
    · simpa using mul_nonneg lg ap
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum each).trans_eq
  simp only [sum_const,card_range,nsmul_eq_mul,L,A]
  field_simp

end GoldbachSpectral435

