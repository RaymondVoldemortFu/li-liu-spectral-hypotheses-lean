module
public import Mathlib.Tactic

/-! Exact dyadic refinement for compactly supported arithmetic weights. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset
namespace GoldbachSpectral435.GoldbachSieve

def lineCoordinate (sign : Bool) (n m : ℕ) : ℤ :=
  if sign then (n:ℤ)+m else (n:ℤ)-m

def lineSum (q M L : ℕ) (d : ℤ) (sign : Bool) (a b : ℕ→ℝ) : ℝ :=
  ∑ n∈range M,∑ m∈range L, if (q:ℤ)∣lineCoordinate sign n m-d then a n*b m else 0

def exactLine (M L : ℕ) (d : ℤ) (sign : Bool) (a b : ℕ→ℝ) : ℝ :=
  ∑ n∈range M,∑ m∈range L, if lineCoordinate sign n m=d then a n*b m else 0

private lemma double_split {q d : ℤ} (hq : 0<q) (v : ℝ) :
    (if q∣d then v else 0)=(if 2*q∣d then v else 0)+(if 2*q∣d-q then v else 0) := by
  have small (h : 2*q∣d-q) : q∣d := by
    obtain ⟨k,h⟩ := h
    exact ⟨2*k+1,by linear_combination h⟩
  have left (h : 2*q∣d) : q∣d := (dvd_mul_left q 2).trans h
  have excl (h : 2*q∣d) (h' : 2*q∣d-q) : False := by
    obtain ⟨a,ha⟩ := h
    obtain ⟨b,hb⟩ := h'
    have eq : q*(2*(a-b))=q*1 := by linear_combination hb-ha
    have := mul_left_cancel₀ hq.ne' eq
    omega
  by_cases h : q∣d
  · rw [ite_eq_left h]
    obtain ⟨k,hk⟩ := h
    rcases Int.even_or_odd k with ⟨u,hu⟩|⟨u,hu⟩
    · have yes : 2*q∣d := ⟨u,by rw [hk,hu]; ring⟩
      rw [ite_eq_left yes,ite_eq_right (excl yes),add_zero]
    · have yes : 2*q∣d-q := ⟨u,by rw [hk,hu]; ring⟩
      rw [ite_eq_right (fun he => excl he yes),ite_eq_left yes,zero_add]
  · simp [h,mt small h,mt left h]

theorem split_line (q M L : ℕ) (qp : 0<q) (d : ℤ) (sign : Bool) (a b : ℕ→ℝ) :
    lineSum q M L d sign a b=lineSum (2*q) M L d sign a b+lineSum (2*q) M L (d+q) sign a b := by
  unfold lineSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  simp only [Nat.cast_mul,Nat.cast_ofNat,sub_add_eq_sub_sub]
  exact double_split (Nat.cast_pos.mpr qp) _

theorem exact_line_recovery {q M L : ℕ} (d : ℤ) (sign : Bool) (a b : ℕ→ℝ)
    (cap : ∀ n<M, ∀ m<L, |lineCoordinate sign n m-d|<(q:ℤ)) :
    lineSum q M L d sign a b=exactLine M L d sign a b := by
  unfold lineSum exactLine
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro m hm
  have sm := cap n (mem_range.mp hn) m (mem_range.mp hm)
  have eq : (q:ℤ)∣lineCoordinate sign n m-d ↔ lineCoordinate sign n m=d := by
    constructor
    · intro dv
      by_contra ne
      have v := Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr ne)) ((dvd_abs ..).mpr dv)
      omega
    · intro h; simp [h]
  simp only [eq]

#print axioms split_line
#print axioms exact_line_recovery
end GoldbachSpectral435.GoldbachSieve
