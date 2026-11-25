module
public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
namespace GoldbachSpectral

noncomputable def deltaSq (N : ℕ) (s : ℝ) := s * Real.log N ^ 3 / N

noncomputable def width (N : ℕ) (s h : ℝ) := h^2 * Real.log N ^ 3 / (N*s)

/-- Squared norm forms of the two exact equivalences in Li–Liu, Theorem 6.1. -/
def Rbound (D M : ℝ) := M^2 ≤ D
def Sbound (D M η : ℝ) := 4*η*(1-η)*M^2 ≤ D

theorem strongest_width (D M : ℝ) :
    (∀ η : ℝ, 0 < η → η ≤ 1/4 → Sbound D M η) ↔ 3*M^2 ≤ 4*D := by
  constructor
  · intro h
    have hh := h (1/4) (by norm_num) (by norm_num)
    unfold Sbound at hh
    linarith
  · intro h η _ he
    unfold Sbound
    have hprod := mul_nonneg (show 0 ≤ 1/4-η by linarith) (show 0 ≤ 3/4-η by linarith)
    nlinarith [mul_nonneg hprod (sq_nonneg M)]

theorem R_implies_all_widths {D M : ℝ} (hr : Rbound D M) :
    ∀ η : ℝ, 0 < η → η ≤ 1/4 → Sbound D M η := by
  apply (strongest_width _ _).2
  unfold Rbound at hr
  nlinarith [sq_nonneg M]

theorem S_implies_normalized_bound {N : ℕ} {s h M : ℝ}
    (hn : 1 < N) (hs : 0 < s) (hh : 0 < h) (hadm : width N s h ≤ 1/4)
    (H : Sbound (deltaSq N s) M (width N s h)) :
    3*h^2*M^2 ≤ s^2 := by
  have hn' : (1:ℝ) < N := by exact_mod_cast hn
  have hn0 : (0:ℝ) < N := by linarith
  have hl := Real.log_pos hn'
  have he : 0 < width N s h := by unfold width; positivity
  have bound : 3 * width N s h * M^2 ≤ deltaSq N s := by
    unfold Sbound at H
    nlinarith [mul_nonneg (mul_nonneg he.le (show 0 ≤ 1/4-width N s h by linarith)) (sq_nonneg M)]
  unfold width deltaSq at bound
  field_simp at bound
  exact bound

open scoped Quaternion
/-- This is the zero equation of (1.6) for ONE nonzero eigenvalue,
with δ²=8 and μ²=9. -/
theorem rank_one_roots (q : ℍ[ℝ]) :
    q*(1-q) = (((2/9:ℝ)) : ℍ[ℝ]) ↔
      q = (((1/3:ℝ)) : ℍ[ℝ]) ∨ q = (((2/3:ℝ)) : ℍ[ℝ]) := by
  have eqn : (q-(((1/3:ℝ)):ℍ[ℝ]))*(q-(((2/3:ℝ)):ℍ[ℝ])) =
      (((2/9:ℝ)):ℍ[ℝ]) - q*(1-q) := by
    ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one] <;> ring
  rw [← sub_eq_zero, ← neg_sub, neg_eq_zero, ← eqn, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem separated_spectrum :
    (∀ q : ℍ[ℝ], q*(1-q) = (((2/9:ℝ)):ℍ[ℝ]) → q.re ≤ 1-1/4) ∧
    (∃ q : ℍ[ℝ], q*(1-q) = (((2/9:ℝ)):ℍ[ℝ]) ∧ q.re ≠ 1/2) := by
  constructor
  · intro q h
    rcases (rank_one_roots q).mp h with rfl | rfl <;> rw [Quaternion.re_coe] <;> norm_num
  · refine ⟨(((2/3:ℝ)):ℍ[ℝ]), (rank_one_roots _).mpr (Or.inr rfl), ?_⟩
    rw [Quaternion.re_coe]
    norm_num

end GoldbachSpectral

