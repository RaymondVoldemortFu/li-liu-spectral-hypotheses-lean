module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace GoldbachSpectral
open Set Filter
open scoped Topology

/-- The delay equation and initial values used in the Buchstab-density argument. -/
structure BuchstabData (ω : ℝ → ℝ) : Prop where
  initial : ∀ t ∈ Ioo (1:ℝ) 2, ω t = 1/t
  delay : ∀ t : ℝ, 2 < t → HasDerivAt ω ((ω (t-1)-ω t)/t) t

private theorem propagate_constant {ω : ℝ → ℝ} (B : BuchstabData ω) (C : ℝ) (k : ℕ) :
    (∀ t : ℝ, (k:ℝ)+1 < t → ω t = C) → ∀ t : ℝ, 1 < t → ω t = C := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro tail
    apply ih
    intro t ht
    have h₂ : ((k+1:ℕ):ℝ)+1 < t+1 := by push_cast; linarith
    have he : ω =ᶠ[𝓝 (t+1)] (fun _ => C) :=
      (eventually_gt_nhds h₂).mono (fun u hu => tail u hu)
    have hz := (hasDerivAt_const (t+1) C).congr_of_eventuallyEq he
    have hh := (B.delay (t+1) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)).unique hz
    rw [add_sub_cancel_right, div_eq_zero_iff] at hh
    rcases hh with h | h
    · linarith [tail (t+1) h₂]
    · have := Nat.cast_nonneg (α := ℝ) k
      linarith

/-- Positive signs ω(u)-ω(u+1) occur at arbitrarily large real arguments. -/
theorem buchstab_drop {ω : ℝ → ℝ} (B : BuchstabData ω) (A : ℝ) :
    ∃ u : ℝ, A < u ∧ ω (u+1) < ω u := by
  by_contra! no
  let c := max A 2 + 2
  have hA : A+1 < c := by dsimp [c]; linarith [le_max_left A 2]
  have hc : 2 < c := by dsimp [c]; linarith [le_max_right A 2]
  have hd (u : ℝ) (hu : c < u) := B.delay u (hc.trans hu)
  have anti : AntitoneOn ω (Ioi c) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi c)
    · intro u hu
      exact (hd u hu).continuousAt.continuousWithinAt
    · rw [isOpen_Ioi.interior_eq]
      intro u hu
      exact (hd u hu).differentiableAt.differentiableWithinAt
    · rw [isOpen_Ioi.interior_eq]
      intro u hu
      have hu' : c < u := hu
      rw [(hd u hu).deriv]
      have h := no (u-1) (by linarith)
      rw [sub_add_cancel] at h
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have mono : MonotoneOn ω (Ioi (c+1)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
    · intro u hu
      exact (hd u (by have : c+1 < u := hu; linarith)).continuousAt.continuousWithinAt
    · rw [isOpen_Ioi.interior_eq]
      intro u hu
      exact (hd u (by have : c+1 < u := hu; linarith)).differentiableAt.differentiableWithinAt
    · rw [isOpen_Ioi.interior_eq]
      intro u hu
      have hu' : c+1 < u := hu
      have h := anti (a := u-1) (b := u) (by change c < u-1; linarith)
        (by change c < u; linarith) (by linarith)
      rw [(hd u (by linarith)).deriv]
      exact div_nonneg (by linarith) (by linarith)
  obtain ⟨k,hk⟩ := exists_nat_gt (c+2)
  have tail (t : ℝ) (ht : (k:ℝ)+1 < t) : ω t = ω (k:ℝ) :=
    le_antisymm (anti (by change c < (k:ℝ); linarith) (by change c < t; linarith) (by linarith))
      (mono (by change c+1 < (k:ℝ); linarith) (by change c+1 < t; linarith) (by linarith))
  have h₁ := propagate_constant B _ k tail (4/3) (by norm_num)
  have h₂ := propagate_constant B _ k tail (3/2) (by norm_num)
  rw [B.initial _ (by constructor <;> norm_num)] at h₁ h₂
  norm_num at h₁ h₂
  linarith

end GoldbachSpectral

