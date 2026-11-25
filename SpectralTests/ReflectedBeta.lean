module
public import SpectralTests.Transfer
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section
namespace GoldbachSpectral
open MeasureTheory Set

/-- The signed convolution on the separated supports, extended to the real line. -/
noncomputable def reflectedBeta (f g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u, f u * (g (y+u) - g (y-u))

theorem reflectedBeta_odd (f g : ℝ → ℝ) (hg : ∀ x, g (2-x) = g x) (y : ℝ) :
    reflectedBeta f g (2-y) = -reflectedBeta f g y := by
  unfold reflectedBeta
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show 2-y+u = 2-(y-u) by ring, show 2-y-u = 2-(y+u) by ring,
    hg (y-u), hg (y+u)]
  ring

theorem reflectedBeta_mass (f g : ℝ → ℝ) (hg : ∀ x, g (2-x) = g x) :
    (∫ y, reflectedBeta f g y) = 0 := by
  let J := reflectedBeta f g
  have inv : (∫ y : ℝ, J (2-y)) = ∫ y : ℝ, J y :=
    integral_sub_left_eq_self J volume 2
  have anti : (∫ y : ℝ, J (2-y)) = -(∫ y : ℝ, J y) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall (reflectedBeta_odd f g hg))
  change (∫ y : ℝ, J y) = 0
  linarith

/-- Vanishing of the signed model outside its compact positive physical interval. -/
theorem reflectedBeta_support (f g : ℝ → ℝ)
    (hf : ∀ u, f u ≠ 0 → u ∈ Ioo (0:ℝ) (1/10))
    (hg : ∀ u, g u ≠ 0 → u ∈ Ioo (4/5:ℝ) (6/5)) :
    Function.support (reflectedBeta f g) ⊆ Ioo (7/10:ℝ) (13/10) := by
  intro y hy
  by_contra nope
  apply hy
  unfold reflectedBeta
  have zeroed : (fun u => f u * (g (y+u)-g (y-u))) = 0 := by
    funext u
    by_cases hfu : f u = 0
    · simp [hfu]
    obtain ⟨u0,u1⟩ := hf u hfu
    have z₁ : g (y+u) = 0 := by
      by_contra h
      obtain ⟨l,r⟩ := hg _ h
      exact nope ⟨by linarith,by linarith⟩
    have z₂ : g (y-u) = 0 := by
      by_contra h
      obtain ⟨l,r⟩ := hg _ h
      exact nope ⟨by linarith,by linarith⟩
    simp [z₁,z₂]
  rw [zeroed]
  simp

end GoldbachSpectral
