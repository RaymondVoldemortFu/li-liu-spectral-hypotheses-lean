module
public import BetaSampling

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ConditionalGoldbach
namespace GoldbachSpectral435

private theorem unrestricted (f : ℝ → ℝ) (hf : FiniteModelWeight f) (v : ℝ → ℝ) :
    (∫ u in Ioi (0:ℝ), f u*v u) = ∫ u, f u*v u := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  rw [hf.eq_zero_of_nonpos (by simpa using hu),zero_mul]

private theorem cross_integrable (f : ℝ → ℝ) (hf : FiniteModelWeight f)
    {v : ℝ → ℝ} (cv : Continuous v) : Integrable (fun u => f u*v u) :=
  (hf.continuous.mul cv).integrable_of_hasCompactSupport (hf.hasCompactSupport.mul_right)

/-- Polarization of the actual signed beta convolution on the half-lattice.
Symmetry is imposed only on the broad weight. -/
theorem half_cross_vanish (f g : ℝ → ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (hfg : FiniteModelWeight (f+g)) (sf : Function.support f ⊆ Ioo (0:ℝ) (1/8))
    (sg : Function.support g ⊆ Ioo (3/8:ℝ) (5/8)) (refl : ∀ u, g (1-u)=g u) (j : ℕ) :
    signedConvolution (f+g) (((j+1:ℕ):ℝ)/2) =
      signedConvolution f (((j+1:ℕ):ℝ)/2) + signedConvolution g (((j+1:ℕ):ℝ)/2) := by
  let y := ((j+1:ℕ):ℝ)/2
  change signedConvolution (f+g) y = _
  have low : 1/2 ≤ y := by dsimp [y]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
  have upoint (u : ℝ) : g u * f (u+y) = 0 := by
    by_contra hz
    obtain ⟨a,b⟩ := mul_ne_zero_iff.mp hz
    linarith [(sg a).1,(sf b).2]
  have balance (u : ℝ) : f u * g (u+y) = f u*g (y-u) := by
    by_cases a : f u = 0
    · simp [a]
    · have h := sf a
      by_cases z : j=0
      · have e : y=1/2 := by simp [y,z]
        rw [e,← refl (u+1/2),show 1-(u+1/2)=1/2-u by ring]
      · have jp : (1:ℝ) ≤ j := by exact_mod_cast (show 1≤j by omega)
        have big : 1 ≤ y := by dsimp [y]; push_cast; linarith
        have e₁ : g (u+y)=0 := by by_contra nz; linarith [(sg nz).2,h.1]
        have e₂ : g (y-u)=0 := by by_contra nz; linarith [(sg nz).2,h.2]
        rw [e₁,e₂]
  let U := fun (F G : ℝ → ℝ) => ∫ u, F u*G (u+y)
  let V := fun (F G : ℝ → ℝ) => ∫ u, F u*G (y-u)
  have transform (F : ℝ → ℝ) (s : FiniteModelWeight F) :
      signedConvolution F y = 2*U F F - V F F := by
    unfold signedConvolution differenceConvolution sumConvolution U V
    rw [unrestricted F s,unrestricted F s]
  have addInt (v : ℝ → ℝ) (cv : Continuous v) :
      (∫ u, (f u+g u)*(f (v u)+g (v u))) =
        ((∫ u, f u*f (v u))+(∫ u, f u*g (v u)))+
        ((∫ u, g u*f (v u))+(∫ u, g u*g (v u))) := by
    have ff := cross_integrable f hf (hf.continuous.comp cv)
    have fg := cross_integrable f hf (hg.continuous.comp cv)
    have gf := cross_integrable g hg (hf.continuous.comp cv)
    have gg := cross_integrable g hg (hg.continuous.comp cv)
    simp only [add_mul,mul_add]
    exact (integral_add (ff.add gf) (fg.add gg)).trans ((congrArg₂ (· + ·) (integral_add ff gf) (integral_add fg gg)).trans (by simp only [Function.comp_apply]; ring))
  have au : U (f+g) (f+g) = (U f f+U f g)+(U g f+U g g) := addInt _ (continuous_id.add_const _)
  have av : V (f+g) (f+g) = (V f f+V f g)+(V g f+V g g) := addInt _ (continuous_const.sub continuous_id)
  have sym : V g f = V f g := by
    change (∫ u, g u*f (y-u)) = ∫ u, f u*g (y-u)
    rw [← integral_sub_left_eq_self (μ := volume) (fun u => g u*f (y-u)) y]
    simp only [sub_sub_cancel]
    simp_rw [mul_comm (g _) (f _)]
  have gu : U g f = 0 := by simp [U,upoint]
  have fu : U f g = V f g := integral_congr_ae (Filter.Eventually.of_forall balance)
  change signedConvolution (f+g) y = signedConvolution f y + signedConvolution g y
  rw [transform _ hfg,transform f hf,transform g hg,au,av,sym,gu,fu]
  ring

#print axioms half_cross_vanish
end GoldbachSpectral435

