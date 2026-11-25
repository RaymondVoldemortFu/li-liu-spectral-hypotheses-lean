module
public import SpectralTests.Widths
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section
namespace GoldbachSpectral
open Set Module
open scoped Quaternion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Exactly one index for each copy of a nonzero real eigenvalue. -/
def Mode (T : E →L[ℂ] E) := (r : {r : ℝ // r ≠ 0}) ×
  Fin (Module.finrank ℂ (Module.End.eigenspace T.toLinearMap (r.val : ℂ)))

/-- Intrinsic extension of the slice product (1.6).  The imaginary direction
of the argument fixes the complex slice, and all the coefficients are real. -/
noncomputable def spectralX (T : E →L[ℂ] E) (D : ℝ) (q : ℍ[ℝ]) : ℍ[ℝ] :=
  let v := Real.sqrt (q.imI^2+q.imJ^2+q.imK^2)
  let z : ℂ := ⟨q.re,v⟩
  let p := ∏' i : Mode T, (1 - ((4*i.1.val^2/D : ℝ):ℂ) * z * (1-z))
  ⟨p.re,p.im*q.imI/v,p.im*q.imJ/v,p.im*q.imK/v⟩

private theorem real_factor_zero {T : E →L[ℂ] E} {r D : ℝ}
    (i : Mode T) (hD : 0 < D) (hr : 4*i.1.val^2*r*(1-r) = D) :
    spectralX T D (r : ℍ[ℝ]) = 0 := by
  have eqn : 1-(4*i.1.val^2/D)*r*(1-r) = 0 := by field_simp; linarith
  have hz : (1-((4*i.1.val^2/D:ℝ):ℂ)*(r:ℂ)*(1-(r:ℂ))) = 0 := by exact_mod_cast eqn
  have hp : (∏' j : Mode T, (1-((4*j.1.val^2/D:ℝ):ℂ)*(r:ℂ)*(1-(r:ℂ)))) = 0 :=
    (hasProd_zero_of_exists_eq_zero ⟨i,hz⟩).tprod_eq
  unfold spectralX
  simp only [Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add, Real.sqrt_zero]
  change (QuaternionAlgebra.mk (re := (∏' j : Mode T, (1-((4*j.1.val^2/D:ℝ):ℂ)*(r:ℂ)*(1-(r:ℂ)))).re)
    _ _ _ : ℍ[ℝ]) = 0
  rw [hp]
  ext <;> simp

variable [CompleteSpace E]

private theorem extremal_mode (T : E →L[ℂ] E) (comp : IsCompactOperator T)
    (symm : T.IsSymmetric) (nz : ‖T‖ ≠ 0) : ∃ i : Mode T, i.1.val^2 = ‖T‖^2 := by
  let : Nontrivial (E →L[ℂ] E) := nontrivial_of_ne T 0 (norm_ne_zero_iff.mp nz)
  have choice : ∃ r : ℝ, r ∈ spectrum ℝ T ∧ r ≠ 0 ∧ r^2 = ‖T‖^2 := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum T symm.isSelfAdjoint with h | h
    · exact ⟨_,h,nz,rfl⟩
    · exact ⟨_,h,neg_ne_zero.mpr nz,by ring⟩
  obtain ⟨r,hr,hn,hs⟩ := choice
  have hC : (r:ℂ) ≠ 0 := by exact_mod_cast hn
  have hc : (r:ℂ) ∈ spectrum ℂ T := spectrum.algebraMap_mem ℂ hr
  have he := (comp.hasEigenvalue_iff_mem_spectrum hC).mpr hc
  let : FiniteDimensional ℂ (Module.End.eigenspace T.toLinearMap (r:ℂ)) :=
    T.finite_dimensional_eigenspace comp _ hC
  let : Nontrivial (Module.End.eigenspace T.toLinearMap (r:ℂ)) :=
    Submodule.nontrivial_iff_ne_bot.mpr (Module.End.hasEigenvalue_iff.mp he)
  exact ⟨⟨⟨r,hn⟩,⟨0, Module.finrank_pos⟩⟩,hs⟩

/-- Strict violation produces a REAL zero in the open interval (1-η,1). -/
theorem real_zero_of_norm {T : E →L[ℂ] E} (comp : IsCompactOperator T)
    (symm : T.IsSymmetric) {D η : ℝ} (hD : 0 < D) (he : 0 < η) (_he' : η < 1/2)
    (hbad : D < 4*η*(1-η)*‖T‖^2) :
    ∃ r ∈ Ioo (1-η) 1, spectralX T D (r:ℍ[ℝ]) = 0 := by
  have nz : ‖T‖ ≠ 0 := by intro h; rw [h] at hbad; linarith
  obtain ⟨i,hi⟩ := extremal_mode T comp symm nz
  let F := fun r : ℝ => 4*i.1.val^2*r*(1-r)
  have hf : Continuous F := by dsimp [F]; fun_prop
  have hlo : F 1 < D := by simpa [F] using hD
  have hhi : D < F (1-η) := by dsimp [F]; rw [hi]; nlinarith [hbad]
  obtain ⟨r,hr,hroot⟩ := intermediate_value_Ioo' (show 1-η ≤ 1 by linarith) hf.continuousOn ⟨hlo,hhi⟩
  exact ⟨r,hr,real_factor_zero i hD hroot⟩

end GoldbachSpectral

