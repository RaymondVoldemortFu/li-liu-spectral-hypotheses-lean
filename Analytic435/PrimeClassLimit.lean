module
public import MixedPrimeLimit

/-! Uniform one-prime mass in every invertible class of the cutoff
primorial, after restoring the Euler totient normalization. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve

def classAverage (q M : ℕ) (t : ZMod q) (f : ℝ→ℝ) :=
  (q.totient:ℝ)*classMass q M t f/M

private lemma fourth_bound {N M : ℕ} (np : 0<N) (nm : N≤M) :
    (primorial (localCutoff N):ℝ)^4≤(M:ℝ)^(1/8:ℝ) := by
  have a := (primorial_cutoff_power N np).trans (Nat.cast_le.mpr nm)
  have h := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) 32) a (by norm_num : (0:ℝ)≤1/8)
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _)] at h
  norm_num at h ⊢
  exact h

theorem class_average_limit (f : ℝ→ℝ) (hf : FiniteModelWeight f) (ε : ℝ) (ep : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, N≤M → GRH (primorial (localCutoff N)) →
      ∀ t : ZMod (primorial (localCutoff N)), IsUnit t →
      |classAverage (primorial (localCutoff N)) M t f-(∫ u in (0:ℝ)..1,f u)|≤ε := by
  obtain ⟨C,cp,ap⟩ := physical_AP f hf
  have growth := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have lim : Tendsto (fun M : ℕ => C/(M:ℝ)^(1/8:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop growth
  obtain ⟨K,k⟩ := eventually_atTop.mp ((uniform_principal f hf (ε/2) (half_pos ep)).and
    (lim.eventually_lt_const (half_pos ep)))
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop (1:ℕ),cutoff_grows.eventually_ge_atTop 3] with N nk np zz
  intro M nm grh t unit
  let Q := primorial (localCutoff N)
  have qp : (1:ℝ)≤Q := Nat.one_le_cast.mpr (primorial_pos _)
  have fp : 0<(Q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (primorial_pos _))
  have mp : 0<M := np.trans nm
  have mr : 0<(M:ℝ) := Nat.cast_pos.mpr mp
  have q4 : 4≤Q := (by decide : 4≤primorial 3).trans (primorial_mono zz)
  have power := fourth_bound np nm
  have qsq : (Q:ℝ)^2≤M := (pow_le_pow_right₀ qp (by decide : 2≤32)).trans
    ((primorial_cutoff_power N np).trans (Nat.cast_le.mpr nm))
  have qle := (Real.le_sqrt (Nat.cast_nonneg Q) mr.le).mpr qsq
  have raw := ap Q q4 grh M mp t unit
  let U := principalMass Q M f
  have up := (k M (nk.trans nm)).1 Q (primorial_pos _) qle
  have er : |classAverage Q M t f-U/M|≤C/(M:ℝ)^(1/8:ℝ) := by
    have rewrite : classAverage Q M t f-U/M=(Q.totient:ℝ)/M*(classMass Q M t f-U/Q.totient) := by
      unfold classAverage
      field_simp
    rw [rewrite,abs_mul,abs_of_pos (div_pos fp mr)]
    apply (mul_le_mul_of_nonneg_left raw (div_nonneg fp.le mr.le)).trans
    apply (le_div_iff₀ (Real.rpow_pos_of_pos mr (1/8:ℝ))).mpr
    have ph : (Q.totient:ℝ)≤Q := Nat.cast_le.mpr (Nat.totient_le Q)
    have qpow : (Q.totient:ℝ)*(Q:ℝ)^2≤(M:ℝ)^(1/8:ℝ) := calc
      _ ≤ (Q:ℝ)*Q^2 := mul_le_mul_of_nonneg_right ph (sq_nonneg _)
      _ = (Q:ℝ)^3 := by ring
      _ ≤ (Q:ℝ)^4 := pow_le_pow_right₀ qp (by decide : 3≤4)
      _ ≤ _ := power
    rw [Real.sqrt_eq_rpow]
    have e : (M:ℝ)^(1/2:ℝ)*(M:ℝ)^(1/4:ℝ)*(M:ℝ)^(1/8:ℝ)*(M:ℝ)^(1/8:ℝ)=M := by
      rw [← Real.rpow_add mr,← Real.rpow_add mr,← Real.rpow_add mr]
      norm_num
    calc
      _ = C/M*((M:ℝ)^(1/2:ℝ)*(M:ℝ)^(1/4:ℝ)*(M:ℝ)^(1/8:ℝ))*((Q.totient:ℝ)*Q^2) := by ring
      _ ≤ C/M*((M:ℝ)^(1/2:ℝ)*(M:ℝ)^(1/4:ℝ)*(M:ℝ)^(1/8:ℝ))*(M:ℝ)^(1/8:ℝ) := by gcongr
      _ = _ := by rw [mul_assoc (C/M),e,div_mul_cancel₀ _ mr.ne']
  exact (abs_sub_le _ (U/M) _).trans (by linarith only [er,up,(k M (nk.trans nm)).2])

#print axioms class_average_limit
end GoldbachSpectral435.GoldbachSieve
