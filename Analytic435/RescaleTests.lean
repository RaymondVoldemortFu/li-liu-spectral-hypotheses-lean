module
public import PhysicalDensity
public import FiniteDiscrepancy

/-! Real linear combinations and changes of scale of compact Mellin tests. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PhysicalTests

def inflate (r : ℝ) (f : ℝ→ℝ) (u : ℝ) := Real.sqrt r*f (r*u)

def inflated {r : ℝ} (hr : 1≤r) {f : ℝ→ℝ} (hf : FiniteModelWeight f) :
    FiniteModelWeight (inflate r f) := by
  have rp := zero_lt_one.trans_le hr
  refine ⟨contDiff_const.mul (hf.smooth.comp (contDiff_const.mul contDiff_id)),hf.lower/r,hf.upper/r,
    div_pos hf.lower_pos rp,(div_lt_one rp).mpr (hf.upper_lt_one.trans_le hr),
    div_le_div_of_nonneg_right hf.lower_le_upper rp.le,?_⟩
  intro u hu
  obtain ⟨lo,hi⟩ := hf.mem_support_interval (mul_ne_zero_iff.mp hu).2
  exact ⟨(div_le_iff₀ rp).mpr (by linarith only [lo]),(le_div_iff₀ rp).mpr (by linarith only [hi])⟩

private lemma inflate_companion {r : ℝ} (rp : 0≤r) (f : ℝ→ℝ) (u : ℝ) :
    companion (inflate r f) u=companion f (r*u) := by
  unfold companion inflate
  rw [Real.sqrt_mul rp]
  ring

/-- Enlarging the sampling scale and rescaling the weight preserves the
actual original Riesz vector. -/
theorem enlarge (N M P : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) (mp : 0<M) (le : M≤P)
    (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let r := (P:ℝ)/M
    ∃ hg : FiniteModelWeight (inflate r f), testVector N P (mp.trans_le le) (inflate r f) hg =
      testVector N M mp f hf := by
  intro r
  have mr : 0<(M:ℝ) := by exact_mod_cast mp
  have pr : 0<(P:ℝ) := by exact_mod_cast mp.trans_le le
  have hr : 1≤r := (one_le_div mr).mpr (Nat.cast_le.mpr le)
  let hg := inflated hr hf
  refine ⟨hg,?_⟩
  let σ : ℝ := 1/9
  have sp : 0<σ := by norm_num [σ]
  have nr : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have lg := (Real.lt_log_iff_exp_lt nr).mpr big
  have ab : σ∈Ioo (alpha N) beta :=
    ⟨one_div_lt_one_div_of_lt (by norm_num) (by linarith),by norm_num [σ,beta]⟩
  apply ext_inner_right ℂ
  intro v
  change paperInner v _=paperInner v _
  rw [← testVector_rep N P _ _ hg σ sp ab v,← testVector_rep N M _ _ hf σ sp ab v]
  unfold finiteFunctionalValue verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  let s := line σ t
  have mell : mellin (fun u => (companion (inflate r f) u:ℂ)) s =
      (r:ℂ)^(-s)*mellin (fun u => (companion f u:ℂ)) s := by
    simp_rw [inflate_companion (zero_le_one.trans hr)]
    exact mellin_comp_mul_left (fun u : ℝ => (companion f u:ℂ)) s (zero_lt_one.trans_le hr)
  have q (a : ℕ) (p : 0<a) : (a:ℂ)^s≠0 := cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast p.ne'))
  have pow : (r:ℂ)^(-s)=((P:ℂ)^s/(M:ℂ)^s)⁻¹ := by
    dsimp [r]
    rw [Complex.cpow_neg,Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg pr.le mr.le,
      Complex.ofReal_natCast,Complex.ofReal_natCast]
  change (P:ℂ)^s*mellin (fun u => (companion (inflate r f) u:ℂ)) s*(1+s)*fourierLaplace v s=
    (M:ℂ)^s*mellin (fun u => (companion f u:ℂ)) s*(1+s)*fourierLaplace v s
  rw [mell,pow]
  field_simp [q M mp,q P (mp.trans_le le)]

def AtScale (N M : ℕ) (mp : 0<M) (x : HardySpace (alpha N) beta) : Prop :=
  ∃ (f : ℝ→ℝ) (hf : FiniteModelWeight f), x=testVector N M mp f hf

theorem atScale_mono (N M P : ℕ) [NeZero N] (big : Real.exp 10<(N:ℝ)) (mp : 0<M) (le : M≤P)
    {x : HardySpace (alpha N) beta} (hx : AtScale N M mp x) : AtScale N P (mp.trans_le le) x := by
  obtain ⟨f,hf,rfl⟩ := hx
  obtain ⟨hg,eq⟩ := enlarge N M P big mp le f hf
  exact ⟨_,hg,eq.symm⟩

#print axioms enlarge
end GoldbachSpectral435.PhysicalTests
