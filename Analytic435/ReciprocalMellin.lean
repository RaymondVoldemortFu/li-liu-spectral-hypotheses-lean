module
public import PrimeCharacterCancellation
public import ConditionalGoldbach.Proofs.QuadraticIdentity

/-! Reflection of a compact positive Mellin test across the imaginary
part of a vertical line. Its conjugate has no positive-integer samples
when the original test is supported strictly above one. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex Set Filter MeasureTheory
open scoped ComplexConjugate Topology
namespace GoldbachSpectral435.CriticalCharacter

def mirrorWeight (σ : ℝ) (g : ℝ→ℝ) (u : ℝ) := u^(-2*σ)*g u⁻¹

private lemma mirror_support {g : ℝ→ℝ} {a b : ℝ} (ap : 0<a) (bp : 0<b)
    (ss : Function.support g⊆Icc a b) (σ : ℝ) :
    Function.support (mirrorWeight σ g)⊆Icc b⁻¹ a⁻¹ := by
  intro u h
  have h' : g u⁻¹≠0 := right_ne_zero_of_mul (Function.mem_support.mp h)
  have e := ss (Function.mem_support.mpr h')
  have up : 0<u := inv_pos.mp (ap.trans_le e.1)
  exact ⟨(inv_le_comm₀ bp up).mpr e.2,(le_inv_comm₀ up ap).mpr e.1⟩

private lemma mirror_smooth {g : ℝ→ℝ} {a b : ℝ} (ap : 0<a) (bp : 0<b)
    (ss : Function.support g⊆Icc a b) (sm : ContDiff ℝ 4 g) (σ : ℝ) :
    ContDiff ℝ 4 (mirrorWeight σ g) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases low : u<b⁻¹
  · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds low] with t h
    by_contra nz
    exact (not_le_of_gt h) ((mirror_support ap bp ss σ) (Function.mem_support.mpr nz)).1
  · have up := (inv_pos.mpr bp).trans_le (le_of_not_gt low)
    exact (contDiffAt_id.rpow_const_of_ne up.ne').mul (sm.contDiffAt.comp u (contDiffAt_id.inv (by exact up.ne')))

private lemma mirror_mellin (g : ℝ→ℝ) (σ t : ℝ) :
    mellin (fun u => (mirrorWeight σ g u:ℂ)) (line σ t)=conj (mellin (fun u => (g u:ℂ)) (line σ t)) := by
  let s := line σ t
  let a : ℂ := (-2*σ:ℝ)
  have e : mellin (fun u => (mirrorWeight σ g u:ℂ)) s=
      mellin (fun u : ℝ => (u:ℂ)^a • (g u⁻¹:ℂ)) s := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp only [mirrorWeight,ofReal_mul,ofReal_cpow hu.le,smul_eq_mul,a]
  rw [e,mellin_cpow_smul,mellin_comp_inv (fun u => (g u:ℂ)) (s+a)]
  have eq : -(s+a)=conj s := by
    apply Complex.ext <;> dsimp [s,a,line] <;> simp
    ring
  rw [eq]
  unfold mellin
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [smul_eq_mul,map_mul,conj_ofReal]
  rw [← ofReal_cpow_conj u hu,map_sub,map_one]

/-- An analytic logarithmic derivative annihilates the reflected
frequency of a test supported at physical arguments greater than one. -/
theorem conjugate_sampling_zero {q : ℕ} [NeZero q] (q4 : 4≤q) (grh : GRH q)
    (χ : Character q) (nc : χ≠1) (M : ℕ) (qm : q≤M) (f : ℝ→ℝ) (hf : FiniteModelWeight f)
    (large : 1<(M:ℝ)*hf.lower) (σ : ℝ) (sp : 0<σ) (s1 : σ≤1) :
    let W := fun s : ℂ => (M:ℂ)^s*mellin (fun u => (companion f u:ℂ)) s
    Integrable (fun t => conj (W (line σ t))*logDerivative χ (line σ t)) ∧
    (∫ t : ℝ,conj (W (line σ t))*logDerivative χ (line σ t))=0 := by
  intro W
  let m : ℝ := M
  have mp : 0<m := Nat.cast_pos.mpr (show 0<M by omega)
  let g := fun u : ℝ => companion f (m⁻¹*u)
  let a := m*hf.lower
  let b := m*hf.upper
  have ap : 0<a := zero_lt_one.trans large
  have bp : 0<b := mul_pos mp (hf.lower_pos.trans_le hf.lower_le_upper)
  have supp : Function.support g⊆Icc a b := by
    intro u hu
    have v := FiniteModel.companion_support_subset hf hu
    change hf.lower≤m⁻¹*u ∧ m⁻¹*u≤hf.upper at v
    constructor
    · simpa only [mul_inv_cancel_left₀ mp.ne'] using mul_le_mul_of_nonneg_left v.1 mp.le
    · simpa only [mul_inv_cancel_left₀ mp.ne'] using mul_le_mul_of_nonneg_left v.2 mp.le
  have gsm : ContDiff ℝ 4 g := ((FiniteModel.companion_contDiff hf).of_le (by norm_num)).comp
    (contDiff_const.mul contDiff_id)
  let h := mirrorWeight σ g
  let v := fun u : ℝ => h (m*u)
  have hsup := mirror_support ap bp supp σ
  have vs : Function.support v⊆Icc (b⁻¹/m) (a⁻¹/m) := by
    intro u hu
    have bound := hsup hu
    exact ⟨(div_le_iff₀ mp).mpr (by simpa only [mul_comm u m] using bound.1),
      (le_div_iff₀ mp).mpr (by simpa only [mul_comm u m] using bound.2)⟩
  have vsmooth : ContDiff ℝ 4 v := (mirror_smooth ap bp supp gsm σ).comp (contDiff_const.mul contDiff_id)
  obtain ⟨hi,ev⟩ := nonprincipal_sampling q4 grh χ nc M qm v vsmooth vs σ sp s1
  have zero (i : ℕ) : v ((i+1:ℕ)/(M:ℝ))=0 := by
    by_contra nz
    have z := (vs (Function.mem_support.mpr nz)).2
    have up : ((i+1:ℕ):ℝ)≤a⁻¹ := (div_le_div_iff_of_pos_right mp).mp z
    have lt : a⁻¹<1 := inv_lt_one_of_one_lt₀ large
    have ge : (1:ℝ)≤(i+1:ℕ) := by exact_mod_cast Nat.succ_pos i
    linarith
  simp_rw [zero,ofReal_zero,mul_zero,tsum_zero,neg_zero] at ev
  have formula (t : ℝ) : (M:ℂ)^(line σ t)*mellin (fun u => (v u:ℂ)) (line σ t)=conj (W (line σ t)) := by
    let s := line σ t
    have hg : mellin (fun u => (g u:ℂ)) s=W s := by
      change mellin (fun u : ℝ => (companion f (m⁻¹*u):ℂ)) s=_
      rw [mellin_comp_mul_left (fun u => (companion f u:ℂ)) s (inv_pos.mpr mp),
        smul_eq_mul,ofReal_inv,Complex.inv_cpow _ _ (by simpa only [arg_ofReal_of_nonneg mp.le] using Real.pi_ne_zero.symm),Complex.cpow_neg]
      simp [W,m]
    change (M:ℂ)^s*mellin (fun u : ℝ => (h (m*u):ℂ)) s=_
    rw [mellin_comp_mul_left (fun u => (h u:ℂ)) s mp,smul_eq_mul,Complex.cpow_neg]
    have nz : (m:ℂ)^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr mp.ne'))
    rw [← ofReal_natCast M]
    change (m:ℂ)^s*(((m:ℂ)^s)⁻¹*mellin (fun u => (h u:ℂ)) s)=_
    rw [mul_inv_cancel_left₀ nz]
    exact (mirror_mellin g σ t).trans (congrArg _ hg)
  change Integrable (fun t => ((M:ℂ)^(line σ t)*mellin (fun u => (v u:ℂ)) (line σ t))*logDerivative χ (line σ t)) at hi
  unfold verticalMellin at ev
  simp_rw [formula] at hi ev
  refine ⟨hi,?_⟩
  exact (mul_eq_zero.mp ev).resolve_left (inv_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)))

#print axioms conjugate_sampling_zero
end GoldbachSpectral435.CriticalCharacter
