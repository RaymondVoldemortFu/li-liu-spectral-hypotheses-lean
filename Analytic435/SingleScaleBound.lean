module
public import SingleScaleDensity
public import FirstBlockBound

/-! The finite sum estimate at one scale controls all vectors in the entire
compressed Hilbert space of that scale. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Filter
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PhysicalTests
open FiniteDiscrepancy

private lemma span_decomposition {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : Set H) (zero : (0:H)∈S) (add : ∀ {x y : H}, x∈S → y∈S → x+y∈S)
    (scale : ∀ r : ℝ, ∀ {x : H}, x∈S → (r:ℂ) • x∈S) {z : H} (hz : z∈Submodule.span ℂ S) :
    ∃ x∈S, ∃ y∈S, z=x+Complex.I • y := by
  induction hz using Submodule.span_induction with
  | mem v hv => exact ⟨v,hv,0,zero,by simp⟩
  | zero => exact ⟨0,zero,0,zero,by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u,hu,v,hv,rfl⟩ := hx
    obtain ⟨s,hs,t,ht,rfl⟩ := hy
    exact ⟨u+s,add hu hs,v+t,add hv ht,by rw [smul_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨x,hx,y,hy,rfl⟩ := hx
    refine ⟨(c.re:ℂ) • x+((-c.im:ℝ):ℂ) • y,add (scale _ hx) (scale _ hy),
      (c.im:ℂ) • x+(c.re:ℂ) • y,add (scale _ hx) (scale _ hy),?_⟩
    have a : (c.re:ℂ)+Complex.I*(c.im:ℂ)=c := by simpa only [mul_comm Complex.I] using Complex.re_add_im c
    have b : ((-c.im:ℝ):ℂ)+Complex.I*(c.re:ℂ)=c*Complex.I := by
      apply Complex.ext <;> simp
    rw [smul_add,smul_smul,smul_add,smul_smul,smul_smul]
    calc
      _ = ((c.re:ℂ) • x+(Complex.I*(c.im:ℂ)) • x)+
          (((-c.im:ℝ):ℂ) • y+(Complex.I*(c.re:ℂ)) • y) := by rw [← add_smul,← add_smul,a,b]
      _ = _ := by abel

def ScaleBound (N k : ℕ) (B : ℝ) : Prop := ∀ (f : ℝ→ℝ), FiniteModelWeight f →
  ‖arithmetic N (k*N) f-continuousModel N k f‖≤ B*normFunctional (k*N) f (alpha N)

/-- A single real-weight inequality controls the whole complex half-line
block with the same constant, including vectors meeting the left edge. -/
theorem block_bound (N k : ℕ) [NeZero N] (kp : 0<k) (ev : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (B : ℝ) (cap : ScaleBound N k B)
    (z : HardySpace (alpha N) beta)
    (support : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log (k*N:ℕ) → z t=0) :
    ‖inner ℂ z (residualOperator ha N z)‖≤B*‖z‖^2 := by
  let M := k*N
  have mp : 0<M := Nat.mul_pos kp (NeZero.pos N)
  let S := {x | AtScale N M mp x}
  let T := residualOperator ha N
  have incl {x} (hx : x∈S) : x∈tests N := ⟨k,kp,hx⟩
  have realcap {x} (hx : x∈S) : ‖inner ℂ x (T x)‖≤B*‖x‖^2 := by
    obtain ⟨f,hf,rfl⟩ := hx
    obtain ⟨n,d⟩ := exact_form N k kp ev big g ha f hf
    change ‖paperInner (T _) _‖≤_
    rw [d,n]
    exact cap f hf
  have closed : IsClosed {x | ‖inner ℂ x (T x)‖≤B*‖x‖^2} := by apply isClosed_le <;> fun_prop
  have h : z∈closure (↑(Submodule.span ℂ S) : Set (HardySpace (alpha N) beta)) :=
    single_scale_density N M mp big z support
  apply (closure_minimal (t:={x | ‖inner ℂ x (T x)‖≤B*‖x‖^2}) _ closed) h
  intro w hw
  obtain ⟨x,hx,y,hy,rfl⟩ := span_decomposition S (atScale_zero N M mp big)
    (atScale_add N M mp big) (atScale_smul N M mp big) hw
  obtain ⟨form,nrm⟩ := real_splits N ev big g ha x y (incl hx) (incl hy)
  change ‖inner ℂ (x+Complex.I • y) (T (x+Complex.I • y))‖≤ B*‖x+Complex.I • y‖^2
  rw [form,nrm,mul_add]
  exact (norm_add_le _ _).trans (add_le_add (realcap hx) (realcap hy))

/-- In the first block a finite mesh controls every complex vector supported
in physical time above -log N. -/
theorem first_block_mesh (N m : ℕ) [NeZero N] (ev : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (mp : 0<m) (D : ℝ)
    (mesh : ∀ j : ℕ, j≤m → |GoldbachPrimitive.primitive N (j/(m:ℝ))|≤D)
    (x : HardySpace (alpha N) beta) (support : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log N → x t=0) :
    ‖inner ℂ x (residualOperator ha N x)‖≤
      576*Real.pi*(D+singularSeries N/m+singularSeries N/N)*‖x‖^2 := by
  apply block_bound N 1 zero_lt_one ev big grh ha _ _ x (by simpa only [one_mul] using support)
  intro f hf
  obtain ⟨n,e⟩ := exact_form N 1 zero_lt_one ev big grh ha f hf
  rw [← e,← n]
  simpa only [one_mul] using GoldbachPrimitive.first_scale_mesh N m ev big grh ha mp D mesh f hf

#print axioms block_bound
#print axioms first_block_mesh
end GoldbachSpectral435.PhysicalTests
