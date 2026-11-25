module
public import SpectralTests.RowChange
public import SpectralTests.PrimeProgression
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
noncomputable section
namespace GoldbachSpectral.BandSieve
open Finset Set ArithmeticFunction
open scoped ContDiff

def inner : ContDiffBump (5/2:ℝ) := ⟨1/2,3/2,by norm_num,by norm_num⟩
def outer : ContDiffBump (3/2:ℝ) := ⟨1/8,1/2,by norm_num,by norm_num⟩
def wfun (H : ℝ) (h : ℕ) : ℝ := inner ((h:ℝ)/H)
def vfun (P : ℝ) (m : ℕ) : ℝ := if Odd m then vonMangoldt m*outer ((m:ℝ)/P) else 0
def shape (a H P : ℝ) (x : ℝ) : ℝ := inner ((x-a)/H)*outer (x/P)

theorem sample_data {P H : ℕ} (pp : 4≤P) (hp : 0<H) :
    (∀ i,0≤wfun H i) ∧ (∀ m,0≤vfun P m) ∧
    (∀ i : ℕ, 2 * H ≤ i → i ≤ 3 * H → 1 ≤ wfun H i) ∧
    (∀ m : ℕ, m.Prime → 7*P≤5*m → 5*m≤8*P → Real.log m≤vfun P m) ∧
    (∑ m∈Finset.Icc P (2*P),vfun P m) ≤ (P+1:ℝ)*Real.log (2*P) := by
  have ph : 0<(P:ℝ) := by exact_mod_cast (show 0<P by omega)
  have hh : 0<(H:ℝ) := by exact_mod_cast hp
  refine ⟨fun _ => inner.nonneg,?_,?_,?_,?_⟩
  · intro m
    unfold vfun
    split
    · exact mul_nonneg vonMangoldt_nonneg outer.nonneg
    · exact le_rfl
  · intro i h1 h2
    unfold wfun
    apply le_of_eq
    symm
    apply inner.one_of_mem_closedBall
    rw [Metric.mem_closedBall,Real.dist_eq,abs_le]
    change -(1/2:ℝ) ≤ i/H-5/2 ∧ (i:ℝ)/H-5/2≤1/2
    have x : 2≤(i:ℝ)/H := (le_div_iff₀ hh).mpr (by exact_mod_cast h1)
    have y : (i:ℝ)/H≤3 := (div_le_iff₀ hh).mpr (by exact_mod_cast h2)
    constructor <;> linarith
  · intro m pr h1 h2
    have od := pr.odd_of_ne_two (by omega)
    rw [vfun,ite_eq_left od,vonMangoldt_apply_prime pr,outer.one_of_mem_closedBall, mul_one]
    rw [Metric.mem_closedBall,Real.dist_eq,abs_le]
    change -(1/8:ℝ) ≤ m/P-3/2 ∧ (m:ℝ)/P-3/2≤1/8
    have x : 7/5≤(m:ℝ)/P := (le_div_iff₀ ph).mpr (by
      have a : 7*(P:ℝ)≤5*m := by exact_mod_cast h1
      linarith)
    have y : (m:ℝ)/P≤8/5 := (div_le_iff₀ ph).mpr (by
      have a : 5*(m:ℝ)≤8*P := by exact_mod_cast h2
      linarith)
    constructor <;> linarith
  · have est (m : ℕ) (hm : m∈Finset.Icc P (2*P)) : vfun P m ≤ Real.log (2*(P:ℝ)) := by
      obtain ⟨l,r⟩ := Finset.mem_Icc.mp hm
      have lg := Real.log_le_log (by exact_mod_cast (show 0<m by omega)) (by exact_mod_cast r : (m:ℝ)≤2*P)
      unfold vfun
      split
      · exact (mul_le_of_le_one_right vonMangoldt_nonneg outer.le_one).trans (vonMangoldt_le_log.trans lg)
      · exact Real.log_nonneg (by linarith [show (4:ℝ)≤P by exact_mod_cast pp])
    have sum := Finset.sum_le_sum est
    simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc] at sum
    simpa only [show 2*P+1-P=P+1 by omega,Nat.cast_add,Nat.cast_one] using sum

theorem variation_bound :
    ∃ D : ℝ, 0<D ∧ ∀ H : ℕ, 0<H →
      let L := 4*H+1
      2*(|wfun H L|+∑ i∈range L,|wfun H i-wfun H (i+1)|) ≤ D := by
  have sm : ContDiff ℝ ∞ (inner : ℝ → ℝ) := inner.contDiff
  obtain ⟨C,B⟩ := (sm.continuous_deriv (by simp)).bounded_above_of_compact_support inner.hasCompactSupport.deriv
  have cp : 0≤C := (abs_nonneg _).trans (B 0)
  refine ⟨2*(1+5*C),by positivity,?_⟩
  intro H hp L
  have hh : 0<(H:ℝ) := by exact_mod_cast hp
  have step (i : ℕ) (_hi : i∈range L) : |wfun H i-wfun H (i+1)| ≤ C/(H:ℝ) := by
    have bound := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => sm.differentiable (by simp) x) (fun x _ => B x)
      (Set.mem_univ (((i+1:ℕ):ℝ)/H)) (Set.mem_univ ((i:ℝ)/H))
    simp only [Real.norm_eq_abs, Nat.cast_add,Nat.cast_one] at bound
    have eqn : (i:ℝ)/H-(i+1)/H=-(1/(H:ℝ)) := by ring
    simpa only [wfun,Nat.cast_add,Nat.cast_one,eqn,abs_neg,abs_of_nonneg (one_div_nonneg.mpr hh.le),mul_one_div] using bound
  have sum := Finset.sum_le_sum step
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at sum
  have lc : (L:ℝ) ≤ 5*H := by exact_mod_cast (show L≤5*H by dsimp [L]; omega)
  have s := mul_le_mul_of_nonneg_right lc (div_nonneg cp hh.le)
  have eqn : 5*(H:ℝ)*(C/H)=5*C := by field_simp
  have small : |wfun H L|≤1 := by rw [wfun,abs_of_nonneg inner.nonneg]; exact inner.le_one
  linarith

private theorem bump_derivative {t : ℝ} (B : ContDiffBump t) (a H x : ℝ) :
    HasDerivAt (fun y : ℝ => B ((y-a)/H)) (deriv (B : ℝ → ℝ) ((x-a)/H)/H) x := by
  have d := ((hasDerivAt_id x).sub_const a).div_const H
  simpa only [Function.comp_def,id_eq,mul_one_div] using
    (((B.contDiff : ContDiff ℝ ∞ (B : ℝ → ℝ)).differentiable (by simp) ((x-a)/H)).hasDerivAt.comp x d)

theorem row_tests : ∃ D : ℝ, 0<D ∧ ∀ (N : ℕ) (a H P : ℝ), 1≤H → 3*H≤P → P<(N:ℝ)/20 →
    ShiftTest N (3*H) P (fun x => shape a H P x/D) := by
  obtain ⟨A,hA⟩ := ((inner.contDiff : ContDiff ℝ ∞ (inner : ℝ → ℝ)).continuous_deriv (by simp)).bounded_above_of_compact_support inner.hasCompactSupport.deriv
  obtain ⟨B,hB⟩ := ((outer.contDiff : ContDiff ℝ ∞ (outer : ℝ → ℝ)).continuous_deriv (by simp)).bounded_above_of_compact_support outer.hasCompactSupport.deriv
  have ap : 0≤A := (abs_nonneg _).trans (hA 0)
  have bp : 0≤B := (abs_nonneg _).trans (hB 0)
  let D := 1+3*(A+B)
  have dp : 0<D := by dsimp [D]; positivity
  refine ⟨D,dp,?_⟩
  intro N a H P hh size small
  have hp : 0<H := by linarith
  have pp : 0<P := by linarith
  have inside (x : ℝ) (hx : shape a H P x/D ≠ 0) : P<x ∧ x<2*P ∧ a+H<x ∧ x<a+4*H := by
    have z := (div_ne_zero_iff.mp hx).1
    obtain ⟨l,r⟩ := mul_ne_zero_iff.mp z
    change (x-a)/H ∈ Function.support inner at l
    change x/P ∈ Function.support outer at r
    rw [inner.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at l
    rw [outer.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at r
    change -(3/2:ℝ)<(x-a)/H-5/2 ∧ (x-a)/H-5/2<3/2 at l
    change -(1/2:ℝ)<x/P-3/2 ∧ x/P-3/2<1/2 at r
    have l₁ := (lt_div_iff₀ hp).mp (by linarith [l.1] : 1<(x-a)/H)
    have l₂ := (div_lt_iff₀ hp).mp (by linarith [l.2] : (x-a)/H<4)
    have r₁ := (lt_div_iff₀ pp).mp (by linarith [r.1] : 1<x/P)
    have r₂ := (div_lt_iff₀ pp).mp (by linarith [r.2] : x/P<2)
    exact ⟨by linarith,r₂,by linarith,by linarith⟩
  refine ⟨by linarith,size,small,?_,?_,⟨a+H,?_⟩,?_⟩
  · exact ((inner.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
      (outer.contDiff.comp (contDiff_id.div_const _))).div_const _
  · intro x hx
    have z := inside x hx
    exact ⟨z.1.le,z.2.1.le⟩
  · intro x hx
    have z := inside x hx
    exact ⟨z.2.2.1.le,by linarith [z.2.2.2]⟩
  · intro x
    have d₁ := bump_derivative inner a H x
    have d₂ : HasDerivAt (fun y : ℝ => outer (y/P)) (deriv (outer : ℝ → ℝ) (x/P)/P) x := by
      simpa using bump_derivative outer 0 P x
    have d := ((d₁.mul d₂).div_const D).deriv
    simp only [Pi.mul_apply] at d
    rw [abs_div,abs_of_pos dp]
    constructor
    · apply (div_le_one dp).mpr
      rw [shape,abs_mul,abs_of_nonneg inner.nonneg,abs_of_nonneg outer.nonneg]
      exact ((mul_le_of_le_one_right inner.nonneg outer.le_one).trans inner.le_one).trans (by dsimp [D]; linarith)
    · change 3*H*|deriv (fun y => (inner ((y-a)/H)*outer (y/P))/D) x|≤1
      rw [d,abs_div,abs_of_pos dp,← mul_div_assoc,div_le_one dp]
      have tri := abs_add_le (deriv (inner : ℝ → ℝ) ((x-a)/H)/H*outer (x/P)) (inner ((x-a)/H)*(deriv (outer : ℝ → ℝ) (x/P)/P))
      simp only [abs_mul,abs_div,abs_of_pos hp,abs_of_pos pp,abs_of_nonneg inner.nonneg,abs_of_nonneg outer.nonneg] at tri
      have j := mul_le_of_le_one_right (div_nonneg (abs_nonneg (deriv (inner : ℝ → ℝ) ((x-a)/H))) hp.le) (outer.le_one (x := x/P))
      have k := mul_le_of_le_one_left (div_nonneg (abs_nonneg (deriv (outer : ℝ → ℝ) (x/P))) pp.le) (inner.le_one (x := (x-a)/H))
      have aa := div_le_div_of_nonneg_right (hA ((x-a)/H)) hp.le
      have bb := div_le_div_of_nonneg_right (hB (x/P)) pp.le
      have b' := div_le_div_of_nonneg_left bp hp (by linarith : H≤P)
      have bound := tri.trans (add_le_add (j.trans aa) (k.trans (bb.trans b')))
      have mul := mul_le_mul_of_nonneg_left bound (show 0≤3*H by positivity)
      have id : 3*H*(A/H+B/H)=3*(A+B) := by field_simp
      exact mul.trans (by rw [id]; dsimp [D]; linarith)

end GoldbachSpectral.BandSieve

