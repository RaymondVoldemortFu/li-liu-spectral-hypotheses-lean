module
public import FirstLineLimits

/-! Polarization recovers arbitrary smooth local tests from the reflected
quadratic test family of the original operator. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Finset
open scoped Topology
namespace GoldbachSpectral435.FirstLineLimits
open GoldbachPrimitive

lemma mirror_mass (N n : ℕ) (le : n≤N) : mass N (N-n)=mass N n := by
  have c : (N-n).Coprime N ↔ n.Coprime N := by
    calc
      _ ↔ (N-n).Coprime ((N-n)+n) := by rw [Nat.sub_add_cancel le]
      _ ↔ (N-n).Coprime n := Nat.coprime_self_add_right
      _ ↔ N.Coprime n := Nat.coprime_sub_self_left le
      _ ↔ _ := Nat.coprime_comm
  simp only [mass,c,Nat.sub_sub_self le,mul_comm (mangoldt (N-n))]

theorem observed_reflect (N : ℕ) (np : 0<N) (f : ℝ→ℝ) :
    observed N (fun t => f (1-t))=observed N f := by
  let w := fun n : ℕ => mass N n*f (n/(N:ℝ))
  have endp : mass N N=0 := by simp [mass,mangoldt]
  have same (n : ℕ) (h : n∈range (N+1)) : mass N n*f (1-(n:ℝ)/N)=w (N-n) := by
    have le : n≤N := by have := mem_range.mp h; omega
    have nr : (N:ℝ)≠0 := by exact_mod_cast np.ne'
    dsimp [w]
    rw [mirror_mass N n le,Nat.cast_sub le,sub_div,div_self nr]
  have e : (∑ n∈range (N+1), mass N n*f (1-(n:ℝ)/N))=∑ n∈range (N+1), w n := by
    rw [sum_congr rfl same]
    simpa using sum_range_reflect w (N+1)
  simp only [sum_range_succ,w,endp,zero_mul,add_zero] at e
  exact congrArg (·/singularSeries N) e

def cutoff (d u : ℝ) : ℝ :=
  Real.smoothTransition ((u-d)/d)*Real.smoothTransition (((1-u)-d)/d)

lemma cutoff_smooth (d : ℝ) : ContDiff ℝ 6 (cutoff d) := by
  unfold cutoff
  apply ContDiff.mul <;> apply Real.smoothTransition.contDiff.comp <;> fun_prop

lemma cutoff_limits (d u : ℝ) : 0≤cutoff d u ∧ cutoff d u≤1 := by
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),?_⟩
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (one_mul _)

lemma cutoff_support {d : ℝ} (dp : 0<d) : Function.support (cutoff d)⊆Set.Icc d (1-d) := by
  intro u hu
  by_contra out
  apply hu
  unfold cutoff
  by_cases h : d≤u
  · have n : 1-d<u := lt_of_not_ge (fun j => out ⟨h,j⟩)
    have z : ((1-u)-d)/d≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) dp.le
    rw [Real.smoothTransition.zero_of_nonpos z,mul_zero]
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) dp.le),zero_mul]

lemma cutoff_one {d u : ℝ} (dp : 0<d) (lo : 2*d≤u) (hi : u≤1-2*d) : cutoff d u=1 := by
  unfold cutoff
  rw [Real.smoothTransition.one_of_one_le ((one_le_div dp).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((one_le_div dp).mpr (by linarith)),one_mul]

private lemma polarization {f : ℝ→ℝ} (hf : FiniteModelWeight f) :
    ∃ (a b : ℝ→ℝ) (_ : FiniteModelWeight a) (_ : FiniteModelWeight b),
      ∀ u, reflected a u-reflected b u=2*(f u+f (1-u)) := by
  let d := min hf.lower (1-hf.upper)/4
  have dp : 0<d := div_pos (lt_min hf.lower_pos (sub_pos.mpr hf.upper_lt_one)) (by norm_num)
  have u := hf.upper_lt_one
  have l := hf.lower_le_upper
  have lo : 2*d≤hf.lower := by dsimp [d]; linarith [hf.lower_pos,min_le_left hf.lower (1-hf.upper)]
  have hi : hf.upper≤1-2*d := by dsimp [d]; linarith [min_le_right hf.lower (1-hf.upper)]
  have ends : d≤1-d := by linarith
  let g := cutoff d
  have both {x : ℝ} (h : f x≠0) : g (1-x)=1 := by
    obtain ⟨a,b⟩ := hf.mem_support_interval h
    exact cutoff_one dp (by linarith) (by linarith)
  have sg : Function.support f⊆Set.Icc d (1-d) := fun x h =>
    ⟨(by linarith [((hf.mem_support_interval h).1)]),(by linarith [((hf.mem_support_interval h).2)])⟩
  have support (op : ℝ→ℝ→ℝ) (zero : op 0 0=0) : Function.support (fun t => op (g t) (f t))⊆Set.Icc d (1-d) := by
    intro x hx
    by_contra out
    have gz : g x=0 := by by_contra nz; exact out (cutoff_support dp nz)
    have fz : f x=0 := by by_contra nz; exact out (sg nz)
    exact hx (show op (g x) (f x)=0 by rw [gz,fz,zero])
  let a := fun t => g t+f t
  let b := fun t => g t-f t
  refine ⟨a,b,⟨(cutoff_smooth d).add hf.smooth,d,1-d,dp,by linarith,ends,support (·+·) (by norm_num)⟩,
    ⟨(cutoff_smooth d).sub hf.smooth,d,1-d,dp,by linarith,ends,support (·-·) (by norm_num)⟩,?_⟩
  intro t
  have left : f t*g (1-t)=f t := by by_cases h : f t=0 <;> simp [h,both]
  have right : f (1-t)*g t=f (1-t) := by
    by_cases h : f (1-t)=0
    · simp [h]
    · have v := both h
      rw [show 1-(1-t)=t by ring] at v
      rw [v,mul_one]
  dsimp [reflected,a,b]
  linear_combination 2*left+2*right

private lemma observed_pair (N : ℕ) (np : 0<N) (a b f : ℝ→ℝ)
    (eq : ∀ t, reflected a t-reflected b t=2*(f t+f (1-t))) :
    observed N (reflected a)-observed N (reflected b)=4*observed N f := by
  have before : observed N (reflected a)-observed N (reflected b)=2*(observed N f+observed N (fun t => f (1-t))) := by
    unfold observed
    rw [← sub_div,← add_div,← sum_sub_distrib,← sum_add_distrib,← mul_div_assoc,Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro n _
    linear_combination (mass N n)*eq ((n:ℝ)/N)
  rw [before,observed_reflect N np]
  ring

private lemma mean_pair (a b f : ℝ→ℝ) (ha : FiniteModelWeight a) (hb : FiniteModelWeight b) (hf : FiniteModelWeight f)
    (eq : ∀ t, reflected a t-reflected b t=2*(f t+f (1-t))) :
    mean (reflected a)-mean (reflected b)=4*mean f := by
  have cont (v : ℝ→ℝ) (c : Continuous v) : Continuous (reflected v) := c.mul (c.comp (continuous_const.sub continuous_id))
  unfold mean
  rw [← intervalIntegral.integral_sub ((cont a ha.continuous).intervalIntegrable ..) ((cont b hb.continuous).intervalIntegrable ..)]
  simp_rw [eq]
  have mir : Continuous (fun x : ℝ => f (1-x)) := hf.continuous.comp (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (hf.continuous.intervalIntegrable ..)
    (mir.intervalIntegrable ..),intervalIntegral.integral_comp_sub_left,sub_self,sub_zero]
  ring

/-- Convergence at every fixed smooth interior weight, without any
symmetry condition on that weight. -/
theorem smooth_limit {n : ℕ→ℕ} [∀ j, NeZero (n j)] (h : FirstScaleDecay n)
    (ng : Tendsto n atTop atTop) (he : ∀ j, Even (n j)) (grh : ∀ j, GRH (n j))
    (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    Tendsto (fun j => observed (n j) f) atTop (𝓝 (mean f)) := by
  obtain ⟨a,b,ha,hb,eq⟩ := polarization hf
  have lim := ((reflected_limit h ng he grh a ha).sub (reflected_limit h ng he grh b hb)).div_const 4
  rw [mean_pair a b f ha hb hf eq] at lim
  simpa only [observed_pair _ (NeZero.pos _) a b f eq,mul_div_cancel_left₀ _ (by norm_num : (4:ℝ)≠0)] using lim

#print axioms smooth_limit
end GoldbachSpectral435.FirstLineLimits
