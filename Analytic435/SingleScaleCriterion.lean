module
public import SingleScaleBound
public import ExistenceLocalization
public import KernelBound

/-! One prescribed sampling scale per modulus detects the full original
existence assertion, with a uniform error for the discarded output tail. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Filter
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435.PhysicalTests
open FiniteDiscrepancy ExistenceLocalization

def horizon (N : ℕ) : ℝ := 8*Real.log N*Real.log (Real.log N)
def scale (N : ℕ) : ℕ := ⌈Real.exp (horizon N)/(N:ℝ)⌉₊

lemma horizon_le_log (N : ℕ) [NeZero N] :
    0<scale N ∧ horizon N≤Real.log (scale N*N:ℕ) := by
  have np : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have pos : 0<scale N := Nat.ceil_pos.mpr (div_pos (Real.exp_pos _) np)
  refine ⟨pos,(Real.le_log_iff_exp_le (by exact_mod_cast Nat.mul_pos pos (NeZero.pos N))).mpr ?_⟩
  push_cast
  exact (div_le_iff₀ np).mp (Nat.le_ceil _)

private def mask {a : ℝ} (S : Set ℝ) (m : MeasurableSet S) (x : HardySpace a beta) : HardySpace a beta :=
  ((Lp.memLp x).indicator m.nullMeasurableSet).toLp _

private lemma mask_ae {a : ℝ} (S : Set ℝ) (m : MeasurableSet S) (x : HardySpace a beta) :
    mask S m x=ᵐ[hardyMeasure a beta] S.indicator x :=
  ((Lp.memLp x).indicator m.nullMeasurableSet).coeFn_toLp

private lemma mask_norm {a : ℝ} (S : Set ℝ) (m : MeasurableSet S) (x : HardySpace a beta) :
    ‖mask S m x‖≤‖x‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [mask_ae S m x] with t ht
  rw [ht]
  exact norm_indicator_le_norm_self (x:ℝ→ℂ) t

private lemma mask_energy {a : ℝ} (S : Set ℝ) (m : MeasurableSet S) (x : HardySpace a beta) :
    ‖mask S m x‖^2=∫ t in S, ‖x t‖^2*hardyWeight a beta t := by
  rw [hardySpace_norm_sq_integral,← integral_indicator m]
  apply integral_congr_ae
  filter_upwards [(volume_absolutelyContinuous_hardyMeasure _ _).ae_eq (mask_ae S m x)] with t ht
  by_cases h : t∈S <;> simp [ht,h]

private lemma mask_inner {a : ℝ} (S : Set ℝ) (m : MeasurableSet S) (x y : HardySpace a beta) :
    inner ℂ (mask S m x) y=inner ℂ x (mask S m y) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mask_ae S m x,mask_ae S m y] with t h j
  by_cases s : t∈S <;> simp [h,j,s]

private theorem tail_transfer (N : ℕ) [NeZero N] (ev : Even N) (big : Real.exp 10<(N:ℝ))
    (g : GRH N) (ha : alpha N<beta) (d B : ℝ) (dp : 0≤d) (bp : 0≤B)
    (tail : ∀ x : HardySpace (alpha N) beta, (∫ t in Iic (-horizon N),
      ‖(residualOperator ha N x) t‖^2*hardyWeight (alpha N) beta t)≤d^2*‖x‖^2)
    (finite : ScaleBound N (scale N) B) : ‖residualOperator ha N‖≤B+2*d := by
  let T := residualOperator ha N
  have sym := (residualOperator_spec_at _ N (large_alpha_pos big) (large_parameters big).1 g ha).2.2.2.1.isSymmetric
  have q (x : HardySpace (alpha N) beta) : ‖inner ℂ x (T x)‖≤(B+2*d)*‖x‖^2 := by
    let S := Iic (-horizon N)
    let y := mask Sᶜ measurableSet_Iic.compl x
    let z := mask S measurableSet_Iic x
    have ny : ‖y‖≤‖x‖ := mask_norm ..
    have yz : y+z=x := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_add y z,mask_ae Sᶜ measurableSet_Iic.compl x,mask_ae S measurableSet_Iic x] with t a b c
      rw [a]
      change mask Sᶜ measurableSet_Iic.compl x t+mask S measurableSet_Iic x t=x t
      rw [b,c]
      by_cases s : t∈S <;> simp [s]
    obtain ⟨pos,lg⟩ := horizon_le_log N
    have supp : ∀ᵐ t ∂hardyMeasure (alpha N) beta, t≤ -Real.log (scale N*N:ℕ) → y t=0 := by
      filter_upwards [mask_ae Sᶜ measurableSet_Iic.compl x] with t h ht
      have m : t∈S := by change t≤ -horizon N; linarith
      exact h.trans (indicator_of_notMem (notMem_compl_iff.mpr m) _)
    have near := block_bound N (scale N) pos ev big g ha B finite y supp
    have far (v : HardySpace (alpha N) beta) : ‖inner ℂ z (T v)‖≤‖x‖*(d*‖v‖) := by
      have energy := tail v
      rw [← mask_energy S measurableSet_Iic (T v),← mul_pow] at energy
      have norm := le_of_sq_le_sq energy (mul_nonneg dp (norm_nonneg _))
      rw [show inner ℂ z (T v)=_ from mask_inner S measurableSet_Iic x (T v)]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left norm (norm_nonneg _))
    have rev : ‖inner ℂ y (T z)‖=‖inner ℂ z (T y)‖ := by
      have eq : inner ℂ (T y) z=inner ℂ y (T z) := sym y z
      rw [← eq]
      exact norm_inner_symm ..
    have expand : inner ℂ x (T x)=inner ℂ y (T y)+(inner ℂ z (T x)+inner ℂ y (T z)) := by
      conv_lhs => rw [← yz,inner_add_left,map_add,inner_add_right,inner_add_right]
      rw [← yz,map_add,inner_add_right]
      abel
    rw [expand]
    apply (norm_add_le _ _).trans
    have tr := norm_add_le (inner ℂ z (T x)) (inner ℂ y (T z))
    rw [rev] at tr
    calc
      _ ≤ B*‖x‖^2+(‖x‖*(d*‖x‖)+‖x‖*(d*‖x‖)) := add_le_add
        (near.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ny 2) bp))
        (tr.trans (add_le_add (far x) ((far y).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ny dp) (norm_nonneg _)))))
      _ = _ := by ring
  rw [T.norm_eq_iSup_rayleighQuotient sym]
  apply ciSup_le
  intro x
  by_cases z : x=0
  · simp [z,show 0≤B+2*d by positivity]
  change |(inner ℂ (T x) x).re/‖x‖^2|≤_
  rw [abs_div,abs_of_nonneg (sq_nonneg ‖x‖)]
  apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr z) _)).mpr
  exact (Complex.abs_re_le_norm _).trans ((congrArg norm (sym x x)).le.trans (q x))

/-- Extending the estimate from the prescribed real tests to the full original
operator costs at most C/(log N)^2, with an absolute constant. -/
theorem norm_le_single_scale :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) [NeZero N], Even N → Real.exp 10<(N:ℝ) → GRH N →
      ∀ (ha : alpha N<beta) (B : ℝ), 0≤B → ScaleBound N (scale N) B →
        ‖residualOperator ha N‖≤B+C/(Real.log N)^2 := by
  obtain ⟨D,dp,energy⟩ := uniform_far_energy
  refine ⟨2*Real.sqrt D,by positivity,?_⟩
  intro N inst he big grh ha B bp cap
  let l := Real.log (N:ℝ)
  have lp : 0<l := (large_parameters big).2.1
  let d := Real.sqrt D/l^2
  have ds : d^2=D/l^4 := by
    dsimp [d]
    rw [div_pow,Real.sq_sqrt dp.le]
    ring
  have cut (v : HardySpace (alpha N) beta) : (∫ t in Iic (-horizon N),
      ‖(residualOperator ha N v) t‖^2*hardyWeight (alpha N) beta t)≤ d^2*‖v‖^2 := by
    rw [ds]
    exact energy N he big grh ha v
  have bound := tail_transfer N he big grh ha d B (by dsimp [d]; positivity) bp cut cap
  exact bound.trans_eq (by dsimp [d,l]; ring)

/-- For each N just the explicit dilation ceil(exp(8 log N log log N)/N)
is needed. The arithmetic and continuous sums are both finite at this scale. -/
theorem exists_iff_single_scale : (∃ h, HypothesisS h) ↔
    ∀ ε : ℝ, 0<ε → EvenEventually (fun N => ∀ [NeZero N], GRH N →
      ScaleBound N (scale N) (ε*singularSeries N)) := by
  constructor
  · intro existsS ε ep
    obtain ⟨K,h⟩ := FiniteDiscrepancy.some_S_iff.mp existsS ε ep
    exact ⟨K,fun N hn he _ grh => h N hn he grh (scale N) (horizon_le_log N).1⟩
  · intro fixed
    apply some_actual_S_iff.mpr
    intro ε ep
    obtain ⟨D,dp,energy⟩ := uniform_far_energy
    obtain ⟨K,h⟩ := (fixed (ε/2) (by positivity)).and evenEventually_large
    have loglim := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    have lim : Tendsto (fun n : ℕ => D/Real.log n^4) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 4≠0)).comp loglim)
    obtain ⟨J,small⟩ := eventually_atTop.mp (lim.eventually_lt_const (show 0<(ε/4)^2 by positivity))
    refine ⟨max K J,fun N hn he => ?_⟩
    obtain ⟨fin,big⟩ := h N (by omega) he
    obtain ⟨four,_,ha⟩ := large_parameters big
    let inst : NeZero N := ⟨by omega⟩
    have ss := (singularSeries_gt_one N).le
    have sp := singularSeries_pos N
    by_cases grh : GRH N
    · rw [eligibleNorm_spec N ha grh]
      have cut (v : HardySpace (alpha N) beta) := (energy N he big grh ha v).trans
        (mul_le_mul_of_nonneg_right (small N (by omega)).le (sq_nonneg _))
      have b := tail_transfer N he big grh ha (ε/4) ((ε/2)*singularSeries N)
        (by positivity) (by positivity) cut (fin grh)
      have c := mul_le_mul_of_nonneg_left ss ep.le
      linarith
    · simp [eligibleNorm,grh,mul_nonneg ep.le sp.le]

/-- The two-dimensional integral only needs an estimate at the specified
finite horizon for each modulus. -/
theorem exists_of_single_kernel_decay
    (decay : ∀ ε : ℝ, 0<ε → EvenEventually (fun N => ∀ [NeZero N], GRH N →
      MemLp (CumulativeKernel.normalizedKernel N (scale N)) 2 CumulativeKernel.thresholds ∧
      2*Real.pi*CumulativeKernel.kernelSize N (scale N)≤ε*singularSeries N)) :
    ∃ h, HypothesisS h := by
  apply exists_iff_single_scale.mpr
  intro ε ep
  obtain ⟨K,h⟩ := (decay ε ep).and evenEventually_large
  refine ⟨K,fun N hn he inst grh f hf => ?_⟩
  obtain ⟨cap,big⟩ := h N hn he
  obtain ⟨integ,small⟩ := cap grh
  have ha := (large_parameters big).2.2
  have kp := (horizon_le_log N).1
  obtain ⟨n,e⟩ := exact_form N (scale N) kp he big grh ha f hf
  rw [← e,← n]
  exact (CumulativeKernel.spectral_bound N (scale N) kp he big grh ha integ f hf).trans
    (mul_le_mul_of_nonneg_right small (sq_nonneg _))

#print axioms exists_of_single_kernel_decay
#print axioms norm_le_single_scale
#print axioms exists_iff_single_scale
end GoldbachSpectral435.PhysicalTests
