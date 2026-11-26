module
public import Characters
public import CumulativeKernel

/-! Conductor and strip-width dependence of the logarithmic derivative,
and uniform Mellin decay of the compact physical tests down to the axis. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex Set Metric MeasureTheory
namespace GoldbachSpectral435.CriticalCharacter

/-- A zero-free disk extending to within σ/2 of the critical line gives
a bound with a single conductor logarithm and explicit dependence on σ. -/
theorem log_derivative (q : ℕ) [NeZero q] (hq : 4≤q) (grh : GRH q)
    (χ : Character q) (nc : χ≠1) (σ t : ℝ) (sp : 0<σ) (s1 : σ≤1) :
    ‖logDerivative χ (line σ t)‖≤80/σ^2*(6+Real.log q)*(1+|t|) := by
  let c := line 3 t
  let R := 5/2-σ/2
  let r := 5/2-σ
  let z := (1/2:ℂ)+line σ t-c
  let f := fun u : ℂ => χ.LFunction (c+u)
  let X := (q:ℝ)*(|t|+2)
  have qr : (4:ℝ)≤q := by exact_mod_cast hq
  have qp : 0<(q:ℝ) := by linarith
  have tp := abs_nonneg t
  have rp : 0≤r := by dsimp [r]; linarith
  have gap : r<R := by dsimp [r,R]; linarith
  have big := rp.trans_lt gap
  have cr : c.re=3 := by simp [c,line]
  have cn : ‖c‖≤3+|t| := by
    simpa [c,line,norm_mul,Real.norm_eq_abs] using norm_add_le ((3:ℝ):ℂ) ((t:ℂ)*I)
  have xp : 0<X := by dsimp [X]; positivity
  have sz : 8≤X := by dsimp [X]; nlinarith only [qr,mul_nonneg qp.le tp]
  have analyt : AnalyticOnNhd ℂ f (ball 0 R) := fun u _ =>
    ((χ.differentiable_LFunction nc).analyticAt _).comp (analyticAt_const.add analyticAt_id)
  have half (u : ℂ) (hu : u∈ball 0 R) : 1/2<(c+u).re := by
    have n := mem_ball_zero_iff.mp hu
    have low := (neg_le_abs u.re).trans (abs_re_le_norm u)
    rw [add_re,cr]
    dsimp [R] at n
    linarith
  have no (u : ℂ) (hu : u∈ball 0 R) : f u≠0 := LFunction_ne_zero_of_GRH grh χ nc (half u hu)
  have low : 1/2≤‖f 0‖ := by simpa [f] using LFunction_right_lower_bound χ c cr.ge
  have upper (u : ℂ) (hu : u∈ball 0 R) : ‖f u‖≤8*X := by
    have re := half u hu
    have disk := mem_ball_zero_iff.mp hu
    have mag := norm_add_le c u
    have b := LFunction_polynomial_bound χ nc (c+u) (by linarith)
    have rat : ‖c+u‖/(c+u).re≤2*‖c+u‖ := by
      convert div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num : (0:ℝ)<1/2) re.le using 1
      ring
    have bk : 1+‖c+u‖/(c+u).re≤8*(|t|+2) := by dsimp [R] at disk; linarith
    exact b.trans ((mul_le_mul_of_nonneg_left bk qp.le).trans_eq (by dsimp [X]; ring))
  have zr : z=((σ-5/2:ℝ):ℂ) := by dsimp [z,c,line]; push_cast; ring
  have zn : ‖z‖≤r := by rw [zr,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]; dsimp [r]; linarith
  have b := logDerivative_disk_bound f R r (8*X) (1/2) big rp gap (by norm_num) (by linarith)
    analyt no low upper z zn
  have atz : c+z=1/2+line σ t := by dsimp [z]; ring
  have d := ((χ.differentiable_LFunction nc (c+z)).hasDerivAt).comp z ((hasDerivAt_id z).const_add c)
  have df : deriv f z=deriv χ.LFunction (1/2+line σ t) := by
    simpa only [f,Function.comp_def,atz,mul_one] using d.deriv
  rw [df,show f z=χ.LFunction (1/2+line σ t) by simp only [f,atz]] at b
  have pref : 8*R/(R-r)^2≤80/σ^2 := by
    rw [show R-r=σ/2 by dsimp [r,R]; ring,div_le_div_iff₀ (by positivity) (by positivity)]
    dsimp [R]
    nlinarith only [mul_pos sp (sq_pos_of_pos sp)]
  have lq : 0≤Real.log q := Real.log_nonneg (by linarith)
  have log16 : Real.log 16≤4 := by
    rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have logt := Real.log_le_sub_one_of_pos (by positivity : 0 < |t|+2)
  have logb : Real.log (8*X/(1/2))≤(6+Real.log q)*(1+|t|) := by
    rw [show 8*X/(1/2)=16*((q:ℝ)*(|t|+2)) by dsimp [X]; ring,Real.log_mul (by norm_num) xp.ne',
      Real.log_mul qp.ne' (by positivity)]
    nlinarith only [log16,logt,tp,mul_nonneg lq tp]
  have lg : 0≤Real.log (8*X/(1/2)) := Real.log_nonneg (by linarith)
  exact b.trans ((mul_le_mul pref logb lg (by positivity)).trans_eq (by ring))

theorem mellin_axis (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    ∃ C : ℝ, 0<C ∧ ∀ s : ℂ, s.re∈Icc (0:ℝ) 1 →
      ‖mellin (fun u => (companion f u:ℂ)) s‖≤C*(1+|s.im|)⁻¹^4 := by
  let g := CumulativeKernel.profile f
  have cont : ContDiff ℝ 4 g := (CumulativeKernel.profile_smooth hf).of_le (by decide)
  have support : Function.support g⊆Icc hf.lower hf.upper := by
    intro u hu
    apply hf.mem_support_interval
    intro z
    exact hu (by simp [g,CumulativeKernel.profile,z])
  obtain ⟨C,cp,dec⟩ := compact_mellin_finite_decay 4 g cont _ _ support 1 2 (by norm_num) (by norm_num)
  refine ⟨C,cp,fun s hs => ?_⟩
  have eq : (fun u => (companion f u:ℂ))=(fun u : ℝ => (u:ℂ)^(1:ℂ) • (g u:ℂ)) := by
    funext u
    rw [Complex.cpow_one,smul_eq_mul]
    have real : companion f u=u*g u := by
      by_cases up : 0<u
      · unfold companion g CumulativeKernel.profile
        field_simp [(Real.sqrt_pos.mpr up).ne']
        nlinarith only [congrArg (·*f u) (Real.sq_sqrt up.le)]
      · simp [companion,g,CumulativeKernel.profile,Real.sqrt_eq_zero_of_nonpos (le_of_not_gt up)]
    exact_mod_cast real
  rw [eq,mellin_cpow_smul]
  simpa only [add_im,one_im,add_zero] using dec (s+1) (by
    rw [add_re,one_re]; constructor <;> linarith [hs.1,hs.2])

#print axioms log_derivative
#print axioms mellin_axis
end GoldbachSpectral435.CriticalCharacter
