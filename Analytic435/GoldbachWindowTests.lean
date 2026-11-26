module
public import GoldbachSmoothTests

/-! Smooth inner approximations of all initial intervals for the actual
normalized Goldbach measure. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Filter Finset Set
open scoped Topology
namespace GoldbachSpectral435.FirstLineLimits
open GoldbachPrimitive GoldbachSieve

def window (t d u : ℝ) : ℝ :=
  Real.smoothTransition ((u-d)/d)*Real.smoothTransition ((t-u-d)/d)

lemma window_bounds (t d u : ℝ) : 0≤window t d u ∧ window t d u≤1 :=
  ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
   (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
     (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (one_mul _)⟩

lemma window_right {t d u : ℝ} (dp : 0<d) (hu : t-d≤u) : window t d u=0 := by
  have h : (t-u-d)/d≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) dp.le
  unfold window
  rw [Real.smoothTransition.zero_of_nonpos h,mul_zero]

lemma window_one {t d u : ℝ} (dp : 0<d) (left : 2*d≤u) (right : u≤t-2*d) :
    window t d u=1 := by
  unfold window
  rw [Real.smoothTransition.one_of_one_le ((one_le_div dp).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((one_le_div dp).mpr (by linarith)),one_mul]

def window_weight {t d : ℝ} (dp : 0<d) (sep : 4*d≤t) (t1 : t≤1) : FiniteModelWeight (window t d) where
  smooth := by unfold window; apply ContDiff.mul <;> apply Real.smoothTransition.contDiff.comp <;> fun_prop
  lower := d
  upper := t-d
  lower_pos := dp
  upper_lt_one := by linarith
  lower_le_upper := by linarith
  support_subset := by
    intro u hu
    by_contra out
    apply hu
    by_cases h : d≤u
    · exact window_right dp (le_of_not_ge (fun j => out ⟨h,j⟩))
    · have v : (u-d)/d≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) dp.le
      unfold window
      rw [Real.smoothTransition.zero_of_nonpos v,zero_mul]

lemma window_mean {t d : ℝ} (dp : 0<d) (sep : 4*d≤t) (t1 : t≤1) :
    t-4*d≤mean (window t d) ∧ mean (window t d)≤t := by
  have c := (window_weight dp sep t1).continuous
  have mid : 2*d≤t-2*d := by linarith
  have eq : (∫ x in 2*d..t-2*d, window t d x)=t-4*d := by
    rw [intervalIntegral.integral_congr (g:=fun _ => (1:ℝ)) (fun x hx => by
      rw [uIcc_of_le mid] at hx
      exact window_one dp hx.1 hx.2)]
    simp
    ring
  have last : (∫ x in t..1, window t d x)=0 := by
    rw [intervalIntegral.integral_congr (g:=fun _ => (0:ℝ)) (fun x hx => by
      rw [uIcc_of_le t1] at hx
      exact window_right dp (by linarith [hx.1]))]
    simp
  unfold mean
  refine ⟨eq ▸ intervalIntegral.integral_mono_interval (by positivity) mid (by linarith)
    (Eventually.of_forall (fun x => (window_bounds t d x).1)) (c.intervalIntegrable ..),?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (c.intervalIntegrable 0 t) (c.intervalIntegrable t 1),last,add_zero]
  have b := intervalIntegral.integral_mono_on (μ:=volume) (show 0≤t by linarith) (c.intervalIntegrable 0 t)
    ((continuous_const (y:=(1:ℝ))).intervalIntegrable 0 t) (fun x _ => (window_bounds t d x).2)
  simpa using b

lemma window_mass_compare (N : ℕ) {t d : ℝ} (dp : 0<d) :
    distribution N (t-2*d)-distribution N (2*d)≤observed N (window t d) ∧
    observed N (window t d)≤distribution N t := by
  have mp (n : ℕ) : 0≤mass N n := by
    unfold mass
    split_ifs
    · exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg _)
    · rfl
  unfold distribution observed
  rw [← sub_div,← sum_sub_distrib]
  constructor <;> apply div_le_div_of_nonneg_right _ (singularSeries_pos N).le <;> apply sum_le_sum <;> intro n _
  · let u := (n:ℝ)/N
    change (if u<t-2*d then mass N n else 0)-(if u<2*d then mass N n else 0)≤mass N n*window t d u
    have pos := mul_nonneg (mp n) (window_bounds t d u).1
    by_cases a : u<t-2*d <;> by_cases b : u<2*d <;> simp only [a,b,ite_true,ite_false,sub_self,sub_zero,zero_sub] <;> try linarith [mp n]
    rw [window_one dp (le_of_not_gt b) a.le,mul_one]
  · by_cases a : (n:ℝ)/N<t
    · simpa only [ite_eq_left a] using (mul_le_mul_of_nonneg_left (window_bounds t d ((n:ℝ)/N)).2 (mp n)).trans_eq (mul_one _)
    · simp [a,window_right dp (show t-d≤(n:ℝ)/N by linarith)]

end GoldbachSpectral435.FirstLineLimits
