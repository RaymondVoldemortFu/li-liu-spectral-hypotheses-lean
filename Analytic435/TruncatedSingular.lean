module
public import LocalFactorTail

/-! Uniform approximation of the original singular series by the local
factors up to z. The bound is simultaneous over all log H ≤ B z log z. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Finset Filter
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open GoldbachSpectral

def primeCorrection (p : ℕ) : ℝ := ((p:ℝ)-1)/((p:ℝ)-2)

def truncatedSeries (H z : ℕ) : ℝ := 2*(∏ n∈range (z+1), twinFactor n)*
  ∏ p∈H.primeFactors.filter (fun p => 2<p ∧ p≤z), primeCorrection p

private def tailProduct (H z : ℕ) := ∏ p∈largeFactors H z, primeCorrection p

private lemma correction_bounds {p : ℕ} (hp : 4≤p) :
    1≤primeCorrection p ∧ primeCorrection p≤Real.exp (2/(p:ℝ)) := by
  have pr : (4:ℝ)≤p := by exact_mod_cast hp
  have pp : 0<(p:ℝ) := by linarith
  have den : 0<(p:ℝ)-2 := by linarith
  have c : primeCorrection p=1+1/((p:ℝ)-2) := by unfold primeCorrection; field_simp; ring
  rw [c]
  constructor
  · linarith [one_div_pos.mpr den]
  · have b : 1/((p:ℝ)-2)≤2/(p:ℝ) := (div_le_div_iff₀ den pp).mpr (by linarith)
    linarith [Real.add_one_le_exp (2/(p:ℝ))]

private lemma product_bounds (H z : ℕ) (zz : 3≤z) :
    1≤tailProduct H z ∧ tailProduct H z≤Real.exp (2*reciprocalTail H z) := by
  have b (p : ℕ) (m : p∈largeFactors H z) := correction_bounds (show 4≤p by have := (mem_filter.mp m).2; omega)
  refine ⟨one_le_prod₀ (fun p m => (b p m).1),?_⟩
  have c := prod_le_prod₀ (fun p m => zero_le_one.trans (b p m).1) (fun p m => (b p m).2)
  unfold tailProduct
  apply c.trans_eq
  rw [← Real.exp_sum,reciprocalTail,mul_sum]
  congr 1
  apply sum_congr rfl
  intro p _
  ring

private lemma series_ratio (H z : ℕ) (zz : 3≤z) :
    truncatedSeries H z/singularSeries H=
      ((∏ n∈range (z+1), twinFactor n)/(∏' n, twinFactor n))/tailProduct H z := by
  let A := H.primeFactors.filter (2<·)
  let S := H.primeFactors.filter (fun p => 2<p ∧ p≤z)
  have left : A.filter (·≤z)=S := by ext p; simp [A,S,and_assoc]
  have right : A.filter (fun p => ¬p≤z)=largeFactors H z := by
    ext p
    simp only [A,largeFactors,mem_filter,not_le]
    constructor
    · exact fun ⟨⟨m,_⟩,h⟩ => ⟨m,h⟩
    · exact fun ⟨m,h⟩ => ⟨⟨m,by omega⟩,h⟩
  have prod := prod_filter_mul_prod_filter_not A (·≤z) primeCorrection
  rw [left,right] at prod
  change (∏ p∈S, primeCorrection p)*tailProduct H z=∏ p∈A,primeCorrection p at prod
  have nn : (∏ p∈S, primeCorrection p)≠0 := by
    apply prod_ne_zero_iff.mpr
    intro p hp
    have h : (2:ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2.1
    exact (div_pos (by linarith) (by linarith) : 0<((p:ℝ)-1)/((p:ℝ)-2)).ne'
  have c : 0<(∏' n, twinFactor n) := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) twin_convergence.2
  have tp := zero_lt_one.trans_le (product_bounds H z zz).1
  rw [original_series]
  change (2*_* (∏ p∈S,primeCorrection p))/(2*(∏' n,twinFactor n)*(∏ p∈A,primeCorrection p))=_
  rw [← prod]
  field_simp

theorem truncated_series_uniform (B ε : ℝ) (ep : 0<ε) :
    ∀ᶠ z : ℕ in atTop, ∀ H : ℕ, 0<H → Real.log H≤B*z*Real.log z →
      |truncatedSeries H z/singularSeries H-1|≤ε := by
  let twin := ∏' n, twinFactor n
  have tw : 0<twin := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) twin_convergence.2
  have lim : Tendsto (fun z : ℕ => (∏ n∈range (z+1), twinFactor n)/twin) atTop (𝓝 1) := by
    rw [← div_self tw.ne']
    simpa only [Function.comp_def] using
      ((twin_convergence.1.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)).div_const twin)
  let η := Real.log (1+ε/2)/2
  have pos : 0<η := div_pos (Real.log_pos (by linarith)) (by norm_num)
  filter_upwards [eventually_ge_atTop (3:ℕ),uniform_reciprocal_tail B η pos,
    Metric.tendsto_nhds.mp lim (ε/2) (half_pos ep)] with z zz lt near
  intro H hp size
  have b := product_bounds H z zz
  have r := lt H hp size
  have e : tailProduct H z≤1+ε/2 := by
    apply b.2.trans
    have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left r (by norm_num : (0:ℝ)≤2))
    simpa only [η,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0),Real.exp_log (by linarith : 0<1+ε/2)] using h
  have tp := zero_lt_one.trans_le b.1
  change dist ((∏ n∈range (z+1),twinFactor n)/twin) 1<ε/2 at near
  rw [Real.dist_eq,abs_lt] at near
  rw [series_ratio H z zz,abs_le]
  change -ε≤((∏ n∈range (z+1),twinFactor n)/twin)/tailProduct H z-1 ∧
    ((∏ n∈range (z+1),twinFactor n)/twin)/tailProduct H z-1≤ε
  constructor
  · rw [le_sub_iff_add_le,le_div_iff₀ tp]
    nlinarith only [near.1,e,mul_le_mul_of_nonneg_left b.1 ep.le]
  · rw [sub_le_iff_le_add,div_le_iff₀ tp]
    nlinarith only [near.2,b.1,ep,mul_le_mul_of_nonneg_left b.1 ep.le]

#print axioms truncated_series_uniform
end GoldbachSpectral435.GoldbachSieve
