module
public import KernelBound

/-! Integrals of affine threshold functions at the two axes of the square. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Filter Finset
namespace GoldbachSpectral435.CumulativeKernel

def edgeWeight (r : ℝ) := r*Real.sqrt r

lemma edge_pos {r : ℝ} (h : 0<r) : 0<edgeWeight r := mul_pos h (Real.sqrt_pos.mpr h)

lemma edge_mono {r s : ℝ} (p : 0≤r) (h : r≤s) : edgeWeight r≤edgeWeight s :=
  mul_le_mul h (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _) (p.trans h)

private lemma step_integrable (s : ℝ) {u : ℝ→ℝ} (hu : Measurable u) :
    Integrable (fun x => step s (u x)) unitMeasure := by
  apply (integrable_const (μ:=unitMeasure) (1:ℝ)).mono' (step_measurable measurable_const hu).aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (step_bounds _ _).1] using (step_bounds s (u x)).2

/-- Each of the affine maps parametrizing the lines in the model pulls a
threshold of width s back to an interval of length s. -/
private lemma step_average {s : ℝ} (sp : 0<s) {u : ℝ→ℝ} (hu : Measurable u)
    (l : ℝ) (image : ∀ x, 0<u x → u x<s → x∈Ioo l (l+s)) :
    (∫ x, step s (u x) ∂unitMeasure)≤edgeWeight s := by
  let J := Ioo l (l+s)
  let g := J.indicator (fun _ : ℝ => Real.sqrt s)
  have cmp (x : ℝ) : step s (u x)≤g x := by
    unfold step
    split_ifs with h
    · have mem : x∈J := image x h.1 h.2.1
      simpa only [g,indicator_of_mem mem] using Real.sqrt_le_sqrt h.2.1.le
    · exact indicator_nonneg (fun _ _ => Real.sqrt_nonneg _) _
  have m : unitMeasure.real J≤s := by
    have b : unitMeasure.real J≤volume.real J := ENNReal.toReal_mono (by simp [J])
      (Measure.restrict_le_self (μ:=volume) (s:=Ioc (0:ℝ) 1) J)
    simpa [J,Real.volume_real_Ioo,sp.le] using b
  have gi : Integrable g unitMeasure := (integrable_const _).indicator measurableSet_Ioo
  apply (integral_mono (step_integrable s hu) gi cmp).trans
  dsimp only [g]
  rw [integral_indicator measurableSet_Ioo,setIntegral_const,smul_eq_mul]
  exact mul_le_mul_of_nonneg_right m (Real.sqrt_nonneg _)

private lemma arc_one_side {s t : ℝ} (sp : 0<s) {u v : ℝ→ℝ}
    (hu : Measurable u) (hv : Measurable v) (l : ℝ)
    (image : ∀ x, 0<u x → u x<s → x∈Ioo l (l+s)) :
    (∫ x, step s (u x)*step t (v x) ∂unitMeasure)≤edgeWeight s := by
  have bound (x : ℝ) : step s (u x)*step t (v x)≤step s (u x) :=
    mul_le_of_le_one_right (step_bounds _ _).1 (step_bounds _ _).2
  have integr : Integrable (fun x => step s (u x)*step t (v x)) unitMeasure := by
    apply (step_integrable s hu).mono' ((step_measurable measurable_const hu).mul
      (step_measurable measurable_const hv)).aestronglyMeasurable
    filter_upwards with x
    change ‖step s (u x)*step t (v x)‖≤step s (u x)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (step_bounds _ _).1 (step_bounds _ _).1)]
      using bound x
  exact (integral_mono integr (step_integrable s hu) bound).trans (step_average sp hu l image)

/-- An affine line a positive distance from the corner contributes at most
a constant times (st)^(3/2). This includes cuts approaching either axis. -/
theorem arc_edges {s t y : ℝ} (sp : 0<s) (tp : 0<t) (yp : 0<y) (u v : ℝ→ℝ)
    (hu : Measurable u) (hv : Measurable v) (l r : ℝ)
    (left : ∀ x, 0<u x → u x<s → x∈Ioo l (l+s))
    (right : ∀ x, 0<v x → v x<t → x∈Ioo r (r+t))
    (apart : ∀ x, 0<u x → 0<v x → y≤u x+v x) :
    |∫ x, step s (u x)*step t (v x) ∂unitMeasure|≤
      (edgeWeight (y/2))⁻¹*edgeWeight s*edgeWeight t := by
  have ep := edge_pos (half_pos yp)
  have nonneg := integral_nonneg (μ:=unitMeasure) (fun x => mul_nonneg (step_bounds s (u x)).1 (step_bounds t (v x)).1)
  rw [abs_of_nonneg nonneg]
  by_cases dead : s+t≤y
  · have z (x : ℝ) : step s (u x)*step t (v x)=0 := by
      unfold step
      split_ifs with a b b
      · exfalso
        linarith [apart x a.1 b.1,a.2.1,b.2.1]
      all_goals simp
    simp_rw [z]
    simp only [integral_zero]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr ep.le) (edge_pos sp).le) (edge_pos tp).le
  by_cases large : y/2≤t
  · have le := edge_mono (half_pos yp).le large
    have side := arc_one_side (t:=t) sp hu hv l left
    apply side.trans
    have lift := mul_le_mul_of_nonneg_left le (edge_pos sp).le
    calc
      edgeWeight s = (edgeWeight (y/2))⁻¹*(edgeWeight s*edgeWeight (y/2)) := by field_simp
      _ ≤ (edgeWeight (y/2))⁻¹*(edgeWeight s*edgeWeight t) := mul_le_mul_of_nonneg_left lift (inv_nonneg.mpr ep.le)
      _ = _ := by ring
  · have le := edge_mono (half_pos yp).le (show y/2≤s by linarith)
    have side := arc_one_side (t:=s) tp hv hu r right
    simp_rw [mul_comm (step t (v _))] at side
    apply side.trans
    have lift := mul_le_mul_of_nonneg_right le (edge_pos tp).le
    calc
      edgeWeight t = (edgeWeight (y/2))⁻¹*(edgeWeight (y/2)*edgeWeight t) := by field_simp
      _ ≤ (edgeWeight (y/2))⁻¹*(edgeWeight s*edgeWeight t) := mul_le_mul_of_nonneg_left lift (inv_nonneg.mpr ep.le)
      _ = _ := by ring

#print axioms arc_edges
end GoldbachSpectral435.CumulativeKernel
