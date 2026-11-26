module
public import ThresholdEdges

/-! A measurable envelope on the whole threshold square for every finite
signed kernel. Its constant may depend on the modulus and dilation. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Filter Finset
namespace GoldbachSpectral435.CumulativeKernel

structure EdgeControl (K : ℝ×ℝ→ℝ) : Prop where
  measurable : Measurable K
  bound : ∃ C : ℝ, 0≤C ∧ ∀ s t : ℝ, 0<s → 0<t → |K (s,t)|≤C*(edgeWeight s*edgeWeight t)

private lemma add_control {K J : ℝ×ℝ→ℝ} (h : EdgeControl K) (g : EdgeControl J) :
    EdgeControl (fun p => K p+J p) := by
  obtain ⟨C,cp,b⟩ := h.bound
  obtain ⟨D,dp,c⟩ := g.bound
  refine ⟨h.measurable.add g.measurable,C+D,add_nonneg cp dp,?_⟩
  intro s t sp tp
  rw [add_mul]
  exact (abs_add_le ..).trans (add_le_add (b s t sp tp) (c s t sp tp))

private lemma mul_control {K : ℝ×ℝ→ℝ} (h : EdgeControl K) (a : ℝ) :
    EdgeControl (fun p => a*K p) := by
  obtain ⟨C,cp,b⟩ := h.bound
  refine ⟨measurable_const.mul h.measurable,|a| * C,mul_nonneg (abs_nonneg _) cp,?_⟩
  intro s t sp tp
  rw [abs_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (b s t sp tp) (abs_nonneg _)

private lemma sub_control {K J : ℝ×ℝ→ℝ} (h : EdgeControl K) (g : EdgeControl J) :
    EdgeControl (fun p => K p-J p) := by
  simpa only [neg_one_mul,← sub_eq_add_neg] using add_control h (mul_control g (-1))

private lemma sum_control {ι : Type*} (I : Finset ι) {K : ι→ℝ×ℝ→ℝ}
    (h : ∀ i∈I, EdgeControl (K i)) : EdgeControl (fun p => ∑ i∈I, K i p) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [sum_empty] using (show EdgeControl (fun _ => 0) from
      ⟨measurable_const,0,le_rfl,fun _ _ _ _ => by simp⟩)
  | @insert i I fresh ih =>
    simpa only [sum_insert fresh] using add_control (h i (mem_insert_self ..))
      (ih (fun j hj => h j (mem_insert_of_mem hj)))

private lemma atom_side (u : ℝ) : ∃ C : ℝ, 0≤C ∧ ∀ s : ℝ, 0<s → step s u≤C*edgeWeight s := by
  by_cases up : 0<u
  · have ep := edge_pos up
    refine ⟨(edgeWeight u)⁻¹,(inv_pos.mpr ep).le,fun s sp => ?_⟩
    by_cases inside : u<s
    · apply (step_bounds s u).2.trans
      rw [← div_eq_inv_mul]
      exact (one_le_div ep).mpr (edge_mono up.le inside.le)
    · simp [step,inside,mul_nonneg (inv_pos.mpr ep).le (edge_pos sp).le]
  · refine ⟨0,le_rfl,?_⟩
    simp [step,up]

private lemma atom_control (u v : ℝ) : EdgeControl (fun p => step p.1 u*step p.2 v) := by
  obtain ⟨C,cp,b⟩ := atom_side u
  obtain ⟨D,dp,c⟩ := atom_side v
  refine ⟨(step_measurable measurable_fst measurable_const).mul (step_measurable measurable_snd measurable_const),
    C*D,mul_nonneg cp dp,?_⟩
  intro s t sp tp
  rw [abs_of_nonneg (mul_nonneg (step_bounds _ _).1 (step_bounds _ _).1)]
  exact (mul_le_mul (b s sp) (c t tp) (step_bounds _ _).1 (mul_nonneg cp (edge_pos sp).le)).trans_eq (by ring)

private lemma prime_control (N M : ℕ) : EdgeControl (primeKernel N M) :=
  sum_control _ (fun n _ => sum_control _ (fun j _ => mul_control (atom_control _ _) (coefficient N M n j)))

private lemma arc_control {y : ℝ} (yp : 0<y) (u v : ℝ→ℝ) (hu : Measurable u) (hv : Measurable v)
    (l r : ℝ→ℝ) (left : ∀ s x, 0<u x → u x<s → x∈Ioo (l s) (l s+s))
    (right : ∀ t x, 0<v x → v x<t → x∈Ioo (r t) (r t+t))
    (apart : ∀ x, 0<u x → 0<v x → y≤u x+v x) :
    EdgeControl (fun p => ∫ x, step p.1 (u x)*step p.2 (v x) ∂unitMeasure) := by
  have m : Measurable (fun z : (ℝ×ℝ)×ℝ => step z.1.1 (u z.2)*step z.1.2 (v z.2)) :=
    (step_measurable (measurable_fst.comp measurable_fst) (hu.comp measurable_snd)).mul
      (step_measurable (measurable_snd.comp measurable_fst) (hv.comp measurable_snd))
  refine ⟨m.stronglyMeasurable.integral_prod_right'.measurable,(edgeWeight (y/2))⁻¹,(inv_pos.mpr (edge_pos (half_pos yp))).le,?_⟩
  intro s t sp tp
  simpa only [mul_assoc] using arc_edges sp tp yp u v hu hv (l s) (r t) (left s) (right t) apart

private lemma line_control {y : ℝ} (yp : 0<y) : EdgeControl (lineKernel y) := by
  let plus := fun u : ℝ => u+y
  let neg := fun u : ℝ => y-u
  have a (s x : ℝ) (p : 0<x) (t : x<s) : x∈Ioo (0:ℝ) (0+s) := ⟨p,by linarith⟩
  have b (s x : ℝ) (p : 0<plus x) (t : plus x<s) : x∈Ioo (-y) (-y+s) := by dsimp [plus] at *; constructor <;> linarith
  have c (s x : ℝ) (p : 0<neg x) (t : neg x<s) : x∈Ioo (y-s) (y-s+s) := by dsimp [neg] at *; constructor <;> linarith
  have plusM : Measurable plus := measurable_id.add measurable_const
  have negM : Measurable neg := measurable_const.sub measurable_id
  exact sub_control (add_control
    (arc_control yp id plus measurable_id plusM (fun _ => 0) (fun _ => -y) a b (by intro x xp _; dsimp [plus] at *; linarith))
    (arc_control yp plus id plusM measurable_id (fun _ => -y) (fun _ => 0) b a (by intro x _ xp; dsimp [plus] at *; linarith)))
    (arc_control yp id neg measurable_id negM (fun _ => 0) (fun t => y-t) a c (by intro x _ _; dsimp [neg]; linarith))

theorem signed_control (N k : ℕ) (kp : 0<k) : EdgeControl (signedKernel N k) := by
  apply sub_control (prime_control ..)
  apply sum_control
  intro j _
  exact mul_control (line_control (div_pos (by positivity) (by exact_mod_cast kp))) _

#print axioms signed_control
end GoldbachSpectral435.CumulativeKernel
