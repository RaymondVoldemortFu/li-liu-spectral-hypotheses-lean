module
public import PaperPremise
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Convex

@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Complex Set Filter
open scoped Topology ComplexConjugate InnerProductSpace
namespace GoldbachSpectral435

/-- The same interior sampling sequence works for every sufficiently large modulus. -/
def samplePoint (j : ℕ) : ℂ := line sigmaStar (1 / ((j : ℝ) + 1))

private def ev (N j : ℕ) : HardySpace (alpha N) beta := evaluationVector (samplePoint j)

private def synth (N : ℕ) := Finsupp.linearCombination ℂ (ev N)

/-- Sesquilinear form of a sampled kernel, linear in the first coefficient vector. -/
def sampleForm (K : ℂ → ℂ → ℂ) (c d : ℕ →₀ ℂ) : ℂ :=
  ∑ i ∈ d.support, ∑ j ∈ c.support, conj (d i) * (c j * K (samplePoint i) (samplePoint j))

def gramSize (N : ℕ) (c : ℕ →₀ ℂ) : ℝ :=
  Real.sqrt (sampleForm (reproducingKernel (alpha N) beta) c c).re

/-- A bound expressed entirely in the two explicit kernels and finite sums. -/
def SampleBound (N : ℕ) [NeZero N] (B : ℝ) : Prop :=
  ∀ c d : ℕ →₀ ℂ, ‖sampleForm (weightedKernel N) c d‖ ≤ B * gramSize N c * gramSize N d

private theorem samples_dense (N : ℕ) (big : Real.exp 10 < (N : ℝ)) :
    DenseRange (synth N) := by
  let K := Submodule.span ℂ (Set.range (ev N))
  have orth : Kᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have zeros (i : ℕ) : fourierLaplace v (samplePoint i) = 0 := by
      rw [evaluationVector_spec (s := samplePoint i) (fixed_contour_mem_strip big _)]
      exact hv _ (Submodule.subset_span (Set.mem_range_self i))
    let z := line sigmaStar 0
    have tend : Tendsto samplePoint atTop (𝓝[≠] z) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have lineCont : Continuous (line sigmaStar) := by unfold line; fun_prop
        exact (lineCont.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      · apply Eventually.of_forall
        intro i eqz
        have eqim := congrArg Complex.im eqz
        have him : (1 : ℝ) / ((i : ℝ) + 1) = 0 := by simpa only [samplePoint,z,line,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using eqim
        exact (ne_of_gt (by positivity : 0 < (1 : ℝ) / ((i : ℝ) + 1))) him
    have frequent : ∃ᶠ s in 𝓝[≠] z, fourierLaplace v s = 0 := by
      exact tend.frequently ((Eventually.of_forall zeros).frequently)
    have hopen : IsOpen (strip (alpha N) beta) := isOpen_Ioo.preimage Complex.continuous_re
    have connected : IsPreconnected (strip (alpha N) beta) :=
      ((convex_halfSpace_re_gt (alpha N)).inter (convex_halfSpace_re_lt beta)).isPreconnected
    have vanish := ((fourierLaplace_differentiableOn v).analyticOnNhd hopen).eqOn_zero_of_preconnected_of_frequently_eq_zero
      connected (fixed_contour_mem_strip big 0) frequent
    apply (Submodule.mem_bot ℂ).mpr
    apply fourierLaplace_injective_strip (large_parameters big).2.2
    intro s hs
    rw [evaluationVector_spec hs (0 : HardySpace (alpha N) beta)]
    simpa [paperInner] using vanish hs
  change Dense (Set.range (synth N))
  change Dense (↑(LinearMap.range (synth N)) : Set (HardySpace (alpha N) beta))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  simpa [synth,Finsupp.range_linearCombination,K] using orth

private theorem form_pair (N : ℕ) (T : HardySpace (alpha N) beta →L[ℂ] HardySpace (alpha N) beta)
    (K : ℂ → ℂ → ℂ)
    (entry : ∀ i j, K (samplePoint i) (samplePoint j) = paperInner (T (ev N j)) (ev N i))
    (c d : ℕ →₀ ℂ) : sampleForm K c d = paperInner (T (synth N c)) (synth N d) := by
  simp only [sampleForm,entry,synth,Finsupp.linearCombination_apply,Finsupp.sum,paperInner,
    map_sum,map_smul, sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem gramSize_eq (N : ℕ) (big : Real.exp 10 < (N : ℝ)) (c : ℕ →₀ ℂ) :
    gramSize N c = ‖synth N c‖ := by
  have ent (i j : ℕ) : reproducingKernel (alpha N) beta (samplePoint i) (samplePoint j) =
      paperInner (ContinuousLinearMap.id ℂ _ (ev N j)) (ev N i) := by
    rw [← evaluationVector_reproducingKernel (s := samplePoint i) (z := samplePoint j) (large_parameters big).2.2
      (fixed_contour_mem_strip big _) (fixed_contour_mem_strip big _)]
    exact evaluationVector_spec (fixed_contour_mem_strip big _) _
  rw [gramSize,form_pair N _ _ ent,paperInner,ContinuousLinearMap.id_apply]
  exact (congrArg Real.sqrt (inner_self_eq_norm_sq (𝕜 := ℂ) (synth N c))).trans (Real.sqrt_sq (norm_nonneg _))

theorem sampleBound_iff_norm (N : ℕ) [NeZero N] (even : Even N)
    (big : Real.exp 10 < (N : ℝ)) (g : GRH N) (B : ℝ) (pos : 0 ≤ B) :
    SampleBound N B ↔ ‖residualOperator (large_parameters big).2.2 N‖ ≤ B := by
  let T := residualOperator (large_parameters big).2.2 N
  have ent (i j : ℕ) := proposition_5_4_kernel_pairing N even big g (large_parameters big).2.2
    (samplePoint i) (samplePoint j) (fixed_contour_mem_strip big _) (fixed_contour_mem_strip big _)
  simp only [SampleBound,form_pair N T _ ent,gramSize_eq N big,paperInner]
  constructor
  · intro bound
    have dense := samples_dense N big
    have extend (x y : HardySpace (alpha N) beta) : ‖inner ℂ y (T x)‖ ≤ B * ‖x‖ * ‖y‖ := by
      refine dense.induction_on₂ (p := fun u v => ‖inner ℂ v (T u)‖ ≤ B * ‖u‖ * ‖v‖) ?_ bound x y
      apply isClosed_le <;> fun_prop
    apply T.opNorm_le_bound pos
    intro x
    have t := extend x (T x)
    rw [← inner_self_re_eq_norm,inner_self_eq_norm_sq,pow_two] at t
    by_cases h : 0 < ‖T x‖
    · exact le_of_mul_le_mul_right t h
    · exact (le_of_not_gt h).trans (mul_nonneg pos (norm_nonneg _))
  · intro bound c d
    exact (norm_inner_le_norm _ _).trans (by
      rw [mul_comm ‖synth N d‖]
      gcongr
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _)))

/-- Exact finite test for a prescribed width, including the boundary equality. -/
theorem prescribed_S_iff_samples (h : ℕ → ℝ) (adm : IsAdmissible h) :
    HypothesisS h ↔ EvenEventually (fun N => ∀ [NeZero N], GRH N →
      SampleBound N (spectralScale N /
        (2 * Real.sqrt (zeroFreeWidth N h * (1 - zeroFreeWidth N h))))) := by
  have convert_at (N : ℕ) [NeZero N] (he : Even N) (big : Real.exp 10 < (N : ℝ)) (g : GRH N)
      (cap : zeroFreeWidth N h ≤ 1 / 4) :
      SpectralZeroFree N (alpha N) (large_parameters big).2.2 (zeroFreeWidth N h) ↔
        SampleBound N (spectralScale N / (2 * Real.sqrt (zeroFreeWidth N h * (1-zeroFreeWidth N h)))) := by
    obtain ⟨four,lp,ha⟩ := large_parameters big
    have hp := adm.1 N he four
    have np : 0 < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
    have sp := singularSeries_pos N
    have wp : 0 < zeroFreeWidth N h := by unfold zeroFreeWidth; positivity
    have dp := spectralScale_pos N np sp lp
    rw [sampleBound_iff_norm N he big g _ (by positivity)]
    exact (theorem_6_1 N he big g ha).2.1 _ wp (by linarith)
  constructor
  · rintro ⟨_,free⟩
    obtain ⟨K,hK⟩ := (free.and evenEventually_large).and adm.2.2
    refine ⟨K,fun N hn he inst g => ?_⟩
    obtain ⟨⟨f,big⟩,cap⟩ := hK N hn he
    exact (convert_at N he big g cap).mp (f g inst _)
  · intro tests
    obtain ⟨K,hK⟩ := (tests.and evenEventually_large).and adm.2.2
    refine ⟨adm,K,fun N hn he g inst ha => ?_⟩
    obtain ⟨⟨t,big⟩,cap⟩ := hK N hn he
    exact (convert_at N he big g cap).mpr (@t inst g)

theorem log_S_iff_samples : HypothesisS (fun n => Real.log n) ↔
    EvenEventually (fun N => ∀ [NeZero N], GRH N →
      SampleBound N (spectralScale N / (2 * Real.sqrt
        (zeroFreeWidth N (fun n => Real.log n) * (1-zeroFreeWidth N (fun n => Real.log n)))))) :=
  prescribed_S_iff_samples _ isAdmissible_log

/-- A cofinal strict finite violation for one positive relative level is necessary
and sufficient to rule out all admissible choices. -/
theorem no_S_iff_finite_obstructions :
    (¬∃ h, HypothesisS h) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ K : ℕ, ∃ N ≥ K, Even N ∧ GRH N ∧
        ∃ inst : NeZero N, ∃ c d : ℕ →₀ ℂ,
        ε * singularSeries N * gramSize N c * gramSize N d <
            ‖sampleForm (@weightedKernel N inst) c d‖ := by
  rw [no_admissible_S_iff]
  constructor
  · rintro ⟨ε,ep,rows⟩
    obtain ⟨F,large⟩ := evenEventually_large
    refine ⟨ε,ep,fun K => ?_⟩
    obtain ⟨N,hn,he,g,inst,ha,violation⟩ := rows (max K F)
    refine ⟨N,by omega,he,g,inst,?_⟩
    have hs := (sampleBound_iff_norm N he (large N (by omega) he) g (ε*singularSeries N)
      (mul_nonneg ep.le (singularSeries_pos N).le)).mp
    have fail : ¬SampleBound N (ε*singularSeries N) := fun s => violation.not_ge (hs s)
    simpa [SampleBound,not_forall,not_le] using fail
  · rintro ⟨ε,ep,rows⟩
    obtain ⟨F,large⟩ := evenEventually_large
    refine ⟨ε,ep,fun K => ?_⟩
    obtain ⟨N,hn,he,g,inst,c,d,violation⟩ := rows (max K F)
    have big := large N (by omega) he
    refine ⟨N,by omega,he,g,inst,(large_parameters big).2.2,lt_of_not_ge fun bound => ?_⟩
    exact violation.not_ge ((sampleBound_iff_norm N he big g _ (mul_nonneg ep.le (singularSeries_pos N).le)).mpr bound c d)

#print axioms prescribed_S_iff_samples
#print axioms log_S_iff_samples
#print axioms no_S_iff_finite_obstructions
end GoldbachSpectral435
