module
public import CumulativeKernel

/-! The rectangular primitive of the entire signed prime discrepancy. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach MeasureTheory Set Filter Finset
namespace GoldbachSpectral435.CumulativeKernel
open GoldbachSpectral435.PerronApproximation GoldbachSpectral435.FiniteDiscrepancy

def coefficient (N M n j : ℕ) : ℝ :=
  (mangoldt n*mangoldt j/M)*(offDiagonalSign N j n).re

def primeKernel (N M : ℕ) (p : ℝ×ℝ) : ℝ :=
  ∑ n ∈ range M, ∑ j ∈ range M, coefficient N M n j*(step p.1 (n/(M:ℝ))*step p.2 (j/(M:ℝ)))

def lineKernel (y : ℝ) (p : ℝ×ℝ) : ℝ :=
  (∫ u, step p.1 u*step p.2 (u+y) ∂unitMeasure)+
  (∫ u, step p.1 (u+y)*step p.2 u ∂unitMeasure)-
  (∫ u, step p.1 u*step p.2 (y-u) ∂unitMeasure)

def modelKernel (N k : ℕ) (p : ℝ×ℝ) : ℝ :=
  ∑ j ∈ range (2*k), singularSeries ((j+1)*N)*lineKernel ((j+1:ℕ)/(k:ℝ)) p

def signedKernel (N k : ℕ) (p : ℝ×ℝ) : ℝ :=
  primeKernel N (k*N) p-modelKernel N k p

private def Represents (f : ℝ→ℝ) (K : ℝ×ℝ→ℝ) (v : ℝ) : Prop :=
  Integrable (fun p => derivativePair f p*K p) thresholds ∧
    (∫ p, derivativePair f p*K p ∂thresholds)=v

private lemma scale {f K v} (h : Represents f K v) (a : ℝ) : Represents f (fun p => a*K p) (a*v) := by
  have eq (p : ℝ×ℝ) : derivativePair f p*(a*K p)=a*(derivativePair f p*K p) := by ring
  unfold Represents
  simp_rw [eq]
  exact ⟨h.1.const_mul a,(integral_const_mul _ _).trans (congrArg (a*·) h.2)⟩

private lemma add {f K J v w} (h : Represents f K v) (j : Represents f J w) :
    Represents f (fun p => K p+J p) (v+w) := by
  unfold Represents
  simp_rw [mul_add]
  exact ⟨h.1.add j.1,(integral_add h.1 j.1).trans (congrArg₂ (·+·) h.2 j.2)⟩

private lemma sub {f K J v w} (h : Represents f K v) (j : Represents f J w) :
    Represents f (fun p => K p-J p) (v-w) := by
  unfold Represents
  simp_rw [mul_sub]
  exact ⟨h.1.sub j.1,(integral_sub h.1 j.1).trans (congrArg₂ (·-·) h.2 j.2)⟩

private lemma sumRep {ι : Type*} (I : Finset ι) {f : ℝ→ℝ} {K : ι→ℝ×ℝ→ℝ} {v : ι→ℝ}
    (h : ∀ i∈I, Represents f (K i) (v i)) : Represents f (fun p => ∑ i∈I, K i p) (∑ i∈I, v i) := by
  classical
  unfold Represents
  simp_rw [mul_sum]
  exact ⟨integrable_finsetSum I (fun i hi => (h i hi).1),
    (integral_finsetSum I (fun i hi => (h i hi).1)).trans (sum_congr rfl (fun i hi => (h i hi).2))⟩

private lemma atom (f : ℝ→ℝ) (hf : FiniteModelWeight f) (u v : ℝ) :
    Represents f (fun p => step p.1 u*step p.2 v) (f u*f v) :=
  ⟨atom_integrable f hf u v,represent_pair f hf u v⟩

private lemma arc (f : ℝ→ℝ) (hf : FiniteModelWeight f) (u v : ℝ→ℝ) (hu : Measurable u) (hv : Measurable v) :
    Represents f (fun p => ∫ x, step p.1 (u x)*step p.2 (v x) ∂unitMeasure)
      (∫ x, f (u x)*f (v x) ∂unitMeasure) :=
  ⟨weighted_pair_integrable unitMeasure u v hu hv f hf,(integrate_pairs unitMeasure u v hu hv f hf).symm⟩

private lemma line (f : ℝ→ℝ) (hf : FiniteModelWeight f) (y : ℝ) :
    Represents f (lineKernel y) (signedConvolution f y) := by
  let plus := fun u : ℝ => u+y
  let minus := fun u : ℝ => y-u
  have a := arc f hf id plus measurable_id (measurable_id.add measurable_const)
  have b := arc f hf plus id (measurable_id.add measurable_const) measurable_id
  have c := arc f hf id minus measurable_id (measurable_const.sub measurable_id)
  have loc (g : ℝ→ℝ) : (∫ u in Ioi (0:ℝ), f u*g u)=∫ u, f u*g u ∂unitMeasure := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun u hu => hu.1)
    intro u h
    have dead : f u=0 := by
      by_contra nz
      exact h.2 ⟨h.1,(hf.mem_support_unit nz).2.le⟩
    simp [dead]
  have eq : signedConvolution f y =
      (∫ x, f x*f (plus x) ∂unitMeasure)+(∫ x, f (plus x)*f x ∂unitMeasure)-
      (∫ x, f x*f (minus x) ∂unitMeasure) := by
    unfold signedConvolution differenceConvolution sumConvolution
    rw [loc,loc]
    have flip : (∫ x, f (plus x)*f x ∂unitMeasure)=(∫ x, f x*f (plus x) ∂unitMeasure) :=
      integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
    rw [flip,two_mul]
  rw [eq]
  exact sub (add a b) c

private def raw (N M : ℕ) (f : ℝ→ℝ) : ℝ :=
  ∑ n ∈ range M, ∑ j ∈ range M, coefficient N M n j*(f (n/(M:ℝ))*f (j/(M:ℝ)))

private def mainTerm (N k : ℕ) (f : ℝ→ℝ) : ℝ :=
  ∑ j ∈ range (2*k), singularSeries ((j+1)*N)*signedConvolution f ((j+1:ℕ)/(k:ℝ))

private lemma primes (N M : ℕ) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    Represents f (primeKernel N M) (raw N M f) := by
  apply sumRep
  intro n _
  apply sumRep
  intro j _
  exact scale (atom f hf _ _) _

private lemma model (N k : ℕ) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    Represents f (modelKernel N k) (mainTerm N k f) := sumRep _ (fun _ _ => scale (line f hf _) _)

private lemma real_sign (N n j : ℕ) : ((offDiagonalSign N n j).re:ℂ)=offDiagonalSign N n j := by
  unfold offDiagonalSign residueSign
  split_ifs <;> norm_num

private lemma raw_cast (N M : ℕ) (f : ℝ→ℝ) : ((raw N M f:ℝ):ℂ)=arithmetic N M f := by
  unfold raw arithmetic
  push_cast
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro j _
  have eq : coefficient N M n j*(f (n/(M:ℝ))*f (j/(M:ℝ)))=
      sampleValue M n f*sampleValue M j f*(offDiagonalSign N j n).re := by
    unfold coefficient sampleValue
    rw [div_mul_div_comm,← sq,Real.sq_sqrt (Nat.cast_nonneg M)]
    ring
  simpa only [Complex.ofReal_mul,real_sign] using congrArg Complex.ofReal eq

/-- The exact quadratic discrepancy at every integral dilation is a
double integral of the cumulative signed prime-minus-model kernel. -/
theorem exact_kernel (N k : ℕ) [NeZero N] (kp : 0<k) (he : Even N) (big : Real.exp 10<(N:ℝ))
    (grh : GRH N) (ha : alpha N<beta) (f : ℝ→ℝ) (hf : FiniteModelWeight f) :
    let x := testVector N (k*N) (Nat.mul_pos kp (NeZero.pos N)) f hf
    paperInner (residualOperator ha N x) x =
      ((∫ p, derivativePair f p*signedKernel N k p ∂thresholds : ℝ):ℂ) := by
  intro x
  have rep := sub (primes N (k*N) f hf) (model N k f hf)
  have eq : (∫ p, derivativePair f p*signedKernel N k p ∂thresholds)=raw N (k*N) f-mainTerm N k f := rep.2
  rw [eq,Complex.ofReal_sub,raw_cast,(exact_form N k kp he big grh ha f hf).2]
  congr 1
  simp [mainTerm,continuousModel]

#print axioms exact_kernel
end GoldbachSpectral435.CumulativeKernel
