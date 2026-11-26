module
public import FrequencyMajorant

/-! Compact frequency bands in the exact inversion formula for a specified prime line. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open ConditionalGoldbach Filter Finset MeasureTheory
open scoped Topology
namespace GoldbachSpectral435.GoldbachSieve
open PhysicalTests

/-- Sequences of summation lengths, line coordinates and congruence moduli
along which the normalized variance estimate tends to zero. -/
structure LineSequence where
  base : ℕ→ℕ
  length : ℕ→ℕ
  shift : ℕ→ℕ
  lift : ℕ→ℕ
  growing : Tendsto base atTop atTop
  base_le : ∀ i, base i≤length i
  positive : ∀ i, 0<shift i
  even_shift : ∀ i, Even (shift i)
  horizon_bound : ∀ i, shift i≤2*scale (base i)*base i
  modulus_le : ∀ i, liftedModulus (localCutoff (base i)) (lift i)≤length i
  grh : ∀ i, GRH (liftedModulus (localCutoff (base i)) (lift i))
  small : Tendsto (fun i => let q := liftedModulus (localCutoff (base i)) (lift i)
    (q:ℝ)*(6+Real.log q)^2/length i) atTop (𝓝 0)

namespace LineSequence

def modulus (D : LineSequence) (i : ℕ) := liftedModulus (localCutoff (D.base i)) (D.lift i)
instance (D : LineSequence) (i : ℕ) : NeZero (D.modulus i) := by unfold modulus; infer_instance

def normalization (D : LineSequence) (i : ℕ) : ℝ :=
  D.modulus i/((D.length i:ℝ)^2*singularSeries (D.shift i))

def ordinate (D : LineSequence) (i : ℕ) : ℝ := D.shift i/(D.length i:ℝ)

def integrand (D : LineSequence) (sign : Bool) (f g : ℝ→ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  D.normalization i*frequencySlice (D.modulus i) (D.length i) (D.shift i) sign
    (siftedWeight (D.modulus i) (D.length i) f) (siftedWeight (D.modulus i) (D.length i) g) t

private lemma small_cap (D : LineSequence) (η : ℝ) (hp : 0<η) :
    ∀ᶠ i : ℕ in atTop, (D.modulus i:ℝ)*(6+Real.log (D.modulus i))^2≤η^2*D.length i := by
  filter_upwards [D.small.eventually_lt_const (sq_pos_of_pos hp)] with i h
  have mp : 0<(D.length i:ℝ) := Nat.cast_pos.mpr ((NeZero.pos (D.modulus i)).trans_le (D.modulus_le i))
  exact (div_lt_iff₀ mp).mp h |>.le

private lemma normalization_eq (D : LineSequence) (i : ℕ) (x : ℝ) :
    (D.modulus i:ℝ)*x/((D.length i:ℝ)^2*singularSeries (D.shift i))=D.normalization i*x := by
  unfold normalization; ring

lemma projected_limit (D : LineSequence) (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (sign : Bool) : Tendsto (fun i => D.normalization i*
      classPairs (D.modulus i) (D.shift i) (D.length i) (D.length i) sign f g) atTop (𝓝 (unitIntegral f*unitIntegral g)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  obtain ⟨η,hp,all⟩ := sharp_near_line_limit f g hf hg (ε/2) (by positivity)
  filter_upwards [D.growing.eventually all,D.small_cap η hp] with i est cap
  have e := est (D.length i) (D.shift i) (D.lift i) (D.base_le i) (D.positive i) (D.even_shift i)
    (D.horizon_bound i) (D.modulus_le i) cap (D.grh i) sign
  change abs ((D.modulus i:ℝ)*_/((D.length i:ℝ)^2*singularSeries (D.shift i)) - _)≤ε/2 at e
  rw [D.normalization_eq] at e
  rw [Real.dist_eq]
  exact e.trans_lt (by linarith)

theorem frequency_limit (D : LineSequence) (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (sign : Bool) (t x : ℝ) (hx : Tendsto D.ordinate atTop (𝓝 x)) :
    Tendsto (fun i => D.integrand sign f g i t) atTop (𝓝 (frequencyProfile sign (t*x) t f g)) := by
  have diff : Tendsto (fun i => D.integrand sign f g i t-frequencyProfile sign (t*D.ordinate i) t f g)
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    obtain ⟨η,hp,all⟩ := prime_frequency_limit f g hf hg t (ε/2) (by positivity)
    filter_upwards [D.growing.eventually all,D.small_cap η hp] with i est cap
    have e := est (D.length i) (D.shift i) (D.lift i) (D.base_le i) (D.positive i) (D.even_shift i)
      (D.horizon_bound i) (D.modulus_le i) cap (D.grh i) sign
    change abs ((D.modulus i:ℝ)*_/((D.length i:ℝ)^2*singularSeries (D.shift i)) - _)≤ε/2 at e
    rw [D.normalization_eq] at e
    rw [Real.dist_eq,sub_zero]
    exact e.trans_lt (by linarith)
  have ct : Continuous (fun u : ℝ => frequencyProfile sign (t*u) t f g) := by
    unfold frequencyProfile phaseMix; fun_prop
  have conv := diff.add (ct.continuousAt.tendsto.comp hx)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using conv

/-- After the line ordinate has a limit, the entire contribution of every
fixed compact frequency interval has the expected archimedean limit. -/
theorem compact_band (D : LineSequence) (f g : ℝ→ℝ) (hf : FiniteModelWeight f) (hg : FiniteModelWeight g)
    (sign : Bool) (a b x : ℝ) (hx : Tendsto D.ordinate atTop (𝓝 x)) :
    Tendsto (fun i => ∫ t in a..b,D.integrand sign f g i t) atTop
      (𝓝 (∫ t in a..b,frequencyProfile sign (t*x) t f g)) := by
  obtain ⟨F,⟨hF⟩,upper⟩ := positive_envelope f hf
  obtain ⟨G,⟨hG⟩,upper'⟩ := positive_envelope g hg
  let C := unitIntegral F*unitIntegral G+1
  have cap := (D.projected_limit F G hF hG sign).eventually_lt_const (lt_add_one _)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · filter_upwards with i
    exact (continuous_const.mul (continuous_frequencySlice ..)).aestronglyMeasurable
  · filter_upwards [cap] with i ci
    apply Eventually.of_forall
    intro t _
    have np : 0≤D.normalization i := div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (sq_nonneg _) (singularSeries_pos _).le)
    rw [Real.norm_eq_abs,integrand,abs_mul,abs_of_nonneg np]
    exact (mul_le_mul_of_nonneg_left (prime_frequency_majorant _ _ _ sign f g F G upper upper' t) np).trans ci.le
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun t _ => D.frequency_limit f g hf hg sign t x hx)

#print axioms compact_band
end LineSequence
end GoldbachSpectral435.GoldbachSieve
